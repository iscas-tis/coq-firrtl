From Coq Require Import ZArith FunInd OrderedType FMaps FMapAVL(* for Nat.eq_dec *).
From simplssrlib Require Import SsrOrder FMaps Var ZAriths Tactics Types FSets Store.
From nbits Require Import NBits.
From firrtl Require Import Env Firrtl HiEnv HiFirrtl TopoSort ModuleGraph_oriented (*InferWidth_rewritten*). (* for hfmodule and its parts *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq fintype ssrint ssrfun.
Require Import Coq.micromega.Lia.

(**********         Sem func for InferWidths            ************)

Fixpoint num_ref (ft : ftype) : nat :=
   match ft with
   | Gtyp _ => 1
   | Atyp atyp n => (num_ref atyp) * n + 1
   | Btyp ff => num_ff ff + 1
   end
with num_ff (ff : ffield) : nat :=
   match ff with
   | Fnil => 0
   | Fflips _ _ ft ff' => (num_ref ft) + num_ff ff'
end.

Fixpoint list_gtypref (v : ProdVarOrder.t) (ft : ftype) (ori : bool) : seq (ProdVarOrder.t * fgtyp * bool) :=
match ft with
   | Gtyp gt => [::(v, gt, ori)]
   | Atyp atyp n => list_gtypref (v.1, N.add v.2 1%num) atyp ori
   | Btyp ff => list_gtypref_ff v ff ori
   end
with list_gtypref_ff (v : ProdVarOrder.t) (ff : ffield) (ori : bool) : seq (ProdVarOrder.t * fgtyp * bool) :=
   match ff with
   | Fnil => [::]
   | Fflips _ fl ft ff' => match fl with
                        | Nflip => list_gtypref (v.1, N.add v.2 1%num) ft ori ++ list_gtypref_ff (v.1, N.add v.2 (N.of_nat (num_ref ft))) ff' ori
                        | Flipped => list_gtypref (v.1, N.add v.2 1%num) ft (~~ori) ++ list_gtypref_ff (v.1, N.add v.2 (N.of_nat (num_ref ft))) ff' ori
                        end
   end.
Definition testbty := (Btyp (Fflips (1%num) Nflip (Btyp (Fflips (1%num) Nflip (Gtyp (Fuint_implicit 0)) (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 0)) 2) Fnil))) (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 0)) 2) Fnil))).

Compute (list_gtypref (N0,N0) testbty false).

Definition make_vx_implicit (v : vertex_type) : vertex_type :=
    match v with
    | OutPort gt => OutPort (fgtyp_add_implicit gt)
    | InPort gt => InPort (fgtyp_add_implicit gt)
    | Register gt a b c => Register (fgtyp_add_implicit gt) a b c
    | Wire gt => Wire (fgtyp_add_implicit gt)
    | Node gt => Node (fgtyp_add_implicit gt)
    end.

Fixpoint make_gtyp_implicit (vm nvm : CEP.t vertex_type) (tl : seq (ProdVarOrder.t * fgtyp * bool)) : option (CEP.t vertex_type) := 
match tl with
    | nil => Some vm
    | (pv, gt, _) :: tl => match CEP.find pv vm with
                          | Some vx => let vm' := (if not_implicit gt then CEP.add pv vx nvm
                                        else CEP.add pv (make_vx_implicit vx) nvm) in make_gtyp_implicit vm vm' tl
                          | None => None
                          end
    end.

Definition make_p_implicit (vm nvm : CEP.t vertex_type) (p : HiFP.hfport) : option (CEP.t vertex_type) :=
   match p with
   | Finput v t => let tl := list_gtypref v t false in
                   make_gtyp_implicit vm nvm tl
   | Foutput v t => let tl := list_gtypref v t false in
                   make_gtyp_implicit vm nvm tl
   end.

Fixpoint  make_ps_implicit (vm nvm : CEP.t vertex_type) (ps : seq HiFP.hfport) : option (CEP.t vertex_type) :=
    match ps with
    | nil => Some nvm
    | hd :: tl => match make_p_implicit vm nvm hd with
                | Some vm' => make_ps_implicit vm vm' tl
                | None => None
                end
    end.

Fixpoint make_s_implicit (vm nvm : CEP.t vertex_type) (st : HiFP.hfstmt) : option (CEP.t vertex_type) :=
(* change the vertex of statement st in vm to implicit-width if st defines an implicit-width component *)
   match st with
  | Sskip => Some nvm
  | Swire v t => let tl := list_gtypref v t false in
                 make_gtyp_implicit vm nvm tl
  | Sreg v r => let tl := list_gtypref v (type r) false in
                make_gtyp_implicit vm nvm tl
  | Smem v m => (*TBD*) Some vm
  | Sinst v inst => (*TBD*) Some vm
  | Swhen _ s1 s2 => match make_ss_implicit vm nvm s1 with
                    | Some vm' => make_ss_implicit vm nvm s2
                    | None => None
                    end
  | _ => Some nvm 
  end
with make_ss_implicit (vm nvm : CEP.t vertex_type) (ss : HiFP.hfstmt_seq) : option (CEP.t vertex_type) :=
(* change the vertices of statements ss in vm to implicit-width if ss defines implicit-width components *)
   match ss with
  | Qnil => Some nvm
  | Qcons s st => match make_s_implicit vm nvm s with
                | Some vm' => make_ss_implicit vm vm' st
                | None => None
                end
  end.

Definition make_vm_implicit (F : HiFP.hfmodule) (vm : CEP.t vertex_type) : option (CEP.t vertex_type) :=
   (* in vm, change the type of vertex (explicit to implicit) according to its declaration in F. *)
   match F with
   | FInmod _ pp ss => match make_ps_implicit vm (CEP.empty vertex_type) pp with
                      | Some vm' => make_ss_implicit vm vm' ss
                      | None => None
                      end
   | FExmod _ _ _ => Some (CEP.empty vertex_type)
   end.

Fixpoint ft_find_sub (checkt : ftype) (num : N) (ori : bool) : option (ftype * bool) :=
  match checkt with
  | Gtyp gt => if num == N0 then Some (checkt, ori) else None
  | Atyp atyp n => if num == N0 then Some (checkt, ori)
                   else if (((N.to_nat num) - 1) >= (num_ref atyp) * n) then None
                   else if (((N.to_nat num) - 1) mod (num_ref atyp)) == 0 (* 对应标号是atyp，可能agg *)
                   then Some (atyp, ori)
                   else 
                    ft_find_sub atyp (N.of_nat (((N.to_nat num) - 1) mod (num_ref atyp))) ori
  | Btyp ff => if num == N0 then Some (checkt, ori)
               else ft_find_sub_f ff num ori
  end
with ft_find_sub_f (ff : ffield) (num : N) (ori : bool) : option (ftype * bool) :=
  match ff with
  | Fflips _ Nflip ft ff' => if num == 1%num (* 找到被更新的标号, 所对应的field *)
                              then Some (ft, ori)
                              else if (N.to_nat num) > (num_ref ft) (* 不在该field中, 找下一个field *)
                                  then ft_find_sub_f ff' (N.of_nat ((N.to_nat num) - (num_ref ft))) ori
                              else (* 在field v0中 *)
                                  ft_find_sub ft (N.sub num 1%num) ori
   | Fflips _ Flipped ft ff' => if num == 1%num (* 找到被更新的标号, 所对应的field *)
                              then Some (ft, (~~ori))
                              else if (N.to_nat num) > (num_ref ft) (* 不在该field中, 找下一个field *)
                                  then ft_find_sub_f ff' (N.of_nat ((N.to_nat num) - (num_ref ft))) ori
                              else (* 在field v0中 *)
                                  ft_find_sub ft (N.sub num 1%num) (~~ori)
   | _ => None
  end.
  
Definition type_of_ref (v : ProdVarOrder.t) (tmap : CEP.t (ftype * HiF.forient)) : option (ftype * bool) :=
  match CEP.find (fst v, N0) tmap with
  | Some (checkt, _) => ft_find_sub checkt (snd v) false
  | None => None
  end.

Definition mux_gtyp (t1 : fgtyp) (t2 : fgtyp) : option fgtyp :=
    match t1, t2 with
    | Fuint w1, Fuint w2 => Some (Fuint (maxn w1 w2))
    | Fuint w1, Fuint_implicit w2 
    | Fuint_implicit w1, Fuint w2
    | Fuint_implicit w1, Fuint_implicit w2 => Some (Fuint_implicit (maxn w1 w2))
    | Fsint w1, Fsint w2 => Some (Fsint (maxn w1 w2))
    | Fsint w1, Fsint_implicit w2 
    | Fsint_implicit w1, Fsint w2 
    | Fsint_implicit w1, Fsint_implicit w2 => Some (Fsint_implicit (maxn w1 w2))
    | Fclock, Fclock => Some (Fclock)
    | Freset, Freset => Some (Freset)
    | Fasyncreset, Fasyncreset => Some (Fasyncreset)
    | _,_ => None
    end.

Fixpoint mux_types (t1 : ftype) (t2 : ftype) : option ftype :=
    match t1, t2 with
    | Gtyp gt1, Gtyp gt2 => match mux_gtyp gt1 gt2 with
                            | Some gt => Some (Gtyp gt)
                            | _ => None
                            end
    | Atyp t1' n1, Atyp t2' n2 => match n1 == n2, mux_types t1' t2' with
                                  | true, Some t => Some (Atyp t n1)
                                  | _, _ => None
                                  end
    | Btyp bs1, Btyp bs2 =>
        match mux_btyps bs1 bs2 with
        | Some ff => Some (Btyp ff)
        | None => None
        end
    | _, _ => None
    end
with mux_btyps (bs1 : ffield) (bs2 : ffield) : option ffield :=
    match bs1, bs2 with
    | Fnil, Fnil => Some Fnil
    | Fflips v1 Nflip t1 fs1, Fflips v2 Nflip t2 fs2 =>
        if v1 == v2 then match mux_types t1 t2, mux_btyps fs1 fs2 with
                         | Some t, Some fs => Some (Fflips v1 Nflip t fs)
                         | _, _ => None
                         end
                    else None
    (* mux types must be passive, so Flipped is not allowed *)
    | _, _ => None
  end.

Fixpoint type_of_expr (expr : HiFP.hfexpr) (tmap: CEP.t (ftype * HiF.forient)) : option ftype :=
   (* Find the type of expression expr for reading.

   Similar to type_of_expr in InferWidths *)
  match expr with
  | Econst t bs => match t with
               | Fuint_implicit w => Some (Gtyp (Fuint (Nat.max (size bs) w)))
               | Fsint_implicit w => Some (Gtyp (Fsint (Nat.max (size bs) w)))
               | t => Some (Gtyp t)
               end
  | Eref (Eid r) => match type_of_ref r tmap with
                  | Some (t, _) => Some t
                  | _ => None
                  end
  | Eref _ => None
  | Ecast AsUInt e1 => match type_of_expr e1 tmap with
                      | Some (Gtyp (Fsint w)) | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint w))
                      | Some (Gtyp (Fsint_implicit w)) | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fuint_implicit w))
                      | Some (Gtyp Fclock) | Some (Gtyp Freset) | Some (Gtyp Fasyncreset) => Some (Gtyp (Fuint 1))
                      | _ => None
                      end
  | Ecast AsSInt e1 => match type_of_expr e1 tmap with
                      | Some (Gtyp (Fsint w)) | Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint w))
                      | Some (Gtyp (Fsint_implicit w)) | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fsint_implicit w))
                      | Some (Gtyp Fclock) | Some (Gtyp Freset) | Some (Gtyp Fasyncreset) => Some (Gtyp (Fsint 1))
                      | _ => None
                      end
  | Ecast AsClock e1 => match type_of_expr e1 tmap with
                        | Some (Gtyp _) => Some (Gtyp Fclock)
                        | _ => None
                        end
  | Ecast AsReset e1 => match type_of_expr e1 tmap with
                        | Some (Gtyp _) => Some (Gtyp Freset)
                        | _ => None
                        end
  | Eprim_unop (Upad n) e1 => match type_of_expr e1 tmap with
                              | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (maxn w n)))
                              | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (maxn w n)))
                              | Some (Gtyp (Fsint_implicit w)) => Some (Gtyp (Fsint_implicit (maxn w n)))
                              | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fuint_implicit (maxn w n)))
                              | _ => None
                              end
  | Eprim_unop (Ushl n) e1 => match type_of_expr e1 tmap with
                              | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (w + n)))
                              | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (w + n)))
                              | Some (Gtyp (Fsint_implicit w)) => Some (Gtyp (Fsint_implicit (w + n)))
                              | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fuint_implicit (w + n)))
                              | _ => None
                              end
  | Eprim_unop (Ushr n) e1 => match type_of_expr e1 tmap with
                              | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (maxn (w - n) 1)))
                              | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (maxn (w - n) 1)))
                              | Some (Gtyp (Fsint_implicit w)) => Some (Gtyp (Fsint_implicit (maxn (w - n) 1)))
                              | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fuint_implicit (maxn (w - n) 1)))
                              | _ => None
                              end
  | Eprim_unop Ucvt e1 => match type_of_expr e1 tmap with
                          | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint w))
                          | Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint (w + 1)))
                          | Some (Gtyp (Fsint_implicit w)) => Some (Gtyp (Fsint_implicit w))
                          | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fsint_implicit (w + 1)))
                          | _ => None
                          end
  | Eprim_unop Uneg e1 => match type_of_expr e1 tmap with
                          | Some (Gtyp (Fsint w)) | Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint (w + 1)))
                          | Some (Gtyp (Fsint_implicit w)) | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fsint_implicit (w + 1)))
                          | _ => None
                          end
  | Eprim_unop Unot e1 => match type_of_expr e1 tmap with
                          | Some (Gtyp (Fsint w)) | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint w))
                          | Some (Gtyp (Fsint_implicit w)) | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fuint_implicit w))
                          | _ => None
                          end
  | Eprim_unop (Uextr n1 n2) e1 => match type_of_expr e1 tmap with
                                  | Some (Gtyp (Fsint w)) | Some (Gtyp (Fuint w))
                                  | Some (Gtyp (Fsint_implicit w)) | Some (Gtyp (Fuint_implicit w)) =>
                                        if (n2 <= n1) && (n1 < w) then Some (Gtyp (Fuint (n1 - n2 + 1)))
                                                                  else None
                                  | _ => None
                                  end
  | Eprim_unop (Uhead n) e1 => match type_of_expr e1 tmap with
                              | Some (Gtyp (Fsint w)) | Some (Gtyp (Fuint w))
                              | Some (Gtyp (Fsint_implicit w)) | Some (Gtyp (Fuint_implicit w)) =>
                                  if n <= w then Some (Gtyp (Fuint n))
                                            else None
                              | _ => None
                              end
  | Eprim_unop (Utail n) e1 => match type_of_expr e1 tmap with
                              | Some (Gtyp (Fsint w)) | Some (Gtyp (Fuint w))
                              | Some (Gtyp (Fsint_implicit w)) | Some (Gtyp (Fuint_implicit w)) =>
                                  if n <= w then Some (Gtyp (Fuint (w - n)))
                                            else None
                              | _ => None
                              end
  | Eprim_unop _ e1 => match type_of_expr e1 tmap with
                      | Some (Gtyp (Fsint _)) | Some (Gtyp (Fuint _))
                      | Some (Gtyp (Fsint_implicit _)) | Some (Gtyp (Fuint_implicit _)) => Some (Gtyp (Fuint 1))
                      | _ => None
                      end
  | Eprim_binop (Bcomp _) e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                                  | Some (Gtyp (Fsint _)), Some (Gtyp (Fsint _))
                                  | Some (Gtyp (Fsint _)), Some (Gtyp (Fsint_implicit _))
                                  | Some (Gtyp (Fsint_implicit _)), Some (Gtyp (Fsint _))
                                  | Some (Gtyp (Fsint_implicit _)), Some (Gtyp (Fsint_implicit _))
                                  | Some (Gtyp (Fuint _)), Some (Gtyp (Fuint _))
                                  | Some (Gtyp (Fuint _)), Some (Gtyp (Fuint_implicit _))
                                  | Some (Gtyp (Fuint_implicit _)), Some (Gtyp (Fuint _))
                                  | Some (Gtyp (Fuint_implicit _)), Some (Gtyp (Fuint_implicit _)) =>
                                      Some (Gtyp (Fuint 1))
                                  | _, _ => None
                                  end
  | Eprim_binop Badd e1 e2
  | Eprim_binop Bsub e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (maxn w1 w2 + 1)))
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2)) =>
                                  Some (Gtyp (Fuint_implicit (maxn w1 w2 + 1)))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (maxn w1 w2 + 1)))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint_implicit w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) =>
                                  Some (Gtyp (Fsint_implicit (maxn w1 w2 + 1)))
                              | _, _ => None
                              end
  | Eprim_binop Bmul e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (w1 + w2)))
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2)) =>
                                  Some (Gtyp (Fuint_implicit (w1 + w2)))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (w1 + w2)))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint_implicit w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) =>
                                  Some (Gtyp (Fsint_implicit (w1 + w2)))
                              | _, _ => None
                              end
  | Eprim_binop Bdiv e1 e2  => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint _))
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit _)) => Some (Gtyp (Fuint w1))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint _))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit _)) => Some (Gtyp (Fuint_implicit w1))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint _))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint_implicit _)) => Some (Gtyp (Fsint (w1 + 1)))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint _))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit _)) => Some (Gtyp (Fsint_implicit (w1 + 1)))
                              | _, _ => None
                              end
  | Eprim_binop Brem e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (minn w1 w2)))
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2)) =>
                                  Some (Gtyp (Fuint_implicit (minn w1 w2)))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (minn w1 w2)))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint_implicit w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) =>
                                  Some (Gtyp (Fsint_implicit (minn w1 w2)))
                              | _, _ => None
                              end
  | Eprim_binop Bdshl e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (w1 + 2 ^ w2 - 1)))
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2)) => Some (Gtyp (Fuint_implicit (w1 + 2 ^ w2 - 1)))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fsint (w1 + 2 ^ w2 - 1)))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint_implicit w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) => Some (Gtyp (Fsint_implicit (w1 + 2 ^ w2 - 1)))
                              | _, _ => None
                              end
  | Eprim_binop Bdshr e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint _))
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit _)) => Some (Gtyp (Fuint w1))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint _))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit _)) => Some (Gtyp (Fuint_implicit w1))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fuint _))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fuint_implicit _)) => Some (Gtyp (Fsint w1))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fuint _))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fuint_implicit _)) => Some (Gtyp (Fsint_implicit w1))
                              | _, _ => None
                              end
  | Eprim_binop Bcat e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fuint (w1 + w2)))
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint_implicit w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) =>
                                  Some (Gtyp (Fuint_implicit (w1 + w2)))
                              | _, _ => None
                              end
  | Eprim_binop Band e1 e2
  | Eprim_binop Bor e1 e2
  | Eprim_binop Bxor e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2))
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint_implicit w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) => Some (Gtyp (Fuint (maxn w1 w2)))
                              | _, _ => None
                              end
  | Emux c e1 e2 => match type_of_expr c tmap, type_of_expr e1 tmap, type_of_expr e2 tmap with
                    | Some (Gtyp (Fuint 1)), Some t1, Some t2
                    | Some (Gtyp (Fuint_implicit 1)), Some t1, Some t2 =>
                        mux_types t1 t2
                    | _, _, _ => None
                    end
  | Evalidif c e1 => match type_of_expr c tmap with
                    | Some (Gtyp (Fuint 1)) | Some (Gtyp (Fuint_implicit 1)) => type_of_expr e1 tmap
                    | _ => None
                    end
  end.

Fixpoint code_type_find_vm_widths (code_t : ftype) (v : ProdVarOrder.T) (vm : CEP.t vertex_type) : option (ftype * N) :=
(* find the widths of types used in vm for a component that was declared with type code_t in the code.
   The module graph vertices (v, n), (v, n+1), (v, n+2), ... contain the relevant ground-type subcomponents.
   That means, the module graph vertices should contain ground-type elements as given by code_vm_type_equivalent.
   The result is a pair:
   - the type with widths adapted
   - the new index for n (where the next subcomponent would be found after handling code_t)
     (i.e. n + size_of_ftype code_t)
   If there is some error, the result is None instead.
   We allow non-passive types.
   Note that in most cases, the type of the output of the component is used,
   but for OutPorts we use the type of the input (because an out-port has no output connector). *)
match code_t with
| Gtyp oldgt =>
    match CEP.find v vm with
    | Some (OutPort newgt)
    | Some (InPort newgt)
    | Some (Register newgt _ _ _)
    | Some (Wire newgt)
    | Some (Node newgt) =>
        if fgtyp_equiv oldgt newgt
        then Some (Gtyp newgt, N.add (snd v) 1%num)
        else None
    | None => None
    end
| Atyp code_t' m =>
    (* check the first copy, and then verify that the next m-1 copies have exactly the same types *)
    match code_type_find_vm_widths code_t' (fst v, N.add (snd v) 1%num) vm with
    | Some (graph_t', new_n) =>
        (* Now check that there are another m-1 copies that are identical *)
        Some (Atyp graph_t' m, N.add (snd v) (N.of_nat (num_ref code_t)))
    | None => None
    end
| Btyp code_ff => code_ffield_find_vm_widths code_ff v vm
end
with code_ffield_find_vm_widths (code_ff : ffield) (v : ProdVarOrder.T) (vm : CEP.t vertex_type) : option (ftype * N) :=
match code_ff with
| Fnil => Some (Btyp Fnil, snd v)
| Fflips f flp code_t code_ff' =>
    match code_type_find_vm_widths code_t v vm with
    | Some (graph_t, n') =>
        match code_ffield_find_vm_widths code_ff' (fst v, n') vm with
        | Some (Btyp graph_ff, n'') =>
            Some (Btyp (Fflips f flp graph_t graph_ff), n'')
        | _ => None
        end
    | None => None
    end
end.

Fixpoint stmts_tmap (tmap_scope : CEP.t (ftype * HiF.forient) * CEP.t (ftype * HiF.forient)) (ss : HiFP.hfstmt_seq) (vm : CEP.t vertex_type) : option (CEP.t (ftype * HiF.forient) * CEP.t (ftype * HiF.forient)) :=
(* extends tmap_scope with the types of the defined components in ss.
   The first part of tmap_scope contains all defined components
   (used to check for name clashes, and will also be used later in Sem_frag_stmt);
   the second part contains only the components in the current scope
   (used to check whether a component defined within a Swhen statement
   is illegally used outside it).
   Produces None if some component is defined more than once,
   if a component is accessed before it is defined,
   or if it is accessed out of scope.

   Problem: does not check the directionality of the component
   (e.g. a node can only be read, an output port can only be written).
   Should we replace the tmap with a component environment? *)
match ss with
| Qnil => Some tmap_scope
| Qcons s ss' =>
    match stmt_tmap tmap_scope s vm with
    | Some tmap_scope' => stmts_tmap tmap_scope' ss' vm
    | None => None
    end
end
with stmt_tmap (tmap_scope : CEP.t (ftype * HiF.forient) * CEP.t (ftype * HiF.forient)) (s : HiFP.hfstmt) (vm : CEP.t vertex_type) : option (CEP.t (ftype * HiF.forient) * CEP.t (ftype * HiF.forient)) :=
(* extends tmap_scope with the type of the component defined in s.
   Produces None if s contains a definition of a component that is already in tmap. *)
match s with
| Sskip => Some tmap_scope
| Sfcnct (Eid ref) expr =>
    match type_of_ref ref (snd tmap_scope), type_of_expr expr (snd tmap_scope) with
    | Some _, Some _ => Some tmap_scope
    | _, _ => None (* something undefined or out-of-scope is accessed *)
    end
| Sinvalid (Eid ref) =>
    match type_of_ref ref (snd tmap_scope) with
    | Some _ => Some tmap_scope
    | None => None (* ref is undefined or out of scope *)
    end
| Swire v t =>
    match CEP.find v (fst tmap_scope), code_type_find_vm_widths t v vm with
    | None, Some (newt, _) =>
        Some (CEP.add v (newt, HiF.Duplex) (fst tmap_scope), CEP.add v (newt, HiF.Duplex) (snd tmap_scope))
    | _, _ => None (* identifier v is used multiple times, or the module graph does not fit *)
    end
| Sreg v reg =>
    match CEP.find v (fst tmap_scope), type_of_expr (clock reg) (snd tmap_scope), code_type_find_vm_widths (type reg) v vm with
    | None, Some _, Some (newt, _) =>
        match reset reg with
        | NRst => Some (CEP.add v (newt, HiF.Duplex) (fst tmap_scope), CEP.add v (newt, HiF.Duplex) (snd tmap_scope))
        | Rst rst_sig rst_val =>
            (* We already complete the type checking of rst_sig here;
               there will be no repeated type check in Sem_frag_stmt. *)
            match type_of_expr rst_sig (snd tmap_scope) with
            | Some (Gtyp Fasyncreset) =>
                (* rst_val needs to be constant. At least it cannot be the register itself.
                   Otherwise we do not check whether the value is actually constant. *)
                match type_of_expr rst_val (snd tmap_scope) with
                | Some _ => Some (CEP.add v (newt, HiF.Duplex) (fst tmap_scope), CEP.add v (newt, HiF.Duplex) (snd tmap_scope))
                | None => None (* something undefined or out-of-scope is accessed *)
                end
             | Some (Gtyp (Fuint 1)) =>
                (* rst_val can be variable. For example, it can be an expression containing the register itself *)
                match type_of_expr rst_val (CEP.add v (newt, HiF.Duplex) (snd tmap_scope)) with
                | Some _ => Some (CEP.add v (newt, HiF.Duplex) (fst tmap_scope), CEP.add v (newt, HiF.Duplex) (snd tmap_scope))
                | None => None (* something undefined or out-of-scope is accessed *)
                end
             | _ => None (* something undefined or out-of-scope is accessed *)
             end
        end
    | _, _, _ => None (* identifier v is used multiple times, or the clock is out of scope, or the module graph does not fit *)
    end
| Snode v expr =>
    match CEP.find v (fst tmap_scope), type_of_expr expr (snd tmap_scope) with
    | None, Some newt =>
        Some (CEP.add v (newt, HiF.Source) (fst tmap_scope), CEP.add v (newt, HiF.Source) (snd tmap_scope))
    | _, _ => None (* something undefined or out-of-scope is accessed, or identifier v is used multiple times *)
    end
| Smem _ _ => None
| Sinst _ _ => None
| Swhen cond ss_true ss_false =>
    match type_of_expr cond (snd tmap_scope), stmts_tmap tmap_scope ss_true vm with
    | Some _, Some (tmap_true, _) =>
        if stmts_tmap (tmap_true, snd tmap_scope) ss_false vm is Some (tmap_false, _)
        then Some (tmap_false, snd tmap_scope)
        else None (* there is an error in ss_false *)
    | _, _ => None (* cond accesses something undefined or out-of-scope, or there is an error in ss_true *)
    end
| _ => None
end.

Fixpoint ports_tmap (pp : seq HiFP.hfport) (vm : CEP.t vertex_type) : option (CEP.t (ftype * HiF.forient)) :=
(* creates a tmap that contains exactly the types of the ports in pp. *)
match pp with
| [::] => Some (CEP.empty (ftype * HiF.forient))
| Finput v t :: pp' =>
    match code_type_find_vm_widths t v vm, ports_tmap pp' vm with
    | Some (newt, _), Some tmap' =>
        match CEP.find v tmap' with
        | Some _ => None
        | None => Some (CEP.add v (newt, HiF.Source) tmap')
        end
    | _, _ => None
    end
| Foutput v t :: pp' =>
    match code_type_find_vm_widths t v vm, ports_tmap pp' vm with
    | Some (newt, _), Some tmap' =>
        match CEP.find v tmap' with
        | Some _ => None
        | None => Some (CEP.add v (newt, HiF.Sink) tmap')
        end
    | _, _ => None
    end
end.

Definition ports_stmts_tmap (pp : seq HiFP.hfport) (ss : HiFP.hfstmt_seq) (vm : CEP.t vertex_type) : option (CEP.t (ftype * HiF.forient)) :=
match ports_tmap pp vm with
| Some pmap =>
    match stmts_tmap (pmap, pmap) ss vm with
    | Some (tmap, _) => Some tmap
    | None => None
    end
| None => None
end.

Definition connect_fgtyp_compatible (t_tgt t_src : fgtyp) : bool :=
  fgtyp_equiv t_tgt t_src && (if (not_implicit t_tgt) then true
  else (sizeof_fgtyp t_tgt >= sizeof_fgtyp t_src)).

Fixpoint check_connect_non_passive_type (t_tgt t_src : seq (ProdVarOrder.T * fgtyp * bool)) : bool :=
  match t_tgt, t_src with
  | nil, nil => true
  | (_, thd, false) :: ttl, (_, shd, _) :: stl => connect_fgtyp_compatible thd shd && check_connect_non_passive_type ttl stl
  | (_, thd, true) :: ttl, (_, shd, _) :: stl => connect_fgtyp_compatible shd thd && check_connect_non_passive_type ttl stl
  | _, _ => false
  end.

Fixpoint check_connect_type (t_tgt t_src : seq (ProdVarOrder.T * fgtyp * bool)) : bool :=
  match t_tgt, t_src with
  | nil, nil => true
  | (_, thd, _) :: ttl, (_, shd, _) :: stl => connect_fgtyp_compatible thd shd && check_connect_type ttl stl
  | _, _ => false
  end.

Definition connect_non_passive_type (ref_tgt ref_src : ProdVarOrder.T) (t_tgt t_src : ftype) (ori_tgt ori_src : bool) : Prop :=
  ftype_equiv t_tgt t_src && check_connect_non_passive_type (list_gtypref ref_tgt t_tgt ori_tgt) (list_gtypref ref_src t_src ori_src). 

Definition connect_type (ref : ProdVarOrder.T) (t_tgt t_src : ftype) : Prop :=
  ftype_equiv t_tgt t_src && check_connect_type (list_gtypref ref t_tgt false) (list_gtypref (N0, N0) t_src false).

Fixpoint Sem_frag_stmt (vm_old : CEP.t vertex_type) (s : HiFP.hfstmt) (vm_new : CEP.t vertex_type) (tmap : CEP.t (ftype * HiF.forient)) : Prop :=
   (* The predicate returns True if vm_new/ct_new can be constructed from vm_old/ct_old by applying s.
   type checking, constraints *)
   match s with
   | Sskip => CEP.Equal vm_old vm_new 
   | Sfcnct (Eid ref_tgt) (Eref (Eid ref_src)) => (* allow non-passive types *)
          match type_of_ref ref_tgt tmap, type_of_ref ref_src tmap with
          | Some (ft_tgt, ori_tgt), Some (ft_src, ori_src) => connect_non_passive_type ref_tgt ref_src ft_tgt ft_src ori_tgt ori_src
          | _, _ => False
          end
   | Sfcnct (Eid ref_tgt) (Eref _) => False
   | Sfcnct (Eid ref) expr =>
          match type_of_ref ref tmap, type_of_expr expr tmap with
          | Some (ft_tgt, _), Some ft_src => connect_type ref ft_tgt ft_src
          | _, _ => False
          end
   | Sreg v reg =>
       match reset reg with
        | Rst _ rst_val => match CEP.find v tmap, type_of_expr rst_val tmap with
            | Some (newft, _), Some rst_val_type => connect_type v newft rst_val_type
            | _, _ => false
            end
        | NRst => True (* type check newft: we only need to verify newft is passive *)
        end
   | Smem v mem => False (* ? *)
   | Sinst var1 var2 => False (* ? *)
   | Swhen cond ss_true ss_false =>
       if type_of_expr cond tmap is Some (Gtyp (Fuint 1))
       then exists (vm_true : CEP.t vertex_type),
                   Sem_frag_stmts vm_old ss_true vm_true tmap
                /\
                   Sem_frag_stmts vm_true ss_false vm_new tmap
       else False
   | Sinvalid _
   | Swire _ _
   | Snode _ _ => True
   | _ => False
   end
with Sem_frag_stmts (vm_old : CEP.t vertex_type) (ss : HiFP.hfstmt_seq) (vm_new : CEP.t vertex_type) (tmap : CEP.t (ftype * HiF.forient)) : Prop :=
match ss with
| Qnil =>
       CEP.Equal vm_old vm_new
| Qcons s ss' =>
    exists (vm' : CEP.t vertex_type),
           Sem_frag_stmt vm_old s vm' tmap
        /\
           Sem_frag_stmts vm' ss' vm_new tmap
end.

Definition Sem (F : HiFP.hfmodule) (vm : CEP.t vertex_type) : Prop :=
(* The predicate returns True if G = (vm, ct) conforms to F.
   (If F has errors, there is no such G.)
   (If F has implicit width components, then there are many such Gs.)

   Problem: I made some assumption about identifiers of aggregate-type components;
   is that what you need? *)
match F with
| FInmod n pp ss =>
    match ports_stmts_tmap pp ss vm with
    | Some tmap =>
           (exists (vm' : CEP.t vertex_type) (ct' : CEP.t def_expr),
                  Sem_frag_ports (CEP.empty vertex_type)
                                 (CEP.empty def_expr)
                                 pp vm' ct' tmap
               /\
                  Sem_frag_stmts vm' ss vm tmap)
    | None => False
    end
| FExmod _ _ _ => False
 end.

(**********         Impletation for InferWidths            ************)

Fixpoint combine_mux_expr (c : HiFP.hfexpr) (el1 el2 : seq HiFP.hfexpr) : option (seq HiFP.hfexpr) :=
  match el1, el2 with
  | nil, nil => Some nil
  | hd1 :: tl1, hd2 :: tl2 => match combine_mux_expr c tl1 tl2 with
                            | Some muxl => Some ((Emux c hd1 hd2) :: muxl)
                            | None => None
                            end
  | _, _ => None
  end.

Fixpoint list_gtypexpr (expr_src : HiFP.hfexpr) (t : ftype) : option (seq HiFP.hfexpr) :=
  match expr_src with
  | Eref (Eid ref) => let refl := list_gtypref ref t false in 
                        Some (map (fun tref => (Eref (Eid (fst (fst tref))))) refl)
  | Eref _ => None
  | Emux c e1 e2 => match list_gtypexpr e1 t, list_gtypexpr e2 t with
                  | Some el1, Some el2 => combine_mux_expr c el1 el2
                  | _ ,_ => None
                  end
  | _ => Some [:: expr_src] 
  end.

Fixpoint add_expr_connect_non_passive (el1 el2 : seq (ProdVarOrder.t * fgtyp * bool)) (var2exprs : CEP.t (seq HiFP.hfexpr)) : option (CEP.t (seq HiFP.hfexpr)) :=
  match el1, el2 with
  | nil, nil => Some var2exprs
  | (ref1, _, false) :: ttl, (ref2, _, _) :: stl => match CEP.find ref1 var2exprs with
                | Some ls => add_expr_connect_non_passive ttl stl (CEP.add ref1 ((Eref (Eid ref2)) :: ls) var2exprs)
                | None => add_expr_connect_non_passive ttl stl (CEP.add ref1 [::(Eref (Eid ref2))] var2exprs)
                end
  | (ref1, _, true) :: ttl, (ref2, _, _) :: stl => match CEP.find ref2 var2exprs with
                | Some ls => add_expr_connect_non_passive ttl stl (CEP.add ref2 ((Eref (Eid ref1)) :: ls) var2exprs)
                | None => add_expr_connect_non_passive ttl stl (CEP.add ref2 [::(Eref (Eid ref1))] var2exprs)
                end
  | _, _ => None
  end.

Fixpoint add_expr_connect (el1 : seq (ProdVarOrder.t * fgtyp * bool)) (el2 : seq HiFP.hfexpr) (var2exprs : CEP.t (seq HiFP.hfexpr)) : option (CEP.t (seq HiFP.hfexpr)) :=
  match el1, el2 with
  | nil, nil => Some var2exprs
  | (ref1, _, _) :: tl1, hd2 :: tl2 => 
                match CEP.find ref1 var2exprs with
                | Some ls => add_expr_connect tl1 tl2 (CEP.add ref1 (hd2 :: ls) var2exprs)
                | None => add_expr_connect tl1 tl2 (CEP.add ref1 [::hd2] var2exprs)
                end
  | _, _ => None
  end.

Fixpoint stmts_tmap' (tmap : CEP.t (ftype * HiF.forient)) (emap : CEP.t (seq HiFP.hfexpr)) (ss : HiFP.hfstmt_seq): option (CEP.t (ftype * HiF.forient) * CEP.t (seq HiFP.hfexpr)) :=
match ss with
| Qnil => Some (tmap, emap)
| Qcons s ss' => match stmt_tmap' tmap emap s with
    | Some (tmap', emap') => stmts_tmap' tmap' emap' ss'
    | None => None
    end
end
with stmt_tmap' (tmap : CEP.t (ftype * HiF.forient)) (emap : CEP.t (seq HiFP.hfexpr)) (s : HiFP.hfstmt) : option (CEP.t (ftype * HiF.forient) * CEP.t (seq HiFP.hfexpr)) :=
match s with
| Sskip => Some (tmap, emap)
| Sfcnct (Eid ref) (Eref (Eid ref_src)) => match type_of_ref ref tmap, type_of_ref ref_src tmap with
    | Some (ft_tgt, ori_tgt), Some (ft_src, ori_src) =>  match list_gtypref ref ft_tgt ori_tgt, list_gtypref ref_src ft_src ori_src with
        | lhsl, rhsl => match add_expr_connect_non_passive lhsl rhsl emap with
                                | Some emap' => Some (tmap, emap')
                                | None => None
                                end
        end
    | _, _ => None
    end
| Sfcnct (Eid ref) (Eref _) => None
| Sfcnct (Eid ref) expr => match type_of_ref ref tmap, type_of_expr expr tmap with
    | Some (ft_tgt, ori_tgt), Some ft_src =>  match list_gtypref ref ft_tgt ori_tgt, list_gtypexpr expr ft_src with
        | lhsl, Some rhsl => match add_expr_connect lhsl rhsl emap with
                                | Some emap' => Some (tmap, emap')
                                | None => None
                                end
        | _, _ => None
        end
    | _, _ => None
    end
| Sinvalid (Eid ref) => match type_of_ref ref tmap with
    | Some _ => Some (tmap, emap)
    | None => None
    end
| Swire v t => match CEP.find v tmap with
    | None => Some (CEP.add v (t, HiF.Duplex) tmap, emap)
    | _ => None
    end
| Sreg v reg => match CEP.find v tmap, type_of_expr (clock reg) tmap with
    | None, Some _ =>
        match reset reg with
        | NRst => Some (CEP.add v ((type reg), HiF.Duplex) tmap, emap)
        | Rst rst_sig rst_val => match type_of_expr rst_sig tmap, type_of_expr rst_val tmap with
            | Some _, Some ft_src => match list_gtypref v (type reg) false, list_gtypexpr rst_val ft_src with
                | lhsl, Some rhsl => match add_expr_connect lhsl rhsl emap with
                                | Some emap' => Some (tmap, emap')
                                | None => None
                                end
                | _, _ => None
                end
            | _, _ => None
            end
        end
    | _, _ => None
    end
| Snode v expr => match CEP.find v tmap, type_of_expr expr tmap with
                | None, Some newt => match list_gtypref v newt false, list_gtypexpr expr newt with
                    | lhsl, Some rhsl => match add_expr_connect lhsl rhsl emap with
                                | Some emap' => Some (CEP.add v (newt, HiF.Source) tmap, emap')
                                | None => None
                                end
                    | _, _ => None
                    end
                | _, _ => None
                end
| Smem _ _ => None
| Sinst _ _ => None
| Swhen cond ss_true ss_false =>
    match type_of_expr cond tmap, stmts_tmap' tmap emap ss_true with
    | Some _, Some (tmap_true, emap_true) => stmts_tmap' tmap_true emap_true ss_false 
    | _, _ => None
    end
| _ => None
end.

Fixpoint ports_tmap' (pp : seq HiFP.hfport) : option (CEP.t (ftype * HiF.forient)) :=
(* creates a tmap that contains exactly the types of the ports in pp. *)
match pp with
| [::] => Some (CEP.empty (ftype * HiF.forient))
| Finput v t :: pp' => match ports_tmap' pp' with
    | Some tmap' =>
        match CEP.find v tmap' with
        | Some _ => None
        | None => Some (CEP.add v (t, HiF.Source) tmap')
        end
    | _ => None
    end
| Foutput v t :: pp' => match ports_tmap' pp' with
    | Some tmap' =>
        match CEP.find v tmap' with
        | Some _ => None
        | None => Some (CEP.add v (t, HiF.Sink) tmap')
        end
    | _ => None
    end
end.

Definition ports_stmts_tmap' (pp : seq HiFP.hfport) (ss : HiFP.hfstmt_seq) : option (CEP.t (ftype * HiF.forient) * CEP.t (seq HiFP.hfexpr)) :=
match ports_tmap' pp with
| Some pmap => stmts_tmap' pmap (CEP.empty (seq HiFP.hfexpr)) ss
| None => None
end.

Fixpoint lsreg_stmt (st : HiFP.hfstmt) : option (seq ProdVarOrder.t) :=
  match st with
  | Sskip => Some nil 
  | Swire v t => Some nil
  | Sreg v r => Some (map (fun temp => (fst (fst temp))) (list_gtypref v (type r) false))
  | Smem v m => (*TBD*) Some nil
  | Sinst v inst => (*TBD*) Some nil
  | Snode v e => Some nil
  | Sfcnct v e => Some nil
  | Sinvalid _ => Some nil
  | Swhen _ s1 s2 => match lsreg_stmts s1 , lsreg_stmts s2 with
                    | Some ls, Some ls' => Some (ls ++ ls')
                    | _,_ => None
                    end
  end
with lsreg_stmts (sts : HiFP.hfstmt_seq) :=
  match sts with
  | Qnil => Some nil
  | Qcons s ss => match lsreg_stmt s, lsreg_stmts ss with
                  | Some ls, Some ls' => Some (ls ++ ls')
                  | _,_ => None
                  end
  end.

Fixpoint expr2varlist (expr : HiFP.hfexpr) : option (seq ProdVarOrder.t) :=
  match expr with
  | Econst _ _ => Some nil
  | Eref (Eid ref) => Some [:: ref] 
  | Eprim_unop _ e1 => expr2varlist e1 
  | Eprim_binop _ e1 e2 => match expr2varlist e1, expr2varlist e2 with
                          | Some ls', Some ls'' => Some (ls' ++ ls'')
                          | _,_ => None
                          end
  | Emux e1 e2 e3 => match expr2varlist e1, expr2varlist e2, expr2varlist e3 with
                    | Some ls', Some ls'', Some ls''' => Some (ls' ++ ls'' ++ ls''')
                    | _,_,_ => None
                    end
  | Ecast _ e => expr2varlist e
  | _ => None
   end.

Definition emptyg : (ProdVarOrder.t -> seq ProdVarOrder.t) := (fun _ => [::]).

Definition updg (key : ProdVarOrder.t) (v : seq ProdVarOrder.t) (map : ProdVarOrder.t -> seq ProdVarOrder.t) : ProdVarOrder.t -> seq ProdVarOrder.t :=
    fun (y : ProdVarOrder.t) => if y == key then v else map y.

Fixpoint drawel (v : ProdVarOrder.t) (el : seq HiFP.hfexpr) (newg : ProdVarOrder.t -> seq ProdVarOrder.t) (vertices : seq ProdVarOrder.t) : option ((ProdVarOrder.t -> seq ProdVarOrder.t) * (seq ProdVarOrder.t)) :=
   match el with
   | nil => Some (newg, vertices)
   | e :: etl => match expr2varlist e with
                 | Some ls => let g' := List.fold_left (fun tempg tempv => updg tempv (cons v (tempg tempv)) tempg) ls newg in
                              drawel v etl g' (vertices ++ ls)
                 | None => None
                 end
   end.

Fixpoint drawg depandencyls (tmap : CEP.t (ftype * HiF.forient)) (regls : seq ProdVarOrder.T) (newg regg : ProdVarOrder.t -> seq ProdVarOrder.t) 
(vertices reg_vertices : seq ProdVarOrder.t) : option ((ProdVarOrder.t -> seq ProdVarOrder.t) * (seq ProdVarOrder.t) * (ProdVarOrder.t -> seq ProdVarOrder.t) * (seq ProdVarOrder.t)) :=
   match depandencyls with
   | nil => Some (newg, vertices, regg, reg_vertices)
   | (v, el) :: vtl => match type_of_ref v tmap with
                    | Some (Gtyp gt, _) => if not_implicit gt then drawg vtl tmap regls newg regg vertices reg_vertices (* explicit width则hulve *)
                                            else if ((fst v, N0) \in regls) 
                                                then match drawel v el regg reg_vertices with (* draw implicit reg *)
                                                    | Some (regg', reg_vertices') => drawg vtl tmap regls newg regg' vertices reg_vertices'
                                                    | None => None
                                                    end
                                                else match drawel v el newg vertices with (* draw implicit reg *)
                                                    | Some (newg', vertices') => drawg vtl tmap regls newg' regg vertices' reg_vertices
                                                    | None => None
                                                    end
                    | _ => None
                    end
  end.

Fixpoint fil_ftlist (l : seq (option ftype)) : option (seq fgtyp) :=
  match l with
  | nil => Some [::]
  | (Some (Gtyp gt)) :: tl => match fil_ftlist tl with
                      | Some tl' => Some (gt :: tl')
                      | None => None
                      end
  | _ :: tl => None
  end.

Fixpoint ft_set_sub (checkt : ftype) (newt : fgtyp) (num : N) : option ftype :=
  match checkt with
  | Gtyp _ => if num == N0 then Some (Gtyp newt) else None
  | Atyp atyp n => if num == N0 then None (* 不用agg type更新 *)
                    else if (((N.to_nat num) - 1) >= (num_ref atyp) * n) then None
                    else (* 继续找atyp中的结构 *)
                      match ft_set_sub atyp newt (N.of_nat (((N.to_nat num) - 1) mod (num_ref atyp))) with
                      | Some natyp => Some (Atyp natyp n)
                      | None => None
                      end
  | Btyp ff => if num == N0 then None
                else match ft_set_sub_f ff newt num with
                | Some newf => Some (Btyp newf)
                | None => None
                end
  end
with ft_set_sub_f (ff : ffield) (newt : fgtyp) (num : N) : option ffield :=
  match ff with
  | Fflips v0 fl ft ff' => if (N.to_nat num) > (num_ref ft) (* 不在该field中, 找下一个field *)
                                then match ft_set_sub_f ff' newt (N.of_nat ((N.to_nat num) - (num_ref ft))) with
                                    | Some newf => Some (Fflips v0 fl ft newf)
                                    | None => None
                                    end
                                else (* 在field v0中 *)
                                   match ft_set_sub ft newt (N.sub num 1%num) with
                                   | Some newt' => Some (Fflips v0 fl newt' ff')
                                   | None => None
                                   end
  | _ => None
  end.

Definition max_fgtyp (ft1 : fgtyp) (ft2 : fgtyp) : option fgtyp :=
  match ft1, ft2 with
  | Fuint w1, Fuint_implicit w2 => Some (Fuint_implicit (max w1 w2))
  | Fsint w1, Fsint_implicit w2 => Some (Fsint_implicit (max w1 w2))
  | Fuint_implicit w1, Fuint_implicit w2 => Some (Fuint_implicit (max w1 w2))
  | Fsint_implicit w1, Fsint_implicit w2 => Some (Fsint_implicit (max w1 w2))
  | _,_ => None
  end.

Fixpoint max_ftlist (l : seq fgtyp) (init : fgtyp): option fgtyp :=
  match l with
  | nil => Some init
  | t :: tl => match max_ftlist tl init with
              | Some t' => max_fgtyp t t'
              | None => None
              end
  end.

Definition InferWidth_fun (v : ProdVarOrder.t) (el : seq HiFP.hfexpr) (tmap : CEP.t (ftype * HiF.forient)) : option (CEP.t (ftype * HiF.forient)) :=
(* updates the width of v in tmap so that it is at least the width of the expressions in list el. *)
  match fil_ftlist (map (fun e => type_of_expr e tmap) el) with
  | Some eftl => match CEP.find (fst v, N0) tmap with
                | Some (init, ori) => match ft_find_sub init (snd v) false with
                              | Some (Gtyp initt, _) => match max_ftlist eftl initt with
                                                        | Some nt => match ft_set_sub init nt (snd v) with
                                                                    | Some nt0 => Some (CEP.add (fst v, N0) (nt0, ori) tmap)
                                                                    | None => None
                                                                    end
                                                        | None => None
                                                        end
                              | _ => None
                              end
                | None => None
                end
  | None => None
  end.

Fixpoint InferWidths_fun (od : seq ProdVarOrder.t) (var2exprs : CEP.t (seq HiFP.hfexpr)) (tmap : CEP.t (ftype * HiF.forient)) : option (CEP.t (ftype * HiF.forient)) :=
  match od with
  | nil => Some tmap
  | vhd :: vtl => match CEP.find vhd var2exprs with 
                  | Some el => match InferWidth_fun vhd el tmap with
                          | Some tm => InferWidths_fun vtl var2exprs tm
                          | None => None
                          end
                  | None => None (* 所有od是implicit，一定有连接 *)
                  end
  end.

Definition InferWidths_stage1 (F : HiFP.hfmodule) : option (CEP.t (ftype * HiF.forient)) :=
(* infer widths of implicit-width components among the ports and statements in F.
   A full version would not work on one module alone but on all modules in a circuit together,
   but the principle remains the same. Therefore, let’s just run the algorithm on a single module for now. *)
match F with
| FExmod _ _ _ => None
| FInmod v ps ss =>
    match ports_stmts_tmap' ps ss, lsreg_stmts ss with
    | Some (tmap', var2exprs), Some lsreg => 
            match drawg (CEP.elements var2exprs) tmap' lsreg emptyg emptyg nil nil with
           | Some (theg, vertices, regg, regvs) => 
               match TopoSort.topo_sort vertices theg, TopoSort.topo_sort regvs regg with
               | TopoSort.Sorted inferorder, TopoSort.Sorted regorder => (*match*) InferWidths_fun inferorder var2exprs tmap'(* with
                                                                        | Some tmap0 => match InferWidths_fun regorder var2exprs tmap0 with
                                                                                        | Some newtm => InferWidths_fun inferorder var2exprs newtm
                                                                                        | _ => None
                                                                                        end
                                                                        | _ => None
                                                                        end*)
               | _, _ => None
               end
           | _ => None
           end
       | _,_ => None
       end
end.

Fixpoint expli_ftype (t : ftype) : ftype :=
  match t with
  | Gtyp (Fuint_implicit w) => Gtyp (Fuint w)
  | Gtyp (Fsint_implicit w) => Gtyp (Fsint w)
  | Gtyp _ => t
  | Atyp t_ref n_ref => Atyp (expli_ftype t_ref) n_ref
  | Btyp ff_ref => Btyp (expli_ftype_ff ff_ref)
  end
with expli_ftype_ff (ff_ref : ffield) : ffield :=
  match ff_ref with
  | Fflips v_ref Nflip t_ref ff_ref' => Fflips v_ref Nflip (expli_ftype t_ref) (expli_ftype_ff ff_ref') 
  | Fflips v_ref Flipped t_ref ff_ref' => Fflips v_ref Flipped (expli_ftype t_ref) (expli_ftype_ff ff_ref') 
  | Fnil => Fnil
  end.
  
Definition InferWidths_transp (p : HiFP.hfport) (tmap : CEP.t (ftype * HiF.forient)) : option HiFP.hfport :=
  (* changes the type in one port declaration, depending on the information in tmap, to an explicit-width type *)
  match p with
  | Finput v t => if (ftype_not_implicit t) then Some p
                  else (match CEP.find v tmap with
                  | Some (ft, _) => (* if t has implicit width, update the hfport with ft and change it to explicit width *)
                                Some (Finput v (expli_ftype ft))
                  | _ => None
                  end)
  | Foutput v t => if (ftype_not_implicit t) then Some p
                  else (match CEP.find v tmap with
                  | Some (ft, _) => (* if t has implicit width, update the hfport with ft and change it to explicit width *)
                                Some (Foutput v (expli_ftype ft))
                  | _ => None
                  end)
  end.

Fixpoint InferWidths_transps (ps : seq HiFP.hfport) (tmap : CEP.t (ftype * HiF.forient)) : option (seq HiFP.hfport) :=
  (* changes the types in a sequence of port declarations, depending on the information in tmap, to explicit-width types *)
  match ps with
  | nil => Some nil
  | p :: tl => match InferWidths_transp p tmap, InferWidths_transps tl tmap with
                  | Some n, Some nss => Some (n :: nss)
                  | _, _ => None
                  end
  end.

Fixpoint InferWidths_transs (s : HiFP.hfstmt) (tmap : CEP.t (ftype * HiF.forient)) : option HiFP.hfstmt :=
(* with infered tmap, transform the ports and declarations *)
  match s with
  | Sskip => Some s
  | Swire v t => match CEP.find v tmap with
                  | Some (ft, _) => (* if t has implicit width, update the hfstmt with ft and change it to explicit width *)
                                Some (Swire v (expli_ftype ft))
                  | _ => None
                  end
  | Sreg v r => match CEP.find v tmap with
                | Some (ft, _) => (* if t has implicit width, update the hfstmt with ft and change it to explicit width *)
                              Some (Sreg v (mk_freg (expli_ftype ft) (clock r) (reset r)))
                | _ => None
                end
  | Smem v m => (*TBD*) Some s
  | Sinst v inst => (*TBD*) Some s
  | Snode v e => Some s
  | Sfcnct v e => Some s
  | Sinvalid _ => Some s
  | Swhen c s1 s2 => match InferWidths_transss s1 tmap, InferWidths_transss s2 tmap with
                    | Some n1, Some n2 => Some (Swhen c n1 n2)
                    | _, _ => None
                    end
  end
with InferWidths_transss (sts : HiFP.hfstmt_seq) (tmap : CEP.t (ftype * HiF.forient)) : option HiFP.hfstmt_seq :=
  match sts with
  | Qnil => Some (Qnil ProdVarOrder.T)
  | Qcons s ss => match InferWidths_transs s tmap, InferWidths_transss ss tmap with
                  | Some n, Some nss => Some (Qcons n nss)
                  | _, _ => None
                  end
  end.

Definition InferWidths_stage2 (F : HiFP.hfmodule) (tmap : CEP.t (ftype * HiF.forient)) : option HiFP.hfmodule :=
match F with
  | FExmod _ _ _ => None
  | FInmod v ps ss => match InferWidths_transps ps tmap, InferWidths_transss ss tmap with
                      | Some nps, Some nss => Some (FInmod v nps nss)
                      | _, _ => None
                      end
  end.


Definition InferWidths_m F : option (HiFP.hfmodule * CEP.t (ftype * HiF.forient)) :=
  match InferWidths_stage1 F with
  | Some newtm => match InferWidths_stage2 F newtm with
                  | Some nm => Some (nm, newtm)
                  | _ => None
                  end
  | None => None
  end.

Lemma check_connect_type_correct : forall ft te, (forall n,
  match nth_error ft n, nth_error te n with
  | Some (_, gt, _), Some (_, gte, _) => connect_fgtyp_compatible gt gte
  | None, None => true
  | _, _ => false
  end) -> check_connect_type ft te.
Proof.
  elim. 
  elim.
  simpl; done.
  intros; specialize H0 with (n := 0). 
  assert (H1: (@List.length (ProdVarOrder.t * fgtyp * bool) [::] <= 0)%coq_nat) by apply Nat.le_0_l ;
  apply List.nth_error_None in H1; rewrite H1 in H0; simpl in H0; discriminate.
  intros [[pv0 gt0] ori0] tl H. 
  elim. 
  intro; specialize H0 with (n := 0); simpl in H0; discriminate. 
  - (* case *)
  intros [[pv1 gt1] ori1] tl' H0 IH; clear H0.
  specialize H with (te := tl').
  simpl. 
  apply rwP with (P := connect_fgtyp_compatible gt0 gt1 /\ check_connect_type tl tl').
  apply andP. split.
  specialize IH with (n := 0); simpl in IH; done.
  apply H.
  intro.
  specialize IH with (n := n+1).
  assert (nth_error ((pv0, gt0, ori0) :: tl) (n + 1) = nth_error tl n).
    specialize nth_error_app2 with (l := [:: (pv0, gt0, ori0)]) (l' := tl) (n := (n + 1)); intros.
    simpl in H0; rewrite H0.
    rewrite -Nats.subn_sub addn1 subn1 Nat.pred_succ //.
    apply Nats.leq_le.
    rewrite addn1; apply ltn0Sn.
  rewrite H0 in IH.
  assert (nth_error ((pv1, gt1, ori1) :: tl') (n + 1) = nth_error tl' n).
    specialize nth_error_app2 with (l := [:: (pv1, gt1, ori1)]) (l' := tl') (n := (n + 1)); intros.
    simpl in H1; rewrite H1.
    rewrite -Nats.subn_sub addn1 subn1 Nat.pred_succ //.
    apply Nats.leq_le.
    rewrite addn1; apply ltn0Sn.
  rewrite H1 in IH; done.
Qed.

Lemma check_connect_non_passive_type_correct : forall ft te, (forall n, 
  match nth_error ft n, nth_error te n with
  | Some (_, thd, false), Some (_, shd, _) => connect_fgtyp_compatible thd shd
  | Some (_, thd, true), Some (_, shd, _)=> connect_fgtyp_compatible shd thd
  | None, None => true
  |  _, _ => false
  end) -> check_connect_non_passive_type ft te.
Proof.
  elim.
  elim.
  simpl; done.
  intros; specialize H0 with (n := 0). 
  assert (H1: (@List.length (ProdVarOrder.t * fgtyp * bool) [::] <= 0)%coq_nat) by apply Nat.le_0_l ;
  apply List.nth_error_None in H1; rewrite H1 in H0; simpl in H0; discriminate.
  intros [[pv0 gt0] ori0] tl H. 
  elim. 
  intro. specialize H0 with (n := 0); simpl in H0; case Hori : ori0; rewrite Hori in H0; discriminate. 
  intros [[pv1 gt1] ori1] tl' H0 IH; clear H0.
  specialize H with (te := tl').
  simpl.
  case Hori : ori0; rewrite Hori in IH; clear Hori ori0.
  - (* flip *) 
    apply rwP with (P := connect_fgtyp_compatible gt1 gt0 /\ check_connect_non_passive_type tl tl').
    apply andP. split.
    specialize IH with (n := 0); simpl in IH; done.
    apply H.
    intro.
    specialize IH with (n := n+1).
    assert (nth_error ((pv0, gt0, true) :: tl) (n + 1) = nth_error tl n).
      specialize nth_error_app2 with (l := [:: (pv0, gt0, true)]) (l' := tl) (n := (n + 1)); intros.
      simpl in H0; rewrite H0.
      rewrite -Nats.subn_sub addn1 subn1 Nat.pred_succ //.
      apply Nats.leq_le.
      rewrite addn1; apply ltn0Sn.
    rewrite H0 in IH.
    assert (nth_error ((pv1, gt1, ori1) :: tl') (n + 1) = nth_error tl' n).
      specialize nth_error_app2 with (l := [:: (pv1, gt1, ori1)]) (l' := tl') (n := (n + 1)); intros.
      simpl in H1; rewrite H1.
      rewrite -Nats.subn_sub addn1 subn1 Nat.pred_succ //.
      apply Nats.leq_le.
      rewrite addn1; apply ltn0Sn.
    rewrite H1 in IH; done.

  - (* nflip *) 
    apply rwP with (P := connect_fgtyp_compatible gt0 gt1 /\ check_connect_non_passive_type tl tl').
    apply andP. split.
    specialize IH with (n := 0); simpl in IH; done.
    apply H.
    intro.
    specialize IH with (n := n+1).
    assert (nth_error ((pv0, gt0, false) :: tl) (n + 1) = nth_error tl n).
      specialize nth_error_app2 with (l := [:: (pv0, gt0, false)]) (l' := tl) (n := (n + 1)); intros.
      simpl in H0; rewrite H0.
      rewrite -Nats.subn_sub addn1 subn1 Nat.pred_succ //.
      apply Nats.leq_le.
      rewrite addn1; apply ltn0Sn.
    rewrite H0 in IH.
    assert (nth_error ((pv1, gt1, ori1) :: tl') (n + 1) = nth_error tl' n).
      specialize nth_error_app2 with (l := [:: (pv1, gt1, ori1)]) (l' := tl') (n := (n + 1)); intros.
      simpl in H1; rewrite H1.
      rewrite -Nats.subn_sub addn1 subn1 Nat.pred_succ //.
      apply Nats.leq_le.
      rewrite addn1; apply ltn0Sn.
    rewrite H1 in IH; done.
Qed.

Lemma num_ref_eq : forall checkt nt0, ftype_equiv checkt nt0 -> num_ref checkt = num_ref nt0
with num_ref_eq_f : forall checkf nf0, fbtyp_equiv checkf nf0 -> num_ff checkf = num_ff nf0.
Proof.
  clear num_ref_eq.
  elim.
  intros gt nt0 Heq.
  case Hnt0 : nt0 => [gt0||]; rewrite Hnt0 in Heq; try discriminate.
  simpl; done.

  intros f H n nt0 Heq.
  case Hnt0 : nt0 => [|atyp na|]; rewrite Hnt0 in Heq; try discriminate.
  intros; simpl in Heq; simpl.
  move /andP : Heq => [H0 Heq].
  move /eqP : H0 => H0; rewrite H0.
  apply H in Heq; rewrite Heq; done.

  intros f nt0 Heq. 
  case Hnt0 : nt0 => [||btyp]; rewrite Hnt0 in Heq; try discriminate.
  simpl; simpl in Heq.
  apply num_ref_eq_f in Heq; rewrite Heq; done.

  clear num_ref_eq_f.
  elim.
  intros.
  simpl in H.
  case Hnf0 : nf0; rewrite Hnf0 in H; try discriminate; try done.
  intros v fl ft ff H nf0 Heq.
  case Hnf0 :  nf0 => [|v' fl' ft' ff']; rewrite Hnf0 in Heq; simpl in Heq; case Hf : fl; rewrite Hf in Heq; try discriminate.
  case Hf' : fl'; rewrite Hf' in Heq; try discriminate.
  move /andP : Heq => [Heq0 Heq1].
  move /andP : Heq0 => [_ Heq2].
  apply num_ref_eq in Heq2.
  apply H in Heq1.
  simpl; rewrite Heq1 Heq2; done.
  case Hf' : fl'; rewrite Hf' in Heq; try discriminate.
  move /andP : Heq => [Heq0 Heq1].
  move /andP : Heq0 => [_ Heq2].
  apply num_ref_eq in Heq2.
  apply H in Heq1.
  simpl; rewrite Heq1 Heq2; done.
Qed.

Lemma list_gtypref_lengtheq : forall t1 t2 r1 r2 ori1 ori2, ftype_equiv t1 t2 -> length (list_gtypref r1 t1 ori1) = length (list_gtypref r2 t2 ori2)
with list_gtypref_lengtheq_f : forall t1 t2 r1 r2 ori1 ori2, fbtyp_equiv t1 t2 -> length (list_gtypref_ff r1 t1 ori1) = length (list_gtypref_ff r2 t2 ori2).
Proof.
  elim.
  - (* gt *)
    intros t1 ft2 n.
    intros.
    case Hft2 : ft2 => [t2||]; rewrite Hft2 in H; simpl in H; try discriminate.
    simpl; done.
  - (* array *)
    intros t1 H n1 ft2; intros.
    case Hft2 : ft2 => [|t2 n2|]; rewrite Hft2 in H0; simpl in H0; try discriminate.
    simpl.
    move /andP : H0 => [H0 H3]; move /eqP : H0 => H0.
    move : H3; apply H. 
  - (* btyp *)
    intros t1 ft2; intros.
    case Hft2 : ft2 => [||t2]; rewrite Hft2 in H; simpl in H; try discriminate.
    simpl; move : H; apply list_gtypref_lengtheq_f.
  
  clear list_gtypref_lengtheq_f.
  elim.
  - (* nil *)
    intros.
    case Ht2 : t2; rewrite Ht2 in H; try discriminate.
    simpl; done.
  - (* ffield *)
    intros v1 fl1 ft1 f1 H; intros.
    case Ht2 : t2 => [|v2 fl2 ft2 f2]; rewrite Ht2 in H0; simpl in H0; case Hfl : fl1; rewrite Hfl in H0; try discriminate;
    case Hfl' : fl2; rewrite Hfl' in H0; try discriminate.
    simpl;
    move /andP : H0 => [H0 H1]; move /andP : H0 => [_ H0];
    apply list_gtypref_lengtheq with (r1 := (r1.1, (r1.2 + 1)%num)) (r2 := (r2.1, (r2.2 + 1)%num)) (ori1 := (~~ori1)) (ori2 := (~~ori2)) in H0;
    apply H with (r1 := (r1.1, (r1.2 + N.of_nat (num_ref ft1))%num)) (r2 := (r2.1, (r2.2 + N.of_nat (num_ref ft2))%num)) (ori1 := ori1) (ori2 := ori2) in H1;
    rewrite app_length; rewrite H0 H1 //; rewrite app_length //.
    simpl;
    move /andP : H0 => [H0 H1]; move /andP : H0 => [_ H0];
    apply list_gtypref_lengtheq with (r1 := (r1.1, (r1.2 + 1)%num)) (r2 := (r2.1, (r2.2 + 1)%num)) (ori1 := ori1) (ori2 := ori2) in H0;
    apply H with (r1 := (r1.1, (r1.2 + N.of_nat (num_ref ft1))%num)) (r2 := (r2.1, (r2.2 + N.of_nat (num_ref ft2))%num)) (ori1 := ori1) (ori2 := ori2) in H1;
    rewrite app_length; rewrite H0 H1 //; rewrite app_length //.
Qed.

Lemma listgtyp_eq : forall t_tgt t_expr n ref0 ref1 ori0 ori1 ori2 ori3 pv0 pv1 gt gte, ftype_equiv t_tgt t_expr -> nth_error (list_gtypref ref0 t_tgt ori0) n =
  Some (pv0, gt, ori2) -> nth_error (list_gtypref ref1 t_expr ori1) n = Some (pv1, gte, ori3) -> fgtyp_equiv gt gte
with listgtyp_eq_f : forall t1 t2 ref0 ref1 ori0 ori1 n pv0 pv1 gt gte ori2 ori3, fbtyp_equiv t1 t2 -> nth_error (list_gtypref_ff ref0 t1 ori0) n =
  Some (pv0, gt, ori2) -> nth_error (list_gtypref_ff ref1 t2 ori1) n = Some (pv1, gte, ori3) -> fgtyp_equiv gt gte.
Proof.
  elim.
  - (* gt *)
    intros t1 ft2 n.
    intros.
    case Hft2 : ft2 => [t2||]; rewrite Hft2 in H; simpl in H; try discriminate.
    rewrite Hft2 in H1; simpl in H0; simpl in H1.
    destruct n; simpl in H0; simpl in H1.
    inversion H0; inversion H1; clear H0 H1; rewrite -H4 -H7 //.
    assert (H': (@List.length (ProdVarOrder.t * fgtyp * bool) [::] <= n)%coq_nat) by apply Nat.le_0_l .
    apply List.nth_error_None in H'; rewrite H' in H0; simpl in H0; discriminate.
  - (* atyp *)
    intros t1 H n1 ft2 n; intros.
    case Hft2 : ft2 => [|t2 n2|]; rewrite Hft2 in H0; simpl in H0; try discriminate.
    move /andP : H0 => [H0 H3]; move /eqP : H0 => H0; rewrite H0 in H1; clear H0 n1.
    simpl in H1; rewrite Hft2 in H2; simpl in H2.
    move : H3 H1 H2; apply H.
  - (* btyp *)
    intros t1 ft2; intros.
    case Hft2 : ft2 => [||t2]; rewrite Hft2 in H; simpl in H; try discriminate.
    rewrite Hft2 in H1; simpl in H1; simpl in H0.
    move : H H0 H1.
    apply listgtyp_eq_f.

  clear listgtyp_eq_f.
  elim.
  - (* nil *)
    intros.
    case Ht2 : t2; rewrite Ht2 in H; try discriminate.
    rewrite Ht2 in H1; clear Ht2 t2; simpl in H0; simpl in H1.
    assert (H': (@List.length (ProdVarOrder.t * fgtyp * bool) [::] <= n)%coq_nat) by apply Nat.le_0_l .
    apply List.nth_error_None in H'; rewrite H' in H0; simpl in H0; discriminate.
  - (* ffield *)
    intros v1 fl1 ft1 f1 H; intros.
    case Ht2 : t2 => [|v2 fl2 ft2 f2]; rewrite Ht2 in H0; simpl in H0; case Hfl : fl1; rewrite Hfl in H0; try discriminate;
    case Hfl' : fl2; rewrite Hfl' in H0; try discriminate;
    rewrite Hfl in H1; rewrite Ht2 Hfl' in H2; simpl in H1; simpl in H2; rewrite Hfl' in Ht2; clear Hfl' Hfl fl1 fl2.
    - (* flip *)
      case Hn : (n < length(list_gtypref (ref0.1, (ref0.2 + 1)%num) ft1 (~~ ori0))).
      - (* from ft *)
        assert (nth_error (list_gtypref (ref0.1, (ref0.2 + 1)%num) ft1 (~~ ori0) ++ list_gtypref_ff (ref0.1, (ref0.2 + N.of_nat (num_ref ft1))%num) f1 ori0) n
        = nth_error (list_gtypref (ref0.1, (ref0.2 + 1)%num) ft1 (~~ ori0)) n) by
          (apply nth_error_app1; apply Nats.ltn_lt; rewrite Hn //).
        rewrite H3 in H1; clear H3.
        move /andP : H0 => [H0 H3]; move /andP : H0 => [_ H0].
        generalize H0; apply list_gtypref_lengtheq with (r1 := (ref0.1, (ref0.2 + 1)%num)) (r2 := (ref1.1, (ref1.2 + 1)%num)) (ori1 := (~~ ori0)) (ori2 := (~~ ori1)) in H0; intros H0'.
        rewrite H0 in Hn; clear H0.
        assert (nth_error (list_gtypref (ref1.1, (ref1.2 + 1)%num) ft2 (~~ ori1) ++ list_gtypref_ff (ref1.1, (ref1.2 + N.of_nat (num_ref ft2))%num) f2 ori1) n
        = nth_error (list_gtypref (ref1.1, (ref1.2 + 1)%num) ft2 (~~ ori1)) n) by
          (apply nth_error_app1; apply Nats.ltn_lt; rewrite Hn //).
        rewrite H0 in H2; clear H0.
        move : H0' H1 H2; apply listgtyp_eq.
    - (* from field *)
        assert (nth_error (list_gtypref (ref0.1, (ref0.2 + 1)%num) ft1 (~~ ori0) ++ list_gtypref_ff (ref0.1, (ref0.2 + N.of_nat (num_ref ft1))%num) f1 ori0) n
          = nth_error (list_gtypref_ff (ref0.1, (ref0.2 + N.of_nat (num_ref ft1))%num) f1 ori0) (n - length (list_gtypref (ref0.1, (ref0.2 + 1)%num) ft1 (~~ ori0)))).
          specialize nth_error_app2 with (l := list_gtypref (ref0.1, (ref0.2 + 1)%num) ft1 (~~ ori0))
          (l' := list_gtypref_ff (ref0.1, (ref0.2 + N.of_nat (num_ref ft1))%num) f1 ori0) (n := n); intros.
          apply H3; apply Nats.leq_le.
          admit.
        rewrite H3 in H1; clear H3.
        move /andP : H0 => [H0 H3]; move /andP : H0 => [_ H0].
        assert (nth_error (list_gtypref (ref1.1, (ref1.2 + 1)%num) ft2 (~~ ori1) ++
        list_gtypref_ff (ref1.1, (ref1.2 + N.of_nat (num_ref ft2))%num) f2 ori1) n = nth_error (list_gtypref_ff (ref1.1, (ref1.2 + N.of_nat (num_ref ft2))%num) f2 ori1) (n - length (list_gtypref (ref0.1, (ref0.2 + 1)%num) ft1 (~~ ori0)))).
        specialize nth_error_app2 with (l := list_gtypref (ref1.1, (ref1.2 + 1)%num) ft2 (~~ ori1))
          (l' := list_gtypref_ff (ref1.1, (ref1.2 + N.of_nat (num_ref ft2))%num) f2 ori1) (n := n); intros.
        apply list_gtypref_lengtheq with (r1 := (ref0.1, (ref0.2 + 1)%num)) (r2 := (ref1.1, (ref1.2 + 1)%num)) (ori1 := (~~ ori0)) (ori2 := (~~ ori1)) in H0.
        rewrite H0.
        apply H4; apply Nats.leq_le; clear H4.
        rewrite -H0. 
        admit. (* Hn *)
        rewrite H4 in H2; clear H4.
        move : H3 H1 H2; apply H.
    - (* nflip *)

Admitted. (* TBD *)

Lemma infer_cons_order : forall order1 order2 var2exprs tmap tmap' newtm, InferWidths_fun (order1 ++ order2) var2exprs tmap = Some newtm -> InferWidths_fun order1 var2exprs tmap = Some tmap' ->
  InferWidths_fun order2 var2exprs tmap' = Some newtm.
Proof.
  elim. 
  - (* nil *)
    simpl; intros.
    inversion H0; rewrite -H2 //.
  - (* cons *)
    intros hd tl IH; intros.
    simpl in H; simpl in H0.
    case Hfind : (CEP.find hd var2exprs) => [el|]; rewrite Hfind in H H0; try discriminate.
    case Hinfer : (InferWidth_fun hd el tmap) => [tm|]; rewrite Hinfer in H H0; try discriminate.
    apply IH with (tmap := tm); try done.
Qed.

Lemma mux_types_eq : forall t1 t2 t, mux_types t1 t2 = Some t -> ftype_equiv t1 t2 /\ ftype_equiv t2 t
with mux_btyps_eq : forall t1 t2 t, mux_btyps t1 t2 = Some t -> fbtyp_equiv t1 t2 /\ fbtyp_equiv t2 t.
Proof.
  elim.
  intros.
  case Ht2 : t2 => [gt||]; rewrite Ht2 in H; simpl in H; try discriminate.
  case Hmux : (mux_gtyp f gt) => [gte|]; rewrite Hmux in H; try discriminate.
  inversion H. 
  case Hf : f => [w|w|w|w|||]; rewrite Hf in Hmux.
  case Hgt : gt => [w'|w'|w'|w'|||]; rewrite Hgt in Hmux; simpl in Hmux; try discriminate; inversion Hmux; simpl; done.
  case Hgt : gt => [w'|w'|w'|w'|||]; rewrite Hgt in Hmux; simpl in Hmux; try discriminate; inversion Hmux; simpl; done.
  case Hgt : gt => [w'|w'|w'|w'|||]; rewrite Hgt in Hmux; simpl in Hmux; try discriminate; inversion Hmux; simpl; done.
  case Hgt : gt => [w'|w'|w'|w'|||]; rewrite Hgt in Hmux; simpl in Hmux; try discriminate; inversion Hmux; simpl; done.
  case Hgt : gt => [w'|w'|w'|w'|||]; rewrite Hgt in Hmux; simpl in Hmux; try discriminate; inversion Hmux; simpl; done.
  case Hgt : gt => [w'|w'|w'|w'|||]; rewrite Hgt in Hmux; simpl in Hmux; try discriminate; inversion Hmux; simpl; done.
  case Hgt : gt => [w'|w'|w'|w'|||]; rewrite Hgt in Hmux; simpl in Hmux; try discriminate; inversion Hmux; simpl; done.
  
  intros.
  case Ht2 : t2 => [|atyp na|]; rewrite Ht2 in H0; simpl in H0; try discriminate.
  case Hn : (n == na); rewrite Hn in H0; try discriminate.
  case Hmux : (mux_types f atyp) => [gte|]; rewrite Hmux in H0; try discriminate; inversion H0; clear H0.
  move /eqP : Hn => Hn.
  simpl.
  rewrite Hn eq_refl.
  apply H in Hmux.
  move : Hmux => [Hmux Hmux'].
  rewrite Hmux Hmux'; done.

  clear mux_types_eq.
  intros.
  case Ht2 : t2 => [||btyp]; rewrite Ht2 in H; simpl in H; try discriminate.
  case Hmux : (mux_btyps f btyp) => [ff|]; rewrite Hmux in H; try discriminate; inversion H; clear H.
  simpl.
  apply mux_btyps_eq in Hmux; done.

  clear mux_btyps_eq.
  elim.
  intros.
  case Ht2 : t2; rewrite Ht2 in H; simpl in H; try discriminate.
  inversion H.
  simpl; done.
  intros.
  case Ht2 : t2 => [|v' f' f0' f1']; rewrite Ht2 in H0; simpl in H0; case Hf : f; rewrite Hf in H0; try discriminate.
  case Hf' : f'; rewrite Hf' in H0; try discriminate.
  case Hv : (v == v'); rewrite Hv in H0; try discriminate.
  case Hmux : (mux_types f0 f0') => [nt|]; rewrite Hmux in H0; try discriminate.
  case Hmux' : (mux_btyps f1 f1') => [nf|]; rewrite Hmux' in H0; try discriminate.
  inversion H0; clear H0.
  move /eqP : Hv => Hv.
  simpl.
  rewrite Hv eq_refl.
  apply mux_types_eq in Hmux.
  move : Hmux => [Hmux H0].
  rewrite Hmux H0.
  apply H in Hmux'.
  move : Hmux' => [Hmux' H3].
  rewrite Hmux' H3; done.
Qed.

Lemma mux_expr_type_equiv : forall c s1 s2 tmap te te1 te2, type_of_expr (Emux c s1 s2) tmap = Some te -> type_of_expr s1 tmap = Some te1 -> 
  type_of_expr s2 tmap = Some te2 -> ftype_equiv te te1 /\ ftype_equiv te te2.
Proof.
  intros.
  simpl in H.
  case Hc : (type_of_expr c tmap) => [f|]; rewrite Hc in H; try discriminate.
  case Hf : f => [gt||]; rewrite Hf in H; try discriminate.
  case Hgt : gt => [w|w|w|w|||]; rewrite Hgt in H; try discriminate.
  case Hw : w => [|n0]; rewrite Hw in H; try discriminate.
  case Hn0 : n0; rewrite Hn0 in H; try discriminate.
  rewrite H0 H1 in H.
  apply mux_types_eq in H.
  move : H => [H H2].
  apply ftype_equiv_dlvr with (t1 := te1) (t2 := te2) (t3 := te) in H; try done.
  split; try apply ftype_equiv_comm; try done.
  case Hw : w => [|n0]; rewrite Hw in H; try discriminate.
  case Hn0 : n0; rewrite Hn0 in H; try discriminate.
  rewrite H0 H1 in H.
  apply mux_types_eq in H.
  move : H => [H H2].
  apply ftype_equiv_dlvr with (t1 := te1) (t2 := te2) (t3 := te) in H; try done.
  split; try apply ftype_equiv_comm; try done.
Qed.

Lemma find_mux_types_n : forall t1 t2 t_expr tt1 tt2 n tte r1 ori1 r2 ori2 r3 ori3, mux_types t1 t2 = Some t_expr -> nth_error (list_gtypref r1 t1 ori1) n = Some tt1 -> 
  nth_error (list_gtypref r2 t2 ori2) n = Some tt2 -> nth_error (list_gtypref r3 t_expr ori3) n = Some tte -> mux_gtyp tt1.1.2 tt2.1.2 = Some tte.1.2
with find_mux_types_n_f : forall t1 t2 t_expr tt1 tt2 n tte r1 ori1 r2 ori2 r3 ori3, mux_btyps t1 t2 = Some t_expr -> nth_error (list_gtypref_ff r1 t1 ori1) n = Some tt1 -> 
  nth_error (list_gtypref_ff r2 t2 ori2) n = Some tt2 -> nth_error (list_gtypref_ff r3 t_expr ori3) n = Some tte -> mux_gtyp tt1.1.2 tt2.1.2 = Some tte.1.2.
Proof.
  clear find_mux_types_n.
  elim.
  intros.
  case Ht2 : t2 => [gt||]; rewrite Ht2 in H H1; simpl in H; try discriminate.
  - (* gt *)
    case Hmux : (mux_gtyp f gt) => [gte|]; rewrite Hmux in H; try discriminate.
    inversion H; clear H; simpl in H0; simpl in H1; simpl.
    induction n; simpl in H0; simpl in H1; rewrite -H4 in H2; simpl in H2.
    inversion H0; clear H0; inversion H1; clear H1; inversion H2; clear H2.
    simpl; done.
    assert (Hn: (@List.length (ProdVarOrder.t * fgtyp * bool) [::] <= n)%coq_nat) by apply Nat.le_0_l;
    apply List.nth_error_None in Hn; rewrite Hn in H2; discriminate.
  - (* array *)
    clear find_mux_types_n_f.
    intros.
    case Ht2 : t2 => [|atyp na|]; rewrite Ht2 in H0 H2; simpl in H0; try discriminate.
    case Hn : (n == na); rewrite Hn in H0; try discriminate.
    case Hmux : (mux_types f atyp) => [natyp|]; rewrite Hmux in H0; try discriminate.
    inversion H0; clear H0.
    simpl in H1; simpl in H2; simpl.
    rewrite -H5 in H3; simpl in H3; clear H5 t_expr.
    apply H with (tt1 := tt1) (tt2 := tt2) (n :=n0) (tte := tte) (r1 := (r1.1, (r1.2 + 1)%num)) (ori1 := ori1) (r2 := (r2.1, (r2.2 + 1)%num)) (ori2 := ori2) (r3 := (r3.1, (r3.2 + 1)%num)) (ori3 := ori3) in Hmux; try done.
  - (* bundle *)
    intros.
    case Ht2 : t2 => [||btyp]; rewrite Ht2 in H H1; simpl in H; try discriminate.
    case Hmux : (mux_btyps f btyp) => [ff|]; rewrite Hmux in H; try discriminate.
    inversion H; clear H; rewrite -H4 in H2. 
    simpl in H0; simpl in H1; simpl in H2.
    move : H0 H1 H2.
    apply find_mux_types_n_f; done.

  clear find_mux_types_n_f.
  elim.
  - (* nil *)
    intros.
    case Ht2 : t2; rewrite Ht2 in H; simpl in H; try discriminate.
    simpl in H0.
    apply nth_error_In in H0.
    apply List.in_nil in H0; done.
  - (* ffiled *)
  intros.
  case Ht2 : t2 => [|v' f' f0' f1']; rewrite Ht2 in H0 H2; simpl in H0; case Hf : f ;rewrite Hf in H0; try discriminate.
  case Hf' : f'; rewrite Hf' in H0; try discriminate.
  case Hv : (v == v'); rewrite Hv in H0; try discriminate.
  case Hmux : (mux_types f0 f0') => [nt|]; rewrite Hmux in H0; try discriminate.
  case Hmux' : (mux_btyps f1 f1') => [nf|]; rewrite Hmux' in H0; try discriminate.
  simpl in H1; simpl in H2.
  inversion H0; clear H0; rewrite -H5 in H3; clear H5 t_expr.
  rewrite Hf in H1; rewrite Hf' in H2; rewrite Hf' in Ht2; clear Hf' f' Hf f; simpl in H3.
  case Hn : (n < length (list_gtypref (r1.1, (r1.2 + 1)%num) f0 ori1)).
  - (* 从 ft 取 *)
    assert (nth_error (list_gtypref (r3.1, (r3.2 + 1)%num) nt ori3 ++ 
      list_gtypref_ff (r3.1, (r3.2 + N.of_nat (num_ref nt))%num) nf ori3) n = nth_error (list_gtypref (r3.1, (r3.2 + 1)%num) nt ori3) n).
      apply nth_error_app1. apply Nats.ltn_lt.
      apply mux_types_eq in Hmux; move : Hmux => [Hmux1 Hmux2].
      apply ftype_equiv_dlvr with (t1 := f0) in Hmux2; try done; clear Hmux1.
      apply list_gtypref_lengtheq with (r1 := (r1.1, (r1.2 + 1)%num)) (r2 := (r3.1, (r3.2 + 1)%num)) (ori1 := ori1) (ori2 := ori3) in Hmux2.
      rewrite -Hmux2 Hn //.
    rewrite H0 in H3; clear H0.
    assert (nth_error (list_gtypref (r2.1, (r2.2 + 1)%num) f0' ori2 ++ 
      list_gtypref_ff (r2.1, (r2.2 + N.of_nat (num_ref f0'))%num) f1' ori2) n = nth_error (list_gtypref (r2.1, (r2.2 + 1)%num) f0' ori2) n).
      apply nth_error_app1. apply Nats.ltn_lt.
      apply mux_types_eq in Hmux; move : Hmux => [Hmux1 _].
      apply list_gtypref_lengtheq with (r1 := (r1.1, (r1.2 + 1)%num)) (r2 := (r2.1, (r2.2 + 1)%num)) (ori1 := ori1) (ori2 := ori2) in Hmux1.
      rewrite -Hmux1 Hn //.
    rewrite H0 in H2; clear H0.
    assert (nth_error (list_gtypref (r1.1, (r1.2 + 1)%num) f0 ori1 ++ 
      list_gtypref_ff (r1.1, (r1.2 + N.of_nat (num_ref f0))%num) f1 ori1) n = nth_error (list_gtypref (r1.1, (r1.2 + 1)%num) f0 ori1) n).
      apply nth_error_app1. apply Nats.ltn_lt.
      rewrite Hn //.
    rewrite H0 in H1; clear H0.
    move : Hmux H1 H2 H3.
    apply find_mux_types_n.
  - (* 从 field 取 *)
    clear find_mux_types_n.
    assert (nth_error (list_gtypref (r3.1, (r3.2 + 1)%num) nt ori3 ++ 
      list_gtypref_ff (r3.1, (r3.2 + N.of_nat (num_ref nt))%num) nf ori3) n = nth_error (list_gtypref_ff (r3.1, (r3.2 + N.of_nat (num_ref nt))%num)
      nf ori3) (n - length (list_gtypref (r3.1, (r3.2 + 1)%num) nt ori3))).
      specialize nth_error_app2 with (l := list_gtypref (r3.1, (r3.2 + 1)%num) nt ori3)
        (l' := list_gtypref_ff (r3.1, (r3.2 + N.of_nat (num_ref nt))%num) nf ori3) (n := n); intros.
      apply H0; apply Nats.leq_le; clear H0.
      apply mux_types_eq in Hmux; move : Hmux => [Hmux1 Hmux2].
      apply ftype_equiv_dlvr with (t1 := f0) in Hmux2; try done; clear Hmux1.
      apply list_gtypref_lengtheq with (r1 := (r1.1, (r1.2 + 1)%num)) (r2 := (r3.1, (r3.2 + 1)%num)) (ori1 := ori1) (ori2 := ori3) in Hmux2.
      rewrite -Hmux2.
      admit. (* Hn *)
    rewrite H0 in H3; clear H0.
    generalize Hmux; apply mux_types_eq in Hmux; move : Hmux => [Hmux1 Hmux2]; intros Hmux.
    apply ftype_equiv_dlvr with (t1 := f0) in Hmux2; try done; clear Hmux1.
    apply list_gtypref_lengtheq with (r1 := (r1.1, (r1.2 + 1)%num)) (r2 := (r3.1, (r3.2 + 1)%num)) (ori1 := ori1) (ori2 := ori3) in Hmux2.
    rewrite -Hmux2 in H3.
    assert (nth_error (list_gtypref (r2.1, (r2.2 + 1)%num) f0' ori2 ++ 
      list_gtypref_ff (r2.1, (r2.2 + N.of_nat (num_ref f0'))%num) f1' ori2) n = nth_error (list_gtypref_ff (r2.1, (r2.2 + N.of_nat (num_ref f0'))%num)
      f1' ori2) (n - length (list_gtypref (r2.1, (r2.2 + 1)%num) f0' ori2))).
      specialize nth_error_app2 with (l := list_gtypref (r2.1, (r2.2 + 1)%num) f0' ori2)
        (l' := list_gtypref_ff (r2.1, (r2.2 + N.of_nat (num_ref f0'))%num) f1' ori2) (n := n); intros.
      apply H0; apply Nats.leq_le; clear H0.
      apply mux_types_eq in Hmux; move : Hmux => [Hmux1 _].
      apply list_gtypref_lengtheq with (r1 := (r1.1, (r1.2 + 1)%num)) (r2 := (r2.1, (r2.2 + 1)%num)) (ori1 := ori1) (ori2 := ori2) in Hmux1.
      rewrite -Hmux1.
      admit. (* Hn *)
    rewrite H0 in H2; clear H0.
    apply mux_types_eq in Hmux; move : Hmux => [Hmux1 _].
    apply list_gtypref_lengtheq with (r1 := (r1.1, (r1.2 + 1)%num)) (r2 := (r2.1, (r2.2 + 1)%num)) (ori1 := ori1) (ori2 := ori2) in Hmux1.
    rewrite -Hmux1 in H2.
    assert (nth_error (list_gtypref (r1.1, (r1.2 + 1)%num) f0 ori1 ++ 
      list_gtypref_ff (r1.1, (r1.2 + N.of_nat (num_ref f0))%num) f1 ori1) n = nth_error (list_gtypref_ff (r1.1, (r1.2 + N.of_nat (num_ref f0))%num)
      f1 ori1) (n - length (list_gtypref (r1.1, (r1.2 + 1)%num) f0 ori1))).
      specialize nth_error_app2 with (l := list_gtypref (r1.1, (r1.2 + 1)%num) f0 ori1)
        (l' := list_gtypref_ff (r1.1, (r1.2 + N.of_nat (num_ref f0))%num) f1 ori1) (n := n); intros.
      apply H0; apply Nats.leq_le; clear H0.
      admit. (* Hn *)
    rewrite H0 in H1; clear H0.
    move : Hmux' H1 H2 H3.
    apply H.
Admitted.

Lemma combine_mux_expr_n : forall el1 el2 rhs_expr_ls n e1 e2 c, combine_mux_expr c el1 el2 = Some rhs_expr_ls -> 
  nth_error el1 n = Some e1 -> nth_error el2 n = Some e2 -> nth_error rhs_expr_ls n = Some (Emux c e1 e2).
Proof.
  elim.
  intros.
  apply nth_error_In in H0.
  apply List.in_nil in H0; done.
  intros hd tl IH.
  elim.
  intros.
  apply nth_error_In in H1.
  apply List.in_nil in H1; done.
  intros hd0 tl0 H; clear H.
  intros.
  simpl in H. 
  case Hcombine : (combine_mux_expr c tl tl0) => [muxl|]; rewrite Hcombine in H; try discriminate.
  inversion H; clear H.
  case Hn : n => [|n']; rewrite Hn in H0 H1; simpl in H0; simpl in H1.
  inversion H0; inversion H1.
  simpl; done.
  assert (Emux c hd hd0 :: muxl = [::Emux c hd hd0] ++ muxl).
  simpl; done.
  rewrite H; clear H.
  apply IH with (n := n') (e1 := e1) (e2 := e2) in Hcombine; try done.
Qed.

Lemma list_gtypref_fsteq: forall ft1 ft2 r ori1 n pv gt1 ori ori', ftype_equiv ft2 ft1 -> nth_error (list_gtypref r ft1 ori) n = Some (pv, gt1, ori1) -> (exists gt2 ori2, nth_error (list_gtypref r ft2 ori') n = Some (pv, gt2, ori2))
with list_gtypref_fsteq_f: forall ft1 ft2 r ori1 n pv gt1 ori ori', fbtyp_equiv ft2 ft1 -> nth_error (list_gtypref_ff r ft1 ori) n = Some (pv, gt1, ori1) -> (exists gt2 ori2, nth_error (list_gtypref_ff r ft2 ori') n = Some (pv, gt2, ori2)).
Proof.
  elim.
  - (* gt *)
    intros ft1; intros t2; intros.
    case Ht2 : t2 => [ft2||]; rewrite Ht2 in H; simpl in H; try discriminate.
    simpl in H0; simpl.
    destruct n; simpl in H0.
    inversion H0; clear H0; simpl.
    exists ft2; exists ori'; done.
    assert (H1: (@List.length (ProdVarOrder.t * fgtyp * bool) [::] <= n)%coq_nat) by apply Nat.le_0_l ;
    apply List.nth_error_None in H1; rewrite H1 in H0;discriminate.
  - (* atyp *)
    intros atyp1 IH n1; intros.
    case Ht2 : ft2 => [|atyp2 n2|]; rewrite Ht2 in H; simpl in H; try discriminate.
    move /andP : H => [_ H].
    simpl in H0; simpl.
    apply IH with (ft2 := atyp2) (ori' := ori') in H0; try done.
  - (* btyp *)
    intros f1; intros.
    case Ht2 : ft2 => [||btyp1]; rewrite Ht2 in H; simpl in H; try discriminate.
    simpl; simpl in H0.
    move : H H0; apply list_gtypref_fsteq_f.

  elim.
  - (* nil *)
    intros.
    case Ht2 : ft2 => [|v f f1 f2]; rewrite Ht2 in H; simpl in H; try discriminate.
    simpl in H0.
    assert (H1: (@List.length (ProdVarOrder.t * fgtyp * bool) [::] <= n)%coq_nat) by apply Nat.le_0_l ;
    apply List.nth_error_None in H1; rewrite H1 in H0;discriminate.
    case Hf : f; rewrite Hf in H; discriminate.
  - (* field *)
    intros v1 fl1 t1 f1 IH; intros.
    case Ht2 : ft2 => [|v2 fl2 t2 f2]; rewrite Ht2 in H; simpl in H; try discriminate.
    case Hfl : fl1; case Hfl' : fl2; rewrite Hfl Hfl' in H; try discriminate.
    - (* flip *)
      move /andP : H => [H' H]; move /andP : H' => [_ H'].
      simpl.
      case Hn : (n < length (list_gtypref (r.1, (r.2 + 1)%num) t2 (~~ ori'))).
      - assert (nth_error (list_gtypref (r.1, (r.2 + 1)%num) t2 (~~ ori') ++ list_gtypref_ff (r.1, (r.2 + N.of_nat (num_ref t2))%num) f2 ori') n
          = nth_error (list_gtypref (r.1, (r.2 + 1)%num) t2 (~~ ori')) n).
          apply nth_error_app1. apply Nats.ltn_lt. done.
        simpl in H0; rewrite Hfl in H0.
        rewrite H1; clear H1.
        assert (nth_error (list_gtypref (r.1, (r.2 + 1)%num) t1 (~~ ori) ++ list_gtypref_ff (r.1, (r.2 + N.of_nat (num_ref t1))%num) f1 ori) n
          = nth_error (list_gtypref (r.1, (r.2 + 1)%num) t1 (~~ ori)) n).
          apply nth_error_app1. apply Nats.ltn_lt.
          apply list_gtypref_lengtheq with (r1 := (r.1, (r.2 + 1)%num)) (ori1 := (~~ ori')) (r2 := (r.1, (r.2 + 1)%num)) (ori2 := (~~ ori)) in H'; rewrite -H' //.
        rewrite H1 in H0; clear H1.
        move : H' H0; apply list_gtypref_fsteq.
      - assert (nth_error (list_gtypref (r.1, (r.2 + 1)%num) t2 (~~ ori') ++ list_gtypref_ff (r.1, (r.2 + N.of_nat (num_ref t2))%num) f2 ori') n
          = nth_error (list_gtypref_ff (r.1, (r.2 + N.of_nat (num_ref t2))%num) f2 ori') (n - length (list_gtypref (r.1, (r.2 + 1)%num) t2 (~~ ori')))).
          specialize nth_error_app2 with (l := (list_gtypref (r.1, (r.2 + 1)%num) t2 (~~ ori')))
            (l' := (list_gtypref_ff (r.1, (r.2 + N.of_nat (num_ref t2))%num) f2 ori')) (n := n); intros.
          apply H1; clear H1. apply Nats.leq_le.
          admit. (* Hn *)
        simpl in H0; rewrite Hfl in H0.
        rewrite H1; clear H1.
        assert (nth_error (list_gtypref (r.1, (r.2 + 1)%num) t1 (~~ ori) ++ list_gtypref_ff (r.1, (r.2 + N.of_nat (num_ref t1))%num) f1 ori) n
          = nth_error (list_gtypref_ff (r.1, (r.2 + N.of_nat (num_ref t1))%num) f1 ori) (n - length (list_gtypref (r.1, (r.2 + 1)%num) t1 (~~ ori)))).
          specialize nth_error_app2 with (l := (list_gtypref (r.1, (r.2 + 1)%num) t1 (~~ ori)))
            (l' := (list_gtypref_ff (r.1, (r.2 + N.of_nat (num_ref t1))%num) f1 ori)) (n := n); intros.
          apply H1; clear H1. apply Nats.leq_le.
          apply list_gtypref_lengtheq with (r1 := (r.1, (r.2 + 1)%num)) (ori1 := (~~ ori')) (r2 := (r.1, (r.2 + 1)%num)) (ori2 := (~~ ori)) in H'; rewrite -H'.
          admit. (* Hn *)
        rewrite H1 in H0; clear H1.
        assert (length (list_gtypref (r.1, (r.2 + 1)%num) t2 (~~ ori')) = length (list_gtypref (r.1, (r.2 + 1)%num) t1 (~~ ori))) by (apply list_gtypref_lengtheq; done).
        rewrite H1; clear H1.
        apply num_ref_eq in H'; rewrite H'; clear H'.
        move : H H0; apply IH.
    - (* nflip *)
      admit.
Admitted.

Lemma ftype_equiv_list_eq : forall (t1 t2 : ftype) ref ori, ftype_equiv t1 t2 -> 
  Some [seq Eref (Eid tref.1.1) | tref <- list_gtypref ref t1 ori] = Some [seq Eref (Eid tref.1.1) | tref <- list_gtypref ref t2 ori]
with ftype_equiv_list_eq_f : forall t1 t2 ref ori, fbtyp_equiv t1 t2 -> 
  Some [seq Eref (Eid tref.1.1) | tref <- list_gtypref_ff ref t1 ori] = Some [seq Eref (Eid tref.1.1) | tref <- list_gtypref_ff ref t2 ori].
Proof.
  elim.
  - (* gtyp *)
    clear ftype_equiv_list_eq ftype_equiv_list_eq_f.
    intros; case Ht2 : t2 => [gt2||]; rewrite Ht2 in H; try discriminate.
    simpl; done.
  - (* array *)
    clear ftype_equiv_list_eq ftype_equiv_list_eq_f.
    intros atyp IH; intros.
    intros; case Ht2 : t2 => [gt2|atyp2 n2|]; rewrite Ht2 in H; try discriminate.
    simpl; apply IH.
    simpl in H; move /andP : H => [_ H]; done.
  - (* btyp *)
    intros.
    intros; case Ht2 : t2 => [gt2|atyp2 n2|btyp2]; rewrite Ht2 in H; try discriminate.
    simpl; apply ftype_equiv_list_eq_f.
    simpl in H; done.
  clear ftype_equiv_list_eq_f.
  elim.
  - (* nil *)
    intros; case Ht2 : t2; rewrite Ht2 in H; try discriminate.
    simpl; done.
  - (* cons *)
    intros.
    case Ht2 : t2 => [|v' f' f0' f1']; rewrite Ht2 in H0; simpl in H0; case Hf : f; rewrite Hf in H0; try discriminate.
    case Hf' : f'; rewrite Hf' in H0; try discriminate.
    - (* flip *)
      simpl. 
      move /andP : H0 => [H0' H0]; move /andP : H0' => [_ H0'].
      apply H with (ref := (ref.1, (ref.2 + N.of_nat (num_ref f0))%num)) (ori := ori) in H0; clear H.
      inversion H0; clear H0.
      apply ftype_equiv_list_eq with (ref := (ref.1, (ref.2 + 1)%num)) (ori := (~~ ori)) in H0'; clear ftype_equiv_list_eq.
      inversion H0'; clear H0'.
      admit. (* map_app *)
    - (* nflip *)

Admitted. (* TBD *)

Lemma ftype_equiv_split_eq : forall s t1 t2, ftype_equiv t1 t2 -> list_gtypexpr s t1 = list_gtypexpr s t2.
Proof.
  elim; try done.
  - (* mux *)
    intros c Hc e1 H1 e2 H2; intros.
    simpl.
    generalize H; apply Hc in H; intros H'; clear Hc.
    generalize H'; apply H1 in H'; intros H''; clear H1.
    apply H2 in H''; clear H2.
    rewrite H' H'' //.
  - (* ref *)
    intros.
    simpl. 
    case Hr : h => [ref|||]; try done.
    apply ftype_equiv_list_eq; done.
Qed.

Lemma list_fsteq : forall ref_tgt tgt v_tgt ori, In v_tgt (list_gtypref ref_tgt tgt ori) -> ref_tgt.1 = v_tgt.1.1.1
with list_fsteq_f : forall ref_tgt tgt v_tgt ori, In v_tgt (list_gtypref_ff ref_tgt tgt ori) -> ref_tgt.1 = v_tgt.1.1.1.
Proof.
  intros.
  apply In_nth_error in H.
  destruct H as [n Hn].
  move : tgt ref_tgt v_tgt ori n Hn.
  elim.
  - (* gt *)
    intros.
    simpl in Hn.
    destruct n; simpl in Hn.
    inversion Hn; simpl; done. 
    assert (H: (@List.length (ProdVarOrder.t * fgtyp * bool) [::] <= n)%coq_nat) by apply Nat.le_0_l;
      apply List.nth_error_None in H; rewrite Hn in H; discriminate.
  - (* atyp *)
    intros.
    simpl in Hn. 
    apply H in Hn; simpl in Hn; done.
  - (* btyp *)
    intros.
    simpl in Hn.
    apply list_fsteq_f with (tgt := f) (ori := ori).
    move : Hn; apply nth_error_In.
  
  intros.
  apply In_nth_error in H.
  destruct H as [n Hn].
  move : tgt ref_tgt v_tgt ori n Hn.
  elim.
  - (* nil *)
    intros.
    simpl in Hn.
    assert (H: (@List.length (ProdVarOrder.t * fgtyp * bool) [::] <= n)%coq_nat) by apply Nat.le_0_l;
      apply List.nth_error_None in H; rewrite Hn in H; discriminate.
  - (* field *)
    intros v1 fl1 ft1 f1 IH; intros.
    simpl in Hn. 
    case Hf : fl1; rewrite Hf in Hn.
    - (* flip *)
      case H : (n < length (list_gtypref (ref_tgt.1, (ref_tgt.2 + 1)%num) ft1 (~~ ori))).
      - assert (nth_error (list_gtypref (ref_tgt.1, (ref_tgt.2 + 1)%num) ft1 (~~ ori) ++ list_gtypref_ff (ref_tgt.1, (ref_tgt.2 + N.of_nat (num_ref ft1))%num) f1 ori) n
          = nth_error (list_gtypref (ref_tgt.1, (ref_tgt.2 + 1)%num) ft1 (~~ ori)) n).
          apply nth_error_app1. apply Nats.ltn_lt. done.
        rewrite H0 in Hn; clear H0.
        apply nth_error_In in Hn; apply list_fsteq in Hn; simpl in Hn; done.
      - assert (nth_error (list_gtypref (ref_tgt.1, (ref_tgt.2 + 1)%num) ft1 (~~ ori) ++ list_gtypref_ff (ref_tgt.1, (ref_tgt.2 + N.of_nat (num_ref ft1))%num) f1 ori) n
          = nth_error (list_gtypref_ff (ref_tgt.1, (ref_tgt.2 + N.of_nat (num_ref ft1))%num) f1 ori) (n - length (list_gtypref (ref_tgt.1, (ref_tgt.2 + 1)%num) ft1 (~~ ori)))).
          specialize nth_error_app2 with (l := list_gtypref (ref_tgt.1, (ref_tgt.2 + 1)%num) ft1 (~~ ori)) (l' := list_gtypref_ff (ref_tgt.1, (ref_tgt.2 + N.of_nat (num_ref ft1))%num) f1 ori) (n := n); intros.
          apply H0; clear H0. apply Nats.leq_le.
          admit. (* H *)
        rewrite H0 in Hn; clear H0.
         apply IH in Hn; simpl in Hn; done.
    - (* nflip *)
Admitted.

Lemma list_gtypref_correct : forall t_tgt ref_tgt tmap ori n pv0 gt ori0, type_of_ref ref_tgt tmap = Some (t_tgt, ori) -> nth_error (list_gtypref ref_tgt t_tgt ori) n = Some (pv0, gt, ori0) -> type_of_ref pv0 tmap = Some (Gtyp gt, ori0)
with list_gtypref_correct' : forall f ref_tgt ori n pv0 gt ori0, nth_error (list_gtypref ref_tgt f ori) n = Some (pv0, gt, ori0) -> ft_find_sub f (N.sub pv0.2 ref_tgt.2) ori = Some (Gtyp gt, ori0)
with list_gtypref_correct_f : forall f ref_tgt ori n pv0 gt ori0, nth_error (list_gtypref_ff ref_tgt f ori) n = Some (pv0, gt, ori0) -> ft_find_sub_f f (N.sub pv0.2 ref_tgt.2) ori = Some (Gtyp gt, ori0).
Proof. 
  elim.
  - (* gtyp *)
    intros ft ref_tgt tmap ori n pv gt ori0 Ht Hn. 
    simpl in Hn.
    induction n; simpl in Hn.
    inversion Hn; clear Hn; rewrite H0 in Ht; rewrite Ht H1 H2 //.
    assert (H: (@List.length (ProdVarOrder.t * fgtyp * bool) [::] <= n)%coq_nat) by apply Nat.le_0_l;
    apply List.nth_error_None in H; rewrite Hn in H; discriminate.
  - (* atyp *)
    intros f Hf na ref_tgt tmap ori n pv0 gt ori0 Ht Hn.
    simpl in Hn.
    assert (type_of_ref (ref_tgt.1, (ref_tgt.2 + 1)%num) tmap = Some (f, ori)).
    (*rewrite /type_of_ref; rewrite /type_of_ref in Ht; simpl.
    case Hfind : (CEP.find (ref_tgt.1, 0%num) tmap) => [[checkt ori']|]; rewrite Hfind in Ht; try discriminate.
    case Hcheckt : checkt => [tgt|tatyp tn|tbtyp]; rewrite Hcheckt in Ht; simpl in Ht; simpl.
    - (* checkt = gtyp *)
      case H2 : (ref_tgt.2 == 0%num); rewrite H2 in Ht; discriminate.
    - (* checkt = atyp *)*) admit.
    move : H Hn; apply Hf.
  - (* btyp *)
    intros.
    generalize H0; apply nth_error_In in H0; apply list_fsteq in H0; simpl in H0; intro H0'.
    rewrite /type_of_ref; rewrite /type_of_ref in H; rewrite -H0.
    case Hfind : (CEP.find (ref_tgt.1, 0%num) tmap) => [[checkt ori']|]; rewrite Hfind in H; try discriminate.
    case Hcheckt : checkt => [gtyp|atyp na|btyp]; rewrite Hcheckt in H; simpl in H; simpl.
    - case Hn : (ref_tgt.2 == 0%num); rewrite Hn in H; discriminate.
    - admit.
      (*case Hn : (ref_tgt.2 == 0%num); rewrite Hn in H; try discriminate.*)
    - assert (Hneq : (pv0.2 == 0%num) = false) by admit.
      rewrite Hneq. 
      case Hn : (ref_tgt.2 == 0%num); rewrite Hn in H.
      - (* eq *)
        inversion H; clear H.
        rewrite -H2 in H0'; rewrite -H2; clear H2 f; rewrite -H3 in H0'; clear H3 ori.
        simpl in H0'.
        apply list_gtypref_correct_f in H0'; move /eqP : Hn => Hn; rewrite Hn N.sub_0_r in H0'; done.
      - (* neq *)
        apply list_gtypref_correct with (tmap := tmap) in H0'.
        rewrite /type_of_ref -H0 Hfind Hcheckt in H0'; simpl in H0'; rewrite Hneq in H0'; done.
        rewrite /type_of_ref Hfind Hcheckt; simpl; rewrite Hn; done.
  elim.
  - (* gt *)
    intros.
    simpl in H.
    induction n; simpl in H.
    inversion H; clear H; rewrite N.sub_diag; simpl; done.
    assert (H': (@List.length (ProdVarOrder.t * fgtyp * bool) [::] <= n)%coq_nat) by apply Nat.le_0_l;
    apply List.nth_error_None in H'; rewrite H' in H; discriminate.
  - (* atyp *)
    intros atyp IH na; intros.
    simpl in H; simpl.
    - assert (Hneq : ((ref_tgt.2 < pv0.2)%num /\ (pv0.2 < (N.add ref_tgt.2 (N.of_nat (num_ref atyp))))%num)) by admit.
      (*move : Hneq => [Hneq1 Hneq2].
      apply N.sub_gt in Hneq1.
      apply N.eqb_neq in Hneq1.*)
      case : ((pv0.2 - ref_tgt.2)%num == 0%num).
      admit.
      case : (num_ref atyp * na <= N.to_nat (pv0.2 - ref_tgt.2) - 1).
      admit.
      case : ((N.to_nat (pv0.2 - ref_tgt.2) - 1) mod num_ref atyp == 0).
      admit.
      rewrite Nat.mod_small.
      rewrite Nnat.Nat2N.inj_sub Nnat.N2Nat.id -N.sub_add_distr.
      move : H; apply IH. 
      move : Hneq => [Hneq1 Hneq2].
      admit.
  - (* btyp *)
    intros; simpl; simpl in H.
    - assert (((pv0.2 - ref_tgt.2)%num == 0%num) = false) by admit.
      rewrite H0; clear H0.
    move : H; apply list_gtypref_correct_f.
  
  elim.
  - (* nil *)
    intros; simpl in H.
    assert (H': (@List.length (ProdVarOrder.t * fgtyp * bool) [::] <= n)%coq_nat) by apply Nat.le_0_l;
    apply List.nth_error_None in H'. rewrite H in H'; discriminate.
  - (* field *)
    intros v1 fl1 ft1 f1 IH; intros.
    simpl; simpl in H.
    case Hfl : fl1; rewrite Hfl in H.
    - (* flip *)
      - assert (Hneq : ((pv0.2 - ref_tgt.2)%num == 1%num) = false) by admit.
        rewrite Hneq. 
        case H1 : (num_ref ft1 < N.to_nat (pv0.2 - ref_tgt.2)).
      - assert (nth_error (list_gtypref_ff (ref_tgt.1, (ref_tgt.2 + N.of_nat (num_ref ft1))%num) f1 ori) (n - (length (list_gtypref (ref_tgt.1, (ref_tgt.2 + 1)%num) ft1 (~~ ori)))) = 
          nth_error (list_gtypref (ref_tgt.1, (ref_tgt.2 + 1)%num) ft1 (~~ ori) ++ 
          list_gtypref_ff (ref_tgt.1, (ref_tgt.2 + N.of_nat (num_ref ft1))%num) f1 ori) n) by admit.
        rewrite -H0 in H; clear H0.
        rewrite Nnat.Nat2N.inj_sub Nnat.N2Nat.id -N.sub_add_distr. 
        move : H; apply IH.
      - clear IH list_gtypref_correct_f.
        assert (nth_error (list_gtypref (ref_tgt.1, (ref_tgt.2 + 1)%num) ft1 (~~ ori)) n = 
          nth_error (list_gtypref (ref_tgt.1, (ref_tgt.2 + 1)%num) ft1 (~~ ori) ++ 
          list_gtypref_ff (ref_tgt.1, (ref_tgt.2 + N.of_nat (num_ref ft1))%num) f1 ori) n) by admit.
        rewrite -H0 in H; clear H0.
        rewrite -N.sub_add_distr; move : H.
        apply list_gtypref_correct'.
    - (* nflip *)
      admit.
Admitted. (* TBD *)

Lemma split_expr_type_correct : forall expr newtm, match expr with
  | Eref (Eid ref_src) => forall ft ori, type_of_ref ref_src newtm = Some (ft, ori) -> 
    forall n, match nth_error (list_gtypref ref_src ft ori) n with
    | Some (ref0, gt, ori0) => type_of_ref ref0 newtm = Some (Gtyp gt, ori0)
    | _ => true
    end
  | Eref _ => true
  | _ => forall rhs_expr_ls t_expr, type_of_expr expr newtm = Some t_expr -> list_gtypexpr expr t_expr = Some rhs_expr_ls ->
    forall n, match nth_error (list_gtypref (0%num, 0%num) t_expr false) n, nth_error rhs_expr_ls n with
    | Some (_, gt, _), Some texpr => type_of_expr texpr newtm = Some (Gtyp gt)
    | _, _ => true
    end
  end.
Proof.
  elim.
  - (* const *)
    intros; simpl in H0;inversion H0; clear H0.
    assert (exists gt_expr, t_expr = Gtyp gt_expr) by
      (simpl in H; case Hf : f =>[w|w|w|w|||]; try (rewrite Hf in H; inversion H; rewrite -Hf; exists f; done); 
      try (rewrite Hf in H; inversion H; exists (Fuint (Nat.max (size b) w)); done); try (rewrite Hf in H; inversion H; exists (Fsint (Nat.max (size b) w)); done)).
    destruct H0 as [gt_expr H0]; rewrite H0; simpl.
    induction n as [|n]; simpl.
    simpl in H; rewrite H0 in H; done. 
    assert (H1: (@List.length (ProdVarOrder.t * fgtyp * bool) [::] <= n)%coq_nat) by apply Nat.le_0_l ;
    apply List.nth_error_None in H1; rewrite H1 //.

  (* 其他expr case *)
  admit.
  admit.
  admit.

  (* mux case *)
  intros c Hc s1 Hs1 s2 Hs2.
  intros tmap rhs_expr_ls t_expr Hte Hsplit.
  simpl in Hsplit.
  case Hsplit1 : (list_gtypexpr s1 t_expr) => [el1|]; rewrite Hsplit1 in Hsplit; try discriminate.
  case Hsplit2 : (list_gtypexpr s2 t_expr) => [el2|]; rewrite Hsplit2 in Hsplit; try discriminate.
  generalize Hte.
  simpl in Hte.
  move => Hte'. 
  case Hce : (type_of_expr c tmap) => [f|]; rewrite Hce in Hte; try discriminate.
  case Hcf : f => [cgt||]; rewrite Hcf in Hte; try discriminate.
  case Hcgt : cgt => [w|w|w||||]; rewrite Hcgt in Hcf Hte; try discriminate.
  - (* case1 : c 为 uint1 *)
    case Hw : w => [|n0]; rewrite Hw in Hte; try discriminate.
    case Hw' : n0; rewrite Hw' in Hte Hw; try discriminate.
    rewrite Hw in Hcf; clear Hw Hw' Hcgt w n0 cgt.
    case Hs1e : (type_of_expr s1 tmap) => [t1|]; rewrite Hs1e in Hte; try discriminate.
    case Hs2e : (type_of_expr s2 tmap) => [t2|]; rewrite Hs2e in Hte; try discriminate.
    intro n. 
    case Hrhsn : (nth_error rhs_expr_ls n) => [texpr|]; try done.
    generalize Hs1e.
    specialize Hs1 with (newtm := tmap); case He1 : s1 => [|||||| r1 ]; rewrite He1 in Hs1;
    specialize Hs2 with (newtm := tmap); case He2 : s2 => [|||||| r2 ]; rewrite He2 in Hs2.
    - (* s1,s2 一般expr *)
      1,2,3,4,5,6,8,9,10,11,12,13,15,16,17,18,19,20,22,23,24,25,26,27,29,30,31,32,33,34,36,37,38,39,40,41
       : rewrite -He1; rewrite -He1 in Hs1; rewrite -He2 in Hs2; clear He1 He2;
      apply Hs1 with (rhs_expr_ls := el1) (n:= n) in Hs1e; try done; clear Hs1.
      1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,57,59,61,63,65,67,69,71 : 
      move => Hs1e'.
      1-36 : apply Hs2 with (rhs_expr_ls := el2) (n:= n) in Hs2e; try done; clear Hs2;
      case Hs1n : (nth_error (list_gtypref (0%num, 0%num) t1 false) n) => [[[pv1 tt1] ori1]|]; rewrite Hs1n in Hs1e.
      - (* some *)
        1,5,9,13,17,21,25,29,33,37,41,45,49,53,57,61,65,69,73,77,81,85,89,93,97,101,105,109,113,117,121,125,129,133,137,141 : 
        case Hs2n : (nth_error (list_gtypref (0%num, 0%num) t2 false) n) => [[[pv2 tt2] ori2]|]; rewrite Hs2n in Hs2e.
        - (* some *)
          1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,57,59,61,63,65,67,69,71 : 
          case Hten : (nth_error (list_gtypref (0%num, 0%num) t_expr false) n) => [[[tpv gte] ori0]|]; try done.
          - (* some *)
            1-36 : apply find_mux_types_n with (n := n) (r1 := (N0,N0)) (r2 := (N0,N0)) (r3 := (N0,N0)) (ori1 := false) (ori2 := false) (ori3 := false) (tt1 := (pv1, tt1, ori1)) (tt2 := (pv2, tt2, ori2)) (tte := (tpv, gte, ori0)) in Hte; try done;
            simpl in Hte; clear Hc;
            assert (exists e1, nth_error el1 n = Some e1) by admit;
              (* t_expr 和 t1 满足ftype_equiv，由Hs1n 和 Hsplit1知el1的长度小于n *)
            destruct H as [e1 He1];
            assert (exists e2, nth_error el2 n = Some e2) by admit;
            destruct H as [e2 He2];
            rewrite He1 in Hs1e; rewrite He2 in Hs2e;
            apply combine_mux_expr_n with (n := n) (el1 := el1) (el2 := el2) (e1 := e1) (e2 := e2) in Hsplit; try done;
            rewrite Hsplit in Hrhsn; clear Hsplit;
            inversion Hrhsn; clear Hrhsn H0;
            simpl;
            rewrite Hce Hcf Hs1e Hs2e;
            simpl; rewrite Hte; done.
          - (* none *)
            1-36 : admit. (* not None *)
      - (* none *)
        1,4,7,10,13,16,19,22,25,28,31,34,37,40,43,46,49,52,55,58,61,64,67,70,73,76,79,82,85,88,91,94,97,100,103,106 : admit. (* not None *)
      1-72 : assert (ftype_equiv t_expr t2) by (apply mux_expr_type_equiv with (c := c) (s1 := s1) (s2 := s2) (te := t_expr) (te1 := t1) (te2 := t2) in Hte'; try done;
      move : Hte' => [_ Hte']; done);
      specialize ftype_equiv_split_eq with (s := s2) (t1 := t_expr) (t2 := t2); intro;
      rewrite H0 in Hsplit2; try done.
      1-36 : assert (ftype_equiv t_expr t1) by (apply mux_expr_type_equiv with (c := c) (s1 := s1) (s2 := s2) (te := t_expr) (te1 := t1) (te2 := t2) in Hte'; try done;
      move : Hte' => [Hte' _]; done);
      specialize ftype_equiv_split_eq with (s := s1) (t1 := t_expr) (t2 := t1); intro;
      rewrite H0 in Hsplit1; try done.

    - (* s1 一般expr s2 ref *)
      1-6 : rewrite -He1; rewrite -He1 in Hs1; clear He1;
      apply Hs1 with (rhs_expr_ls := el1) (n:= n) in Hs1e; try done; clear Hs1.
      1,3,5,7,9,11 : 
      move => Hs1e'.
      1-6 : generalize Hs2e; rewrite He2 in Hs2e; intro Hs2e'; simpl in Hs2e; case Hr2 : r2 => [ref2|||]; rewrite Hr2 in Hs2e Hs2; try discriminate;
      case Ht2 : (type_of_ref ref2 tmap) => [[ft2 ori]|]; rewrite Ht2 in Hs2e; try discriminate; inversion Hs2e; clear Hs2e; rewrite H0 in Ht2; clear H0 ft2;
      apply Hs2 with (n := n) in Ht2; clear Hs2;
      case Hs1n : (nth_error (list_gtypref (0%num, 0%num) t1 false) n) => [[[pv1 tt1] ori1]|]; rewrite Hs1n in Hs1e.
      - (* some *)
        1,3,5,7,9,11 : 
        case Hs2n : (nth_error (list_gtypref ref2 t2 ori) n) => [[[pv2 tt2] ori2]|]; rewrite Hs2n in Ht2.
        - (* some *)
          1,3,5,7,9,11 : 
          case Hten : (nth_error (list_gtypref (0%num, 0%num) t_expr false) n) => [[[tpv gte] ori0]|]; try done.
          - (* some *)
            1-6: apply find_mux_types_n with (n := n) (tt1 := (pv1, tt1, ori1)) (tt2 := (pv2, tt2, ori2)) (r1 := (N0,N0)) (r2 := ref2) (r3 := (N0,N0)) (ori1 := false) (ori2 := ori) (ori3 := false) (tte := (tpv, gte, ori0)) in Hte; try done;
            simpl in Hte; clear Hc;
            assert (exists e1, nth_error el1 n = Some e1) by admit;
              (* t_expr 和 t1 满足ftype_equiv，由Hs1n 和 Hsplit1知el1的长度小于n *)
            destruct H as [e1 He1];
            rewrite He1 in Hs1e;
            rewrite He2 in Hsplit2; simpl in Hsplit2; rewrite Hr2 in Hsplit2; inversion Hsplit2; clear Hsplit2;
            apply combine_mux_expr_n with (n := n) (el1 := el1) (el2 := el2) (e1 := e1) (e2 := (Eref (Eid pv2))) in Hsplit; try done.
            1,3,5,7,9,11 : rewrite Hsplit in Hrhsn; clear Hsplit;
            inversion Hrhsn; clear Hrhsn H0; simpl;
            rewrite Hce Hcf Hs1e Ht2; simpl; rewrite Hte; done.
            1-6 : specialize list_gtypref_fsteq with (r := ref2) (ft1 := t2) (ft2 := t_expr) (n := n) (pv := pv2) (gt1 := tt2) (ori := ori) (ori' := false) (ori1 := ori2); intro; apply H in Hs2n; clear H;
            destruct Hs2n as [gt2 [ori2' Hs2n]].
            1,3,5,7,9,11 : rewrite -H0 nth_error_map Hs2n; simpl; done.
            1-6 : apply mux_expr_type_equiv with (c := c) (s1 := s1) (s2 := s2) (te := t_expr) (te1 := t1) (te2 := t2) in Hte'; try done;
            move : Hte' => [_ Hte']; done.
          - (* none *) 
            1-6 : admit. (* not None *)
        - (* none *)
          1-6 : admit.
        1-6 : assert (ftype_equiv t_expr t1) by (apply mux_expr_type_equiv with (c := c) (s1 := s1) (s2 := s2) (te := t_expr) (te1 := t1) (te2 := t2) in Hte'; try done;
        move : Hte' => [Hte' _]; done);
        specialize ftype_equiv_split_eq with (s := s1) (t1 := t_expr) (t2 := t1); intro;
        rewrite H0 in Hsplit1; try done.
    - (*  s2 一般expr s1 ref *)
      1-6 : rewrite -He2 in Hs2; clear He2;
      generalize Hs2e; apply Hs2 with (rhs_expr_ls := el2) (n:= n) in Hs2e; try done; clear Hs2.
      1,3,5,7,9,11 : 
      intro Hs2e'; move => Hs1e'; simpl in Hs1e'; case Hr1 : r1 => [ref1|||]; rewrite Hr1 in Hs1e' Hs1; try discriminate;
      case Ht1 : (type_of_ref ref1 tmap) => [[ft1 ori]|]; rewrite Ht1 in Hs1e'; try discriminate; inversion Hs1e'; clear Hs1e'; rewrite H0 in Ht1; clear H0 ft1;
      apply Hs1 with (n := n) in Ht1; clear Hs1;
      case Hs2n : (nth_error (list_gtypref (0%num, 0%num) t2 false) n) => [[[pv2 tt2] ori2]|]; rewrite Hs2n in Hs2e.
      - (* some *)
        1,3,5,7,9,11 : 
        case Hs1n : (nth_error (list_gtypref ref1 t1 ori) n) => [[[pv1 tt1] ori1]|]; rewrite Hs1n in Ht1.
        - (* some *)
          1,3,5,7,9,11 : 
          case Hten : (nth_error (list_gtypref (0%num, 0%num) t_expr false) n) => [[[tpv gte] ori0]|]; try done.
          - (* some *)
            1-6: apply find_mux_types_n with (n := n) (tt1 := (pv1, tt1, ori1)) (tt2 := (pv2, tt2, ori2)) (r1 := ref1) (r2 := (N0,N0)) (r3 := (N0,N0)) (ori1 := ori) (ori2 := false) (ori3 := false) (tte := (tpv, gte, ori0)) in Hte; try done;
            simpl in Hte; clear Hc;
            assert (exists e2, nth_error el2 n = Some e2) by admit;
              (* t_expr 和 t1 满足ftype_equiv，由Hs1n 和 Hsplit1知el1的长度小于n *)
            destruct H as [e2 He2];
            rewrite He2 in Hs2e;
            rewrite He1 in Hsplit1; simpl in Hsplit1; rewrite Hr1 in Hsplit1; inversion Hsplit1; clear Hsplit1;
            apply combine_mux_expr_n with (n := n) (el1 := el1) (el2 := el2) (e1 := (Eref (Eid pv1))) (e2 := e2) in Hsplit; try done.
            1,3,5,7,9,11 : rewrite Hsplit in Hrhsn; clear Hsplit;
            inversion Hrhsn; clear Hrhsn H0; simpl;
            rewrite Hce Hcf Hs2e Ht1; simpl; rewrite Hte; done.
            1-6 : specialize list_gtypref_fsteq with (r := ref1) (ft1 := t1) (ft2 := t_expr) (n := n) (pv := pv1) (gt1 := tt1) (ori := ori) (ori' := false) (ori1 := ori1); intro; apply H in Hs1n; clear H;
            destruct Hs1n as [gt1 [ori1' Hs1n]].
            1,3,5,7,9,11 : rewrite -H0 nth_error_map Hs1n; simpl; done.
            1-6 : apply mux_expr_type_equiv with (c := c) (s1 := s1) (s2 := s2) (te := t_expr) (te1 := t1) (te2 := t2) in Hte'; try done;
            move : Hte' => [Hte' _]; done.
          - (* none *) 
            1-6 : admit. (* not None *)
        - (* none *)
          1-6 : admit.
        1-6 : assert (ftype_equiv t_expr t2) by (apply mux_expr_type_equiv with (c := c) (s1 := s1) (s2 := s2) (te := t_expr) (te1 := t1) (te2 := t2) in Hte'; try done;
        move : Hte' => [_ Hte']; done);
        specialize ftype_equiv_split_eq with (s := s2) (t1 := t_expr) (t2 := t2); intro;
        rewrite H0 in Hsplit2; try done.

    - (* s1 s2 ref *)
      move => Hs1e'; generalize Hs2e; rewrite He2 in Hs2e; rewrite He1 in Hs1e; intro Hs2e'; simpl in Hs2e; case Hr2 : r2 => [ref2|||]; rewrite Hr2 in Hs2e Hs2; try discriminate;
      case Ht2 : (type_of_ref ref2 tmap) => [[ft2 ori2]|]; rewrite Ht2 in Hs2e; try discriminate; inversion Hs2e; clear Hs2e; rewrite H0 in Ht2; clear H0 ft2.
      apply Hs2 with (n := n) in Ht2; clear Hs2.
      case Hr1 : r1 => [ref1|||]; rewrite Hr1 in Hs1e Hs1; simpl in Hs1e; try discriminate.
      case Ht1 : (type_of_ref ref1 tmap) => [[ft1 ori1]|]; rewrite Ht1 in Hs1e; try discriminate; inversion Hs1e; clear Hs1e; rewrite H0 in Ht1; clear H0 ft1.
      apply Hs1 with (n := n) in Ht1; clear Hs1.
      case Hs1n : (nth_error (list_gtypref ref1 t1 ori1) n) => [[[pv1 tt1] ori1']|]; rewrite Hs1n in Ht1.
      - (* some *)
        case Hs2n : (nth_error (list_gtypref ref2 t2 ori2) n) => [[[pv2 tt2] ori2']|]; rewrite Hs2n in Ht2.
        - (* some *)
          case Hten : (nth_error (list_gtypref (0%num, 0%num) t_expr false) n) => [[[tpv gte] ori0]|]; try done.
          - (* some *)
            apply find_mux_types_n with (n := n) (tt1 := (pv1, tt1, ori1')) (tt2 := (pv2, tt2, ori2')) (r1 := ref1) (r2 := ref2) (r3 := (N0,N0)) (ori1 := ori1) (ori2 := ori2) (ori3 := false) (tte := (tpv, gte, ori0)) in Hte; try done;
            simpl in Hte; clear Hc.
            rewrite He1 in Hsplit1; simpl in Hsplit1; rewrite Hr1 in Hsplit1; inversion Hsplit1; clear Hsplit1.
            rewrite He2 in Hsplit2; simpl in Hsplit2; rewrite Hr2 in Hsplit2; inversion Hsplit2; clear Hsplit2.
            apply combine_mux_expr_n with (n := n) (el1 := el1) (el2 := el2) (e1 := (Eref (Eid pv1))) (e2 := (Eref (Eid pv2))) in Hsplit; try done.
            rewrite Hsplit in Hrhsn; clear Hsplit;
            inversion Hrhsn; clear Hrhsn H0; simpl.
            rewrite Hce Hcf Ht1 Ht2; simpl; rewrite Hte; done.
            specialize list_gtypref_fsteq with (r := ref1) (ft1 := t1) (ft2 := t_expr) (n := n) (pv := pv1) (gt1 := tt1) (ori := ori1) (ori' := false) (ori1 := ori1'); intro; apply H in Hs1n; clear H;
            destruct Hs1n as [gt1 [ori1'' Hs1n]].
            rewrite -H0 nth_error_map Hs1n; simpl; done.
            rewrite -He1 in Hs1e'; apply mux_expr_type_equiv with (c := c) (s1 := s1) (s2 := s2) (te := t_expr) (te1 := t1) (te2 := t2) in Hte'; try done;
            move : Hte' => [Hte0 Hte']; done.
            specialize list_gtypref_fsteq with (r := ref2) (ft1 := t2) (ft2 := t_expr) (n := n) (pv := pv2) (gt1 := tt2) (ori := ori2) (ori' := false) (ori1 := ori2'); intro; apply H in Hs2n; clear H;
            destruct Hs2n as [gt2 [ori2'' Hs2n]].
            rewrite -H1 nth_error_map Hs2n; simpl; done.
            rewrite -He1 in Hs1e'; apply mux_expr_type_equiv with (c := c) (s1 := s1) (s2 := s2) (te := t_expr) (te1 := t1) (te2 := t2) in Hte'; try done;
            move : Hte' => [Hte0 Hte']; done.
          - (* none *) 
            admit. (* not None *)
        - (* none *)
          admit.
      - admit.
  - (* case2 : c 为 uint_implicit1 *)
    admit.

  (* validif *)
  admit.
  (* ref *)
  intros ref tmap.
  case Href : ref => [r|||];try done.
  intros ft ori Hte n.
  case Hfind : (nth_error (list_gtypref r ft ori) n) => [[[pv0 gt] ori0]|]; try done.
  move : Hte Hfind.
  apply list_gtypref_correct.
Admitted.

Lemma num_ref_gt1 : forall ft, 1 <= num_ref ft.
Proof.
  elim.
  intros; simpl; done.
  intros; simpl; rewrite addn1; apply ltn0Sn.
  intros; simpl; rewrite addn1; apply ltn0Sn. 
Qed.

Lemma set_find_sub : forall checkt nt nt0 n b, ft_set_sub checkt nt n = Some nt0 -> ftype_equiv checkt nt0 -> exists b0, ft_find_sub nt0 n b = Some (Gtyp nt, b0)
with set_find_sub_f : forall checkf nf nf0 n b, ft_set_sub_f checkf nf n = Some nf0 -> fbtyp_equiv checkf nf0 -> exists b0, ft_find_sub_f nf0 n b = Some (Gtyp nf, b0).
Proof.
  clear set_find_sub.
  elim.
  - (* set gtyp *)
    intros f nt nt0 n b Hset Heq.
    simpl in Heq.
    simpl in Hset.
    case Ha : (n == 0%num); rewrite Ha in Hset; try discriminate.
    inversion Hset; clear Hset H0.
    case Hnt0 : nt0 => [f0||]; rewrite Hnt0 in Heq; try discriminate.
    simpl; rewrite Ha; exists b; done.
  - (* set array *)
    intros f H fn nt nt0 n b Hset Heq.
    simpl in Hset.
    case Ha0 : (n == 0%num); rewrite Ha0 in Hset.
    inversion Hset; clear Hset.
    case Ht : nt0 => [|atyp na|]; rewrite Ht in Heq; simpl in Heq; try discriminate.
    simpl; rewrite Ha0.
    move /andP : Heq => [Heq0 Heq1].
    generalize Heq1.
    apply num_ref_eq in Heq1; move /eqP : Heq0 => Heq0; rewrite -Heq0 -Heq1.
    move => Heq1'.
    case Ha1 : (num_ref f * fn <= N.to_nat n - 1); rewrite Ha1 in Hset; try discriminate.
    case Ha : ((N.to_nat n - 1) mod num_ref f == 0).
    move /eqP : Ha => Ha; rewrite Ha in Hset.
    case Hset' : (ft_set_sub f nt (N.of_nat 0)) => [natyp|]; rewrite Hset' in Hset; try discriminate.
    case Hf : f => [gt||]; rewrite Hf in Hset'; simpl in Hset'; try discriminate.
    inversion Hset'; inversion Hset; clear Hset' Hset.
    rewrite -H2 -H1 in Ht.
    inversion Ht; exists b; done.
    apply H; try done. 
    case Hset' : (ft_set_sub f nt (N.of_nat ((N.to_nat n - 1) mod num_ref f))) => [natyp|]; 
      rewrite Hset' in Hset; try discriminate.
    rewrite Ht in Hset.
    inversion Hset; clear Hset; done.
  - (* set btyp *)
    intros f nt nt0 n b Hset Heq.
    simpl in Hset.
    case Ha : (n == 0%num); rewrite Ha in Hset; try discriminate.
    case Hset' : (ft_set_sub_f f nt n) => [newf|]; rewrite Hset' in Hset; try discriminate.
    inversion Hset; clear Hset.
    simpl.
    rewrite Ha.
    rewrite -H0 in Heq; simpl in Heq. 
    move : Hset' Heq; apply set_find_sub_f.

  clear set_find_sub_f.
  intros checkf.
  induction checkf.
  - (* induction case1 *)
    intros nf nf0 n Hset Heq.
    simpl in Hset; discriminate.
  - (* induction case2 *)
    intros nf nf0 n b Hset Heq.
    simpl in Hset.
    case Hnf0 :  nf0 => [|v' fl' ft' ff']; rewrite Hnf0 in Heq; simpl in Heq; case Hf : f; rewrite Hf in Heq; try discriminate.
    - (* flip *)
      case Hf' : fl'; rewrite Hf' in Heq; try discriminate.
      simpl.
      case Hn : (n == 1%num).
      - move /eqP : Hn => Hn; rewrite Hn in Hset.
        assert ((num_ref f0 < N.to_nat 1) = false).
        apply leq_gtF; apply num_ref_gt1.
        rewrite H in Hset.
        rewrite N.sub_diag in Hset.
        case Hset' : (ft_set_sub f0 nf 0) => [newt'|]; rewrite Hset' in Hset; try discriminate.
        rewrite Hnf0 in Hset; clear Hnf0; rewrite Hf in Hset; clear Hf f; rewrite Hf' in Hset; clear Hf' fl'.
        inversion Hset; clear Hset; rewrite H2 in Hset'; clear H2 newt' IHcheckf H1 H3.
        move /andP : Heq => [Heq _]; move /andP : Heq => [_ Heq].
        specialize set_find_sub with (checkt := f0) (nt := nf) (nt0 := ft') (n := N0) (b := b).
        apply set_find_sub in Hset'; try done.
        destruct Hset' as [b0 Hset'].
        case Hf0 : f0 => [gt||]; rewrite Hf0 in Heq; simpl in Heq; case Hft' : ft' => [gt'||]; rewrite Hft' in Heq Hset'; simpl in Hset'; try discriminate.
        inversion Hset'; clear Hset'; exists (~~b0); done.
      - move /andP : Heq => [Heq0 Heq1]; move /andP : Heq0 => [_ Heq2].
        generalize Heq2.
        apply num_ref_eq in Heq2; rewrite -Heq2.
        move => Heq2'.
        case Ha : (num_ref f0 < N.to_nat n); rewrite Ha in Hset.
        - case Hset' : (ft_set_sub_f checkf nf (N.of_nat (N.to_nat n - num_ref f0))) => [newf|]; rewrite Hset' in Hset; try discriminate.
          rewrite Hnf0 in Hset.
          inversion Hset; clear Hset.
          rewrite H3 in Hset'; rewrite -Heq2.
          move : Hset' Heq1.
          apply IHcheckf.
        - case Hset' : (ft_set_sub f0 nf (n - 1)) => [newt'|]; rewrite Hset' in Hset; try discriminate.
          rewrite Hnf0 in Hset; inversion Hset; clear Hset.
          rewrite H2 in Hset'.
          move : Hset' Heq2'.
          apply set_find_sub.
    - (* nflip *)
      case Hf' : fl'; rewrite Hf' in Heq; try discriminate.
      simpl.
      case Hn : (n == 1%num).
      - move /eqP : Hn => Hn; rewrite Hn in Hset.
        assert ((num_ref f0 < N.to_nat 1) = false).
        apply leq_gtF; apply num_ref_gt1.
        rewrite H in Hset.
        rewrite N.sub_diag in Hset.
        case Hset' : (ft_set_sub f0 nf 0) => [newt'|]; rewrite Hset' in Hset; try discriminate.
        rewrite Hnf0 in Hset; clear Hnf0; rewrite Hf in Hset; clear Hf f; rewrite Hf' in Hset; clear Hf' fl'.
        inversion Hset; clear Hset; rewrite H2 in Hset'; clear H2 newt' IHcheckf H1 H3.
        move /andP : Heq => [Heq _]; move /andP : Heq => [_ Heq].
        specialize set_find_sub with (checkt := f0) (nt := nf) (nt0 := ft') (n := N0) (b := b).
        apply set_find_sub in Hset'; try done.
        destruct Hset' as [b0 Hset'].
        case Hf0 : f0 => [gt||]; rewrite Hf0 in Heq; simpl in Heq; case Hft' : ft' => [gt'||]; rewrite Hft' in Heq Hset'; simpl in Hset'; try discriminate.
        inversion Hset'; clear Hset'; exists (b0); done.
      - move /andP : Heq => [Heq0 Heq1]; move /andP : Heq0 => [_ Heq2].
        generalize Heq2.
        apply num_ref_eq in Heq2; rewrite -Heq2.
        move => Heq2'.
        case Ha : (num_ref f0 < N.to_nat n); rewrite Ha in Hset.
        - case Hset' : (ft_set_sub_f checkf nf (N.of_nat (N.to_nat n - num_ref f0))) => [newf|]; rewrite Hset' in Hset; try discriminate.
          rewrite Hnf0 in Hset.
          inversion Hset; clear Hset.
          rewrite H3 in Hset'; rewrite -Heq2.
          move : Hset' Heq1.
          apply IHcheckf.
        - case Hset' : (ft_set_sub f0 nf (n - 1)) => [newt'|]; rewrite Hset' in Hset; try discriminate.
          rewrite Hnf0 in Hset; inversion Hset; clear Hset.
          rewrite H2 in Hset'.
          move : Hset' Heq2'.
          apply set_find_sub.
Qed.

Lemma max_compatible' : forall gte gt tmax, max_fgtyp gte gt = Some tmax -> (sizeof_fgtyp gte <= sizeof_fgtyp tmax) && fgtyp_equiv tmax gte && fgtyp_equiv tmax gt && (sizeof_fgtyp gt <= sizeof_fgtyp tmax).
Proof.
  intros.
  case Hgte : gte => [w'|w'|w'|w'|||]; rewrite Hgte in H.
  (* gte = Gtyp (uint w') *)
  - case Hgt : gt => [ow'|ow'|ow'|ow'|||]; rewrite Hgt in H; simpl in Hgt; simpl in H; try discriminate.
    inversion H; clear H.
    simpl.
    rewrite Nat.max_comm.
    apply rwP with (P := (w' <= Nat.max ow' w') && true && true /\ (ow' <= Nat.max ow' w')).
    apply andP.
    split; try apply Nats.le_leq; try apply Nat.le_max_l.
    apply rwP with (P := (w' <= Nat.max ow' w') && true /\ true).
    apply andP.
    split; try done.
    apply rwP with (P := (w' <= Nat.max ow' w') /\ true).
    apply andP.
    split; try done; try apply Nats.le_leq; try apply Nat.le_max_r.
  - case Hgt : gt => [ow'|ow'|ow'|ow'|||]; rewrite Hgt in H; simpl in Hgt; simpl in H; try discriminate.
    inversion H; clear H.
    simpl.
    rewrite Nat.max_comm.
    apply rwP with (P := (w' <= Nat.max ow' w') && true && true /\ (ow' <= Nat.max ow' w')).
    apply andP.
    split; try apply Nats.le_leq; try apply Nat.le_max_l.
    apply rwP with (P := (w' <= Nat.max ow' w') && true /\ true).
    apply andP.
    split; try done.
    apply rwP with (P := (w' <= Nat.max ow' w') /\ true).
    apply andP.
    split; try done; try apply Nats.le_leq; try apply Nat.le_max_r.
  - case Hgt : gt => [ow'|ow'|ow'|ow'|||]; rewrite Hgt in H; simpl in Hgt; simpl in H; try discriminate.
    inversion H; clear H.
    simpl.
    rewrite Nat.max_comm.
    apply rwP with (P := (w' <= Nat.max ow' w') && true && true /\ (ow' <= Nat.max ow' w')).
    apply andP.
    split; try apply Nats.le_leq; try apply Nat.le_max_l.
    apply rwP with (P := (w' <= Nat.max ow' w') && true /\ true).
    apply andP.
    split; try done.
    apply rwP with (P := (w' <= Nat.max ow' w') /\ true).
    apply andP.
    split; try done; try apply Nats.le_leq; try apply Nat.le_max_r.
  - case Hgt : gt => [ow'|ow'|ow'|ow'|||]; rewrite Hgt in H; simpl in Hgt; simpl in H; try discriminate.
    inversion H; clear H.
    simpl.
    rewrite Nat.max_comm.
    apply rwP with (P := (w' <= Nat.max ow' w') && true && true /\ (ow' <= Nat.max ow' w')).
    apply andP.
    split; try apply Nats.le_leq; try apply Nat.le_max_l.
    apply rwP with (P := (w' <= Nat.max ow' w') && true /\ true).
    apply andP.
    split; try done.
    apply rwP with (P := (w' <= Nat.max ow' w') /\ true).
    apply andP.
    split; try done; try apply Nats.le_leq; try apply Nat.le_max_r.
  - case Hgt : gt => [ow'|ow'|ow'|ow'|||]; rewrite Hgt in H; simpl in Hgt; simpl in H; try discriminate.
  - case Hgt : gt => [ow'|ow'|ow'|ow'|||]; rewrite Hgt in H; simpl in Hgt; simpl in H; try discriminate.
  - case Hgt : gt => [ow'|ow'|ow'|ow'|||]; rewrite Hgt in H; simpl in Hgt; simpl in H; try discriminate.
Qed.

Lemma max_compatible : forall el tmap eftl initt tmax, fil_ftlist (map (fun e => type_of_expr e tmap) el) = Some eftl -> forall expr gte, expr \in el -> type_of_expr expr tmap = Some (Gtyp gte) -> max_ftlist eftl initt = Some tmax -> (sizeof_fgtyp gte <= sizeof_fgtyp tmax) && fgtyp_equiv tmax gte.
Proof.
  elim.
  intros.
  rewrite in_nil in H0; discriminate.
  intros hd tl IH tmap eftl initt tmax Hfil expr gte Hin Hgte Hmax.
  rewrite in_cons in Hin.
  case Heq : (expr == hd).
  (* case1 *)
  move /eqP : Heq => Heq.
  rewrite Heq in Hgte.
  simpl in Hfil. 
  rewrite Hgte in Hfil. 
  case Hfil' : (fil_ftlist [seq type_of_expr e tmap | e <- tl]) => [eftl'|]; rewrite Hfil' in Hfil; try discriminate.
  inversion Hfil; clear Hfil.
  rewrite -H0 in Hmax.
  simpl in Hmax.
  case Hmax' : (max_ftlist eftl' initt) => [tmax'|]; rewrite Hmax' in Hmax; try discriminate.
  specialize max_compatible' with (gte := gte) (gt := tmax') (tmax := tmax); intro.
  apply H in Hmax; clear H.
  move /andP : Hmax => [H1 _].
  move /andP : H1 => [H1 _]; done.
  (* case2 *)
  rewrite Heq in Hin.
  rewrite orb_false_l in Hin; clear Heq.
  simpl in Hfil.
  case Hhd : (type_of_expr hd tmap) => [t|]; rewrite Hhd in Hfil;  try discriminate.
  case Hgt : t =>[gt||]; rewrite Hgt in Hfil; try discriminate.
  case Hfil' : (fil_ftlist [seq type_of_expr e tmap | e <- tl]) => [eftl'|]; rewrite Hfil' in Hfil; try discriminate.
  inversion Hfil; clear Hfil.
  rewrite -H0 in Hmax.
  simpl in Hmax.
  case Hmax' : (max_ftlist eftl' initt) => [tmax'|]; rewrite Hmax' in Hmax; try discriminate.
  apply IH with (initt := initt) (tmax := tmax') (expr := expr) (gte := gte) in Hfil'; try done.
  move /andP : Hfil' => [H1 H2].
  apply rwP with (P := (sizeof_fgtyp gte <= sizeof_fgtyp tmax) /\ fgtyp_equiv tmax gte).
  apply andP.
  split.
  specialize max_compatible' with (gte := gt) (gt := tmax') (tmax := tmax); intro H.
  apply H in Hmax; clear H.
  move /andP : Hmax => [_ H3].
  move : H1 H3.
  apply leq_trans.
  specialize max_compatible' with (gte := gt) (gt := tmax') (tmax := tmax); intro H.
  apply H in Hmax; clear H.
  move /andP : Hmax => [Hmax _].
  move /andP : Hmax => [_ H3].
  move : H3 H2.
  apply fgtyp_equiv_dlvr.
Qed.

Lemma max_ftlist_correct : forall eftl initt tmax, max_ftlist eftl initt = Some tmax -> (not_implicit initt = false -> not_implicit tmax = false) /\ fgtyp_equiv initt tmax.
Proof.
  elim.
  intros.
  split.
  intros.
  simpl in H. 
  inversion H.
  rewrite -H2; done.
  simpl in H. 
  inversion H.
  apply fgtyp_equiv_refl.

  intros hd tl H init nt Hl.
  split.
  intro Himpli.
  simpl in Hl. 
  case Htl : (max_ftlist tl init) => [nt'|]; rewrite Htl in Hl; try discriminate.
  apply H in Htl; try done.
  rewrite /max_fgtyp in Hl.
  case Hhd : hd; rewrite Hhd in Hl; try discriminate.
  1-4 : case Hnt' : nt'; rewrite Hnt' in Hl Htl; try discriminate; inversion Hl; simpl; try done.
  
  simpl in Hl. 
  case Htl : (max_ftlist tl init) => [nt'|]; rewrite Htl in Hl; try discriminate.
  apply H in Htl; try done.
  move : Htl => [_ Htl].
  specialize max_compatible' with (gte := hd) (gt := nt') (tmax := nt); intro.
  apply H0 in Hl; clear H0.
  move /andP : Hl => [H1 _].
  move /andP : H1 => [_ H1].
  assert (fgtyp_equiv nt' nt).
  apply fgtyp_equiv_comm; done.
  move : Htl H0.
  apply fgtyp_equiv_dlvr.
Qed.

(*Lemma type_of_expr_eq : forall pv el tmap newtm, InferWidth_fun pv el tmap = Some newtm -> forall expr, expr \in el -> type_of_expr expr tmap = type_of_expr expr newtm.
Proof.
Admitted.*)

Lemma type_of_expr_eqs : forall expr inferorder var2exprs tmap newtm vl, InferWidths_fun inferorder var2exprs tmap = Some newtm -> expr2varlist expr = Some vl -> (forall v, v \in vl -> v \notin inferorder) -> 
type_of_expr expr tmap = type_of_expr expr newtm
with type_of_expr_eq : forall expr hd el tmap newtm vl, InferWidth_fun hd el tmap = Some newtm -> expr2varlist expr = Some vl -> (forall v, v \in vl -> v != hd) -> 
type_of_expr expr tmap = type_of_expr expr newtm.
Proof.
Admitted. (* TBD *)

Lemma ft_set_sub_eq : forall checkt nt' nt0 n init b b0, ft_find_sub checkt n b = Some (init, b0) -> ftype_equiv init (Gtyp nt') -> ft_set_sub checkt nt' n = Some nt0 -> ftype_equiv checkt nt0
with ft_set_sub_eq_f : forall checkf nf' nf0 n init b b0, ft_find_sub_f checkf n b = Some (init, b0) -> ftype_equiv init (Gtyp nf') -> ft_set_sub_f checkf nf' n = Some nf0 -> fbtyp_equiv checkf nf0.
Proof.
  clear ft_set_sub_eq.
  elim.
  - (* set gtyp *)
    intros f nt nt0 n init b b0 Hfind Heq Hset.
    simpl in Hset.
    case Hn : (n == 0%num); rewrite Hn in Hset; try discriminate.
    inversion Hset; simpl.
    move /eqP : Hn => Hn; rewrite Hn in Hfind; simpl in Hfind; inversion Hfind; clear Hfind.
    rewrite -H1 in Heq; simpl in Heq; done.
  - (* set aggt *)
    intros f H n0 nt nt0 n init b b0 Hfind Heq Hset.
    simpl in Hset.
    simpl in Hfind.
    case Ha0 : (n == 0%num); rewrite Ha0 in Hset Hfind; try discriminate.
    case Hn : (num_ref f * n0 <= N.to_nat n - 1); rewrite Hn in Hset Hfind; try discriminate.
    case Ha : ((N.to_nat n - 1) mod num_ref f == 0); rewrite Ha in Hfind.
    move /eqP : Ha => Ha; rewrite Ha in Hset.
    case Hset' : (ft_set_sub f nt (N.of_nat 0)) => [natyp|]; rewrite Hset' in Hset; try discriminate.
    case Hf : f => [gt||]; rewrite Hf in Hset'; simpl in Hset'; try discriminate.
    inversion Hset'; inversion Hset; inversion Hfind; clear Hset' Hset Hfind.
    rewrite -Hf H3 -H1; simpl; rewrite eq_refl Heq //.
    case Hset' : (ft_set_sub f nt (N.of_nat ((N.to_nat n - 1) mod num_ref f))) => [natyp|]; 
      rewrite Hset' in Hset; try discriminate.
    inversion Hset; clear Hset.
    simpl; rewrite eq_refl.
    apply H with (init := init) (b := b) (b0 := b0) in Hset'; try done.
  - (* set btyp *)
    intros f nt nt0 cnt init b b0 Hfind Heq Hset.
    simpl in Hfind.
    simpl in Hset.
    case Ha : (cnt == 0%num); rewrite Ha in Hfind Hset; try discriminate.
    case Hset' : (ft_set_sub_f f nt cnt) => [nf|]; rewrite Hset' in Hset; try discriminate.
    inversion Hset; clear Hset.
    simpl.
    move : Hfind Heq Hset'.
    apply ft_set_sub_eq_f.

  (* field *)
  clear ft_set_sub_eq_f.
  induction checkf.
  - (* Fnil *)
    intros.
    simpl in H; discriminate.
  - (* ffield *)
    intros nt nf0 cnt init b b0 Hfind Heq Hset.
    simpl in Hfind.
    simpl in Hset.
    case Ha : (cnt == 1%num); rewrite Ha in Hfind.
    - move /eqP : Ha => Ha; rewrite Ha in Hset. 
      assert ((num_ref f0 < N.to_nat 1) = false) by (apply leq_gtF; apply num_ref_gt1; rewrite H in Hset; rewrite N.sub_diag in Hset).
      rewrite H in Hset.
      rewrite N.sub_diag in Hset.
      case Hset' : (ft_set_sub f0 nt 0) => [newt'|]; rewrite Hset' in Hset; try discriminate.
      inversion Hset; clear Hset; simpl.
      case Hf: f; rewrite Hf in Hfind; inversion Hfind; clear Hfind.
      - (* flip *)
        rewrite H2 in Hset' H; rewrite Hf in H1; clear H2 f0 H3 b b0 Hf f.
        case Hinit : init => [ginit||]; rewrite Hinit in Hset' Heq; simpl in Hset'; simpl in Heq; try discriminate.
        inversion Hset'; simpl; rewrite eq_refl fbtyp_equiv_refl Heq; done.
      - (* nflip *)
        rewrite H2 in Hset' H; rewrite Hf in H1; clear H2 f0 H3 b b0 Hf f.
        case Hinit : init => [ginit||]; rewrite Hinit in Hset' Heq; simpl in Hset'; simpl in Heq; try discriminate.
        inversion Hset'; simpl; rewrite eq_refl fbtyp_equiv_refl Heq; done.
    - case Hn : (num_ref f0 < N.to_nat cnt); rewrite Hn in Hset Hfind.
      - case Hset' : (ft_set_sub_f checkf nt (N.of_nat (N.to_nat cnt - num_ref f0))) => [newf|]; rewrite Hset' in Hset; try discriminate.
        inversion Hset; clear Hset.
        simpl.
        case Hf: f; rewrite Hf in Hfind; inversion Hfind; clear Hfind.
        - (* flip *)
          apply IHcheckf with (init := init) (b := b) (b0 := b0) in Hset'; try done.
          rewrite eq_refl ftype_equiv_refl Hset'; done.
        - (* nflip *)
          apply IHcheckf with (init := init) (b := b) (b0 := b0) in Hset'; try done.
          rewrite eq_refl ftype_equiv_refl Hset'; done.
      - case Hset' : (ft_set_sub f0 nt (cnt - 1)) => [newt'|]; rewrite Hset' in Hset; try discriminate.
        inversion Hset; clear Hset.
        simpl.
        case Hf: f; rewrite Hf in Hfind; inversion Hfind; clear Hfind.
        - (* flip *)
          apply ft_set_sub_eq with (init := init) (b := ~~b) (b0 := b0) in Hset'; try done.
          rewrite eq_refl fbtyp_equiv_refl Hset'; done.
        - (* nflip *)
          apply ft_set_sub_eq with (init := init) (b := b) (b0 := b0) in Hset'; try done.
          rewrite eq_refl fbtyp_equiv_refl Hset'; done.
Qed.

Lemma InferWidth_fun_correct : forall pv el tmap newtm, InferWidth_fun pv el tmap = Some newtm -> forall expr, expr \in el -> 
      match CEP.find (fst pv, N0) newtm with
      | Some (checkt, ori) => match ft_find_sub checkt pv.2 false, type_of_expr expr newtm with
                              | Some (Gtyp nt, _), Some (Gtyp te) => fgtyp_equiv nt te -> connect_fgtyp_compatible nt te
                              | _,_ => true
                              end
      | _ => true
      end.
Proof.
  intros pv el tmap newtm Hinfer expr Hin.
  generalize Hinfer; rewrite /InferWidth_fun in Hinfer; intro Hinfer'.
  case Hel : (fil_ftlist [seq type_of_expr e tmap | e <- el]) => [eftl|]; rewrite Hel in Hinfer; try discriminate.
  case Hinit : (CEP.find (pv.1, 0%num) tmap) => [[init ori]|]; rewrite Hinit in Hinfer; try discriminate.
  case Hinitt : (ft_find_sub init pv.2 false) => [[initt ori0]|]; rewrite Hinitt in Hinfer; try discriminate.
  case Hinitt'' : initt => [initt''||]; rewrite Hinitt'' in Hinfer; try discriminate.
  case Hmax : (max_ftlist eftl initt'') => [tmax|]; rewrite Hmax in Hinfer; try discriminate.
  case Hset : (ft_set_sub init tmax pv.2) => [nt0|]; rewrite Hset in Hinfer; try discriminate.
  assert (Hvl : exists vl, expr2varlist expr = Some vl) by admit.
  destruct Hvl as [vl Hvl].
  apply type_of_expr_eq with (expr := expr) (vl := vl) in Hinfer'; try done. rewrite -Hinfer'; clear Hinfer'.
  inversion Hinfer; clear Hinfer.
  rewrite CEP.Lemmas.find_add_eq; try apply CEP.SE.eq_refl; clear H0 newtm.
  case Hnt : (ft_find_sub nt0 pv.2 false) => [[nt orin]|]; try done.
  case Hinitt' : nt => [initt'||]; try done.
  specialize set_find_sub with (checkt := init) (nt := tmax) (n := pv.2) (nt0 := nt0) (b := false); intro.
  generalize Hset; apply H in Hset; try done; clear H.
  destruct Hset as [b0 Hset]; rewrite Hnt in Hset; inversion Hset; clear Hset; intro Hset.
  rewrite H1 in Hnt; clear H1 orin; rewrite H0 in Hinitt'; inversion Hinitt'; clear Hinitt'.
  rewrite H0 in Hnt; clear H0 nt; rewrite -H1; clear H1 initt'; rewrite Hinitt'' in Hinitt; clear Hinitt'' initt.
  assert (Himpli : not_implicit initt'' = false).
  admit.
  generalize Hmax; apply max_ftlist_correct in Hmax; move : Hmax => [Hmax _]; apply Hmax in Himpli; clear Hmax; intro Hmax.
  case Hte : (type_of_expr expr tmap) => [te|]; try done.
  case Hgt : te => [gt||]; try done.
  intro; rewrite /connect_fgtyp_compatible Himpli.
  rewrite Hgt in Hte; clear Hgt te; apply max_compatible with (el := el) (tmap := tmap) (expr := expr) (gte := gt) in Hmax; try done.
  move /andP : Hmax => [Hmax H1]; rewrite H1 Hmax //. 
  apply ft_set_sub_eq with (nt' := tmax) (nt0 := nt0) in Hinitt; try done.
  rewrite Hinitt''; simpl.
  apply max_ftlist_correct in Hmax; move : Hmax => [_ Hmax]; done.
  (* Topo 的性质 *)
Admitted.

Lemma inferneq_eq : forall a v expr_seq tmap tmap', InferWidth_fun v expr_seq tmap = Some tmap' -> 
  if (a != v) then type_of_ref a tmap' = type_of_ref a tmap
  (*match CEP.find (fst a, N0) tmap, CEP.find (fst a, N0) tmap' with
        | Some (ft, ori), Some (ft', ori') => ft_find_sub ft (snd a) ori = ft_find_sub ft' (snd a) ori'
        | _, _ => True
        end*)
  else True. 
Proof.
  intros.
  (*case Heq : (a != v); try done.*)
  (*destruct Heq.


  destruct a as [a0 a1]; destruct v as [v0 v1].
  case Heq : ((a0, a1) != (v0, v1)); try done.
    inversion Heq.
  - move /eqP : Heq => Heq; rewrite Heq; clear Heq.
    case Heq' : (a1 == v1).
    -  move /eqP : Heq' => Heq'.
      rewrite Heq Heq'; simpl.
      
    admit.
    assert ((a0, a1) != (v0, v1)).
    admit.
    rewrite H0; clear H0; simpl.
    case Ha : (CEP.find (a0, 0%num) tmap) => [ft|]; try done.
    case Ha' : (CEP.find (a0, 0%num) tmap') => [ft'|]; try done.
    rewrite /InferWidth_fun in H.
    case Hel : (fil_ftlist [seq type_of_hfexpr e tmap | e <- expr_seq]) => [eftl|]; rewrite Hel in H; try discriminate.
    simpl in H; move /eqP : Heq => Heq; rewrite -Heq Ha in H.
    case Hsub : (ft_find_sub ft v1) => [initt|]; rewrite Hsub in H; try discriminate.
    case Hinitt : initt => [initt'||]; rewrite Hinitt in H; try discriminate.
    case Himpli : (not_implicit initt'); rewrite Himpli in H.
    (* case1 *)
    inversion H; clear H.
    rewrite H1 in Ha.
    rewrite Ha in Ha'.
    inversion Ha'; done.
    (* case2 *)
    case Hmax : (max_ftlist eftl initt') => [nt|]; rewrite Hmax in H; try discriminate.
    case Hinfer : (ft_set_sub ft nt v1) => [nt0|]; rewrite Hinfer in H; try discriminate.
    inversion H; clear H.
    rewrite -H1 in Ha'.
    rewrite HiFP.PCELemmas.OP.P.F.add_eq_o in Ha'; try apply CEP.SE.eq_refl.
    inversion Ha'; clear Ha'; rewrite -H0.
    move : Heq' Hinfer.
    apply set_find_sub_neq.
    
  assert ((a0, a1) != (v0, v1)).
  admit.
  rewrite H0; clear H0; simpl.
  case Ha : (CEP.find (a0, 0%num) tmap) => [ft|]; try done.
  case Ha' : (CEP.find (a0, 0%num) tmap') => [ft'|]; try done.
  rewrite /InferWidth_fun in H.
  case Hel : (fil_ftlist [seq type_of_hfexpr e tmap | e <- expr_seq]) => [eftl|]; rewrite Hel in H; try discriminate.
  case Hfindv0 : (CEP.find (v0, 0%num) tmap) => [init|]; rewrite Hfindv0 in H; try discriminate.
  case Hsub : (ft_find_sub init v1) => [initt|]; rewrite Hsub in H; try discriminate.
  case Hinitt : initt => [initt'||]; rewrite Hinitt in H; try discriminate.
  case Himpli : (not_implicit initt'); rewrite Himpli in H.
  (* case1 *)
  inversion H; clear H.
  rewrite H1 in Ha.
  rewrite Ha in Ha'.
  inversion Ha'; done.
  (* case2 *)
  case Hmax : (max_ftlist eftl initt') => [nt|]; rewrite Hmax in H; try discriminate.
  case Hinfer : (ft_set_sub init nt v1) => [nt0|]; rewrite Hinfer in H; try discriminate.
  inversion H; clear H.
  rewrite -H1 in Ha'.
  rewrite HiFP.PCELemmas.OP.P.F.add_neq_o in Ha'.
  rewrite Ha' in Ha. 
  inversion Ha; done.*)
Admitted. (* TBD *)

Lemma infernotin_eq : forall inferorder pv var2exprs tmap newtm, pv \notin inferorder -> InferWidths_fun inferorder var2exprs tmap = Some newtm ->
type_of_ref pv newtm = type_of_ref pv tmap. 
Proof.
  elim.
  - (* nil *)
    intros.
    simpl in H0. 
    inversion H0; clear H0; split; try done.
  - (* cons *)
    intros hd tl IH a var2exprs tmap tmap' Hin Hinfer.
    rewrite in_cons in Hin.
    rewrite negb_or in Hin.
    move /andP : Hin => [H H1].
    simpl in Hinfer.
    case Hel : (CEP.find hd var2exprs) => [el|]; rewrite Hel in Hinfer; try discriminate.
    case Hinfer' : (InferWidth_fun hd el tmap) => [newtm|]; rewrite Hinfer' in Hinfer; try discriminate.
    apply inferneq_eq with (a := a) in Hinfer'; rewrite H in Hinfer'.
    apply IH with (pv := a) in Hinfer; try done.
    try rewrite Hinfer Hinfer' //.
Qed.

Fixpoint find_sub_expr4v (pv : ProdVarOrder.t) (lhsl : seq (ProdVarOrder.t * fgtyp * bool)) (rstl : seq HiFP.hfexpr) : option (seq HiFP.hfexpr) :=
  match lhsl, rstl with
  | nil, nil => Some nil
  | (hd, _, _) :: tl, hde :: tle => if (hd == pv) then Some [:: hde]
                              else find_sub_expr4v pv tl tle
  | _, _ => None
  end.

Fixpoint find_sub_non_passive4v (pv : ProdVarOrder.t) (lhsl rhsl : seq (ProdVarOrder.t * fgtyp * bool)) : option (seq HiFP.hfexpr) :=
  match lhsl, rhsl with
  | nil, nil => Some nil
  | (thd, _, false) :: tl, (shd, _, _) :: tle => if (thd == pv) then Some [:: (Eref (Eid shd))]
                                                            else find_sub_non_passive4v pv tl tle
  | (thd, _, true) :: tl, (shd, _, _) :: tle => if (shd == pv) then Some [:: (Eref (Eid thd))]
                                                            else find_sub_non_passive4v pv tl tle
  | _, _ => None
  end.

Fixpoint find_sub_expr (pv : ProdVarOrder.t) (s : HiFP.hfstmt) (tmap : CEP.t (ftype * HiF.forient)) : option (seq HiFP.hfexpr) :=
  match s with
  | Sreg v r => match reset r with
                | NRst => Some nil
                | Rst _ rst_val => match list_gtypexpr rst_val (type r), list_gtypref v (type r) false with
                                  | Some rstl, lhsl => find_sub_expr4v pv lhsl rstl
                                  | _, _ => None
                                  end
                end
  | Snode v e => match type_of_expr e tmap with
                | Some t => match list_gtypexpr e t, list_gtypref v t false with
                            | Some rstl, lhsl => find_sub_expr4v pv lhsl rstl
                            | _, _ => None
                            end
                | _ => None
                end
  | Sfcnct (Eid ref_tgt) (Eref (Eid ref_src)) =>
                match type_of_ref ref_tgt tmap, type_of_ref ref_src tmap with
                | Some (t_tgt, ori_tgt), Some (t_src, ori_src) =>
                            match list_gtypref ref_tgt t_tgt ori_tgt, list_gtypref ref_src t_src ori_src with
                            | lhsl, rhsl => find_sub_non_passive4v pv lhsl rhsl
                            end
                | _, _ => None
                end
  | Sfcnct (Eid ref_tgt) (Eref _) => None
  | Sfcnct (Eid ref_tgt) expr_src =>
                match type_of_ref ref_tgt tmap, type_of_expr expr_src tmap with
                | Some (t_tgt, ori_tgt), Some t_src =>
                      match list_gtypexpr expr_src t_src, list_gtypref ref_tgt t_tgt ori_tgt with
                      | Some rstl, lhsl => find_sub_expr4v pv lhsl rstl
                      | _, _ => None
                      end
                | _, _ => None
                end
  | Swhen _ s1 s2 => match find_sub_exprs pv s1 tmap, find_sub_exprs pv s2 tmap with
                    | Some e1, Some e2 => Some (e1 ++ e2)
                    | _,_ => None
                    end
  | _ => Some nil
  end
with find_sub_exprs (v : ProdVarOrder.t) (ss : HiFP.hfstmt_seq) (tmap : CEP.t (ftype *HiF.forient)) : option (seq HiFP.hfexpr) :=
  match ss with
  | Qnil => Some nil
  | Qcons s ss' => match find_sub_expr v s tmap, find_sub_exprs v ss' tmap with
                  | Some e, Some el => Some (e ++ el)
                  | _, _ => None
                  end
  end.

Lemma find_sub_expr4v_in : forall (lhsl : seq (ProdVarOrder.t * fgtyp * bool)) rhsl n tgt texpr, nth_error lhsl n = Some tgt -> nth_error rhsl n = Some texpr -> find_sub_expr4v tgt.1.1 lhsl rhsl = Some [:: texpr].
Proof.
  elim. 
  - (* nil *)
    intros.
    apply nth_error_In in H.
    apply List.in_nil in H; done.
  - (* cons *)
    intros hd tl H.
    - (* nil *)
      elim. 
      intros.
      apply nth_error_In in H1.
      apply List.in_nil in H1; done.
    - (* cons *)
      intros hd0 tl0 H0; clear H0.
      intros n [[pv0 t0] ori0]; intros.
      induction n as [|n'].
      simpl in H0; simpl in H1.
      inversion H0; inversion H1; clear H0 H1.
      simpl. rewrite eq_refl //.
      assert (nth_error (hd :: tl) n'.+1 = nth_error tl n').
        specialize nth_error_app2 with (l := [::hd])
          (l' := tl) (n := n'.+1); intros.
        rewrite H2; simpl.
        rewrite -Nats.subn_sub subn0 //.
        apply Nats.leq_le; apply ltn0Sn.
      assert (nth_error (hd0 :: tl0) n'.+1 = nth_error tl0 n').
        specialize nth_error_app2 with (l := [::hd0])
          (l' := tl0) (n := n'.+1); intros.
        rewrite H3; simpl.
        rewrite -Nats.subn_sub subn0 //.
        apply Nats.leq_le; apply ltn0Sn.
      simpl.
      rewrite H2 in H0; rewrite H3 in H1; clear IHn' H2 H3.
      assert ((hd.1.1 == pv0) = false).
      admit.
  destruct hd as [[a b] c]; simpl in H2; rewrite H2.
  move : H0 H1.
  apply H.
Admitted.

Lemma find_sub_non_passive4v_in : forall (lhsl : seq (ProdVarOrder.t * fgtyp * bool)) (rhsl : seq (ProdVarOrder.t * fgtyp * bool)) n tgt src, nth_error lhsl n = Some tgt -> nth_error rhsl n = Some src ->
  if tgt.2 then find_sub_non_passive4v src.1.1 lhsl rhsl = Some [:: (Eref (Eid tgt.1.1))]
  else find_sub_non_passive4v tgt.1.1 lhsl rhsl = Some [:: (Eref (Eid src.1.1))].
Proof.
  elim. 
  - (* nil *)
    intros.
    apply nth_error_In in H.
    apply List.in_nil in H; done.
  - (* cons *)
    intros [[hd ft] ori] tl H.
    - (* nil *)
      elim. 
      intros.
      apply nth_error_In in H1.
      apply List.in_nil in H1; done.
    - (* cons *)
      intros [[hd0 ft0] ori'] tl0 H0; clear H0.
      intros n [[pv0 t0] ori0]; intros.

      induction n as [|n'].
      - simpl in H0; simpl in H1.
        inversion H0; inversion H1; clear H0 H1.
        simpl.
        case Hori : ori0.
        - (* flip *)
        rewrite eq_refl //.
        - rewrite eq_refl //.
      - assert (nth_error ((hd, ft, ori) :: tl) n'.+1 = nth_error tl n').
          specialize nth_error_app2 with (l := [::(hd, ft, ori)])
            (l' := tl) (n := n'.+1); intros.
          rewrite H2; simpl.
          rewrite -Nats.subn_sub subn0 //.
          apply Nats.leq_le; apply ltn0Sn.
        assert (nth_error ((hd0, ft0, ori') :: tl0) n'.+1 = nth_error tl0 n').
          specialize nth_error_app2 with (l := [::(hd0, ft0, ori')])
            (l' := tl0) (n := n'.+1); intros.
          rewrite H3; simpl.
          rewrite -Nats.subn_sub subn0 //.
          apply Nats.leq_le; apply ltn0Sn.
        simpl.
        rewrite H2 in H0; rewrite H3 in H1; clear IHn' H2 H3.
        apply (H _ _ _ _ H0)in H1; simpl in H1.
        assert ((hd == src.1.1) = false) by admit.
        assert ((hd0 == src.1.1) = false) by admit.
        assert ((hd == pv0) = false) by admit.
        assert ((hd0 == pv0) = false) by admit.
        rewrite H2 H3 H4 H5; clear H2 H3 H4 H5.
        case Hori : ori0; rewrite Hori in H1.
        1-2 : case Hori' : ori; try done.
Admitted.

Lemma split_exprs_connect_correct : forall ss ref_tgt expr newtm n t_tgt ori_tgt pv0 gt ori0, type_of_ref ref_tgt newtm = Some (t_tgt, ori_tgt) -> 
  Qin (Sfcnct (Eid ref_tgt) expr) ss -> nth_error (list_gtypref ref_tgt t_tgt ori_tgt) n = Some (pv0, gt, ori0) ->                  
  match expr with
  | Eref (Eid ref_src) => forall t_src ori_src pv1 gte ori1 el, type_of_ref ref_src newtm = Some (t_src, ori_src) -> nth_error (list_gtypref ref_src t_src ori_src) n = Some (pv1, gte, ori1) -> 
                          if ori0 then find_sub_exprs pv1 ss newtm = Some el -> (Eref (Eid pv0)) \in el 
                          else find_sub_exprs pv0 ss newtm = Some el -> (Eref (Eid pv1)) \in el 
  | Eref _ => true
  | _ => forall t_expr texpr rhsl el, type_of_expr expr newtm = Some t_expr -> list_gtypexpr expr t_expr = Some rhsl -> nth_error rhsl n = Some texpr -> find_sub_exprs pv0 ss newtm = Some el -> texpr \in el
  end
with split_expr_connect_correct : forall ref_tgt expr newtm n t_tgt ori_tgt pv0 gt ori0, type_of_ref ref_tgt newtm = Some (t_tgt, ori_tgt) -> 
  nth_error (list_gtypref ref_tgt t_tgt ori_tgt) n = Some (pv0, gt, ori0) ->                  
  match expr with
  | Eref (Eid ref_src) => forall t_src ori_src pv1 gte ori1 el, type_of_ref ref_src newtm = Some (t_src, ori_src) -> nth_error (list_gtypref ref_src t_src ori_src) n = Some (pv1, gte, ori1) -> 
                          if ori0 then find_sub_expr pv1 (Sfcnct (Eid ref_tgt) expr) newtm = Some el -> (Eref (Eid pv0)) \in el 
                          else find_sub_expr pv0 (Sfcnct (Eid ref_tgt) expr) newtm = Some el -> (Eref (Eid pv1)) \in el 
  | Eref _ => true
  | _ => forall t_expr texpr rhsl el, type_of_expr expr newtm = Some t_expr -> list_gtypexpr expr t_expr = Some rhsl -> nth_error rhsl n = Some texpr -> find_sub_expr pv0 (Sfcnct (Eid ref_tgt) expr) newtm = Some el -> texpr \in el
  end.
Proof.
  clear split_exprs_connect_correct.
  elim.
  - (* nil *)
    clear. 
    intros.
    simpl in H0; done.
  - (* cons *)
    intros hd tl IH; intros.
    case Hhd : (hd == Sfcnct (Eid ref_tgt) expr). (* TBD Qin_cons 用来分case *)
    - clear IH H0.
      move /eqP : Hhd => Hhd.
      apply split_expr_connect_correct with (expr := expr) (newtm := newtm) in H1;try done.
      rewrite -Hhd in H1.
  admit.
  admit.

  clear.
  intros.
  case He : expr => [ct c| c e1 | u e1 | op e1 e2 | c e1 e2 | c e1 | ref0 ].
  - (* 一般expr *)
    1-6 : rewrite -He; intros;
    apply find_sub_expr4v_in with (rhsl := rhsl) (texpr := texpr) in H0; try done; simpl in H0;
    rewrite /find_sub_expr He H in H4; rewrite -He H1 H2 H0 in H4; inversion H4;
    rewrite mem_seq1 eq_refl //.
  - (* ref <= ref *)
    case Href : ref0 => [ref_src|||]; try done; intros.
    case Hori : ori0; intros.
    - (* flip *)
      rewrite /find_sub_expr H H1 in H3.
      apply find_sub_non_passive4v_in with (lhsl := (list_gtypref ref_tgt t_tgt ori_tgt)) (tgt := (pv0, gt, ori0)) in H2; try done.
      simpl in H2; rewrite Hori H3 in H2; inversion H2.
      rewrite mem_seq1 eq_refl //.
    - (* nflip *)
      rewrite /find_sub_expr H H1 in H3.
      apply find_sub_non_passive4v_in with (lhsl := (list_gtypref ref_tgt t_tgt ori_tgt)) (tgt := (pv0, gt, ori0)) in H2; try done.
      simpl in H2; rewrite Hori H3 in H2; inversion H2.
      rewrite mem_seq1 eq_refl //.
Admitted.

Lemma find_subs_tmap_eq : forall tmap newtm v ss, (forall c,
  match type_of_ref c tmap, type_of_ref c newtm with
  | Some (t1, _), Some (t2, _) => ftype_equiv t1 t2
  | None, None => true
  | _, _ => false
  end) -> find_sub_exprs v ss newtm = find_sub_exprs v ss tmap
with find_sub_tmap_eq : forall tmap newtm v ss, (forall c,
  match type_of_ref c tmap, type_of_ref c newtm with
  | Some (t1, _), Some (t2, _) => ftype_equiv t1 t2
  | None, None => true
  | _, _ => false
  end) -> find_sub_expr v ss newtm = find_sub_expr v ss tmap.
Proof.
  intros.
Admitted.

(*Lemma infer_find_eq :*)
Lemma infer_type_equiv : forall order var2exprs tmap newtm, InferWidths_fun order var2exprs tmap = Some newtm -> (forall c, 
  match type_of_ref c tmap, type_of_ref c newtm with
  | Some (t1, _), Some (t2, _) => ftype_equiv t1 t2
  | None, None => true
  | _, _ => false
  end).
Proof.
Admitted.

(*Lemma stmts'_find_eq
Lemma stmts'_type_equiv : forall tmap emap newtm s var2exprs, stmts_tmap' tmap emap s = Some (newtm, var2exprs) -> (forall c, 
  match type_of_ref c tmap, type_of_ref c newtm with
  | Some (t1, _), Some (t2, _) => ftype_equiv t1 t2
  | None, None => true
  | _, _ => false
  end)
with stmt'_type_equiv : forall tmap newtm emap s var2exprs, stmts_tmap' tmap emap s = Some (newtm, var2exprs) -> (forall c, 
  match type_of_ref c tmap, type_of_ref c newtm with
  | Some (t1, _), Some (t2, _) => ftype_equiv t1 t2
  | None, None => true
  | _, _ => false
  end).
Proof.
Admitted.*)

Lemma add_expr_connect_findn : forall vl rhsl v var2exprs0 var2exprs, add_expr_connect vl rhsl var2exprs0 = Some var2exprs ->
  match CEP.find v var2exprs0, CEP.find v var2exprs, find_sub_expr4v v vl rhsl with
  | Some el0, Some el, Some el' => TopoSort.subset el (el' ++ el0) /\ TopoSort.subset (el' ++ el0) el
  | None, Some el, Some el' => TopoSort.subset el el' /\ TopoSort.subset el' el
  | _, _, _ => true
  end.

  (*forall vl rstl (var2exprs0 : CEP.t (seq HiFP.hfexpr)), 
  forall v gt ori e, exists n, nth_error vl n = Some (v, gt, ori) -> nth_error rstl n = Some e ->
  match CEP.find v var2exprs0, add_expr_connect vl rstl var2exprs0 with
  | Some el0, Some var2exprs => CEP.find v var2exprs = Some (e :: el0)
  | None, Some var2exprs => CEP.find v var2exprs = Some [:: e]
  | _, _ => true
  end.*)
  (*forall n, match nth_error vl n, nth_error rstl n, add_expr_connect vl rstl var2exprs0 with
  | Some (v, _, _), Some e, Some var2exprs => match CEP.find v var2exprs0 with
                                    | Some el0 => CEP.find v var2exprs = Some (e :: el0)
                                    | None => CEP.find v var2exprs = Some [:: e]
                                    end
  | None, None, Some var2exprs => True
  | _, _, _ => False
  end.*)
Proof.
  elim.
  - (* nil *)
    intros; simpl in H.
    case Hr : rhsl; rewrite Hr in H; try discriminate.
    inversion H; clear H Hr rhsl.
    case Hfind : (CEP.find v var2exprs) => [el|]; try done.
    simpl; split; apply TopoSort.subset_refl.
  - (* cons *)
    intros [[hd gt] ori] tl IH.
    elim.
    - (* nil *)
      intros.
      simpl in H; discriminate.
    - (* cons *)
      intros ehd etl IH'; clear IH'; intros.
      simpl in H.
      case Hfind : (CEP.find hd var2exprs0) => [ls|]; rewrite Hfind in H. 
      - (* hd Some *)
        apply IH with (v := v) in H; clear IH.
        case Heq : (v == hd).
        - (* eq *)
          move /eqP : Heq => Heq. 
          rewrite -Heq in H Hfind; rewrite -Heq; clear Heq hd. 
          rewrite CEP.Lemmas.find_add_eq in H; try apply PVM.SE.eq_refl.
          rewrite Hfind; simpl; rewrite eq_refl.
          assert (find_sub_expr4v v tl etl = Some nil) by admit. (* v = hd, tl中一定没有 *)
          rewrite H0 in H;clear H0.
          case Hfind0 : (CEP.find v var2exprs) => [el|]; try done; rewrite Hfind0 in H.
          move : H => [H H']; split; try done.
        - (* neq *)
          rewrite CEP.Lemmas.find_add_neq in H.
          case Hfind0 : (CEP.find v var2exprs0) => [el0|]; try done; rewrite Hfind0 in H.
          case Hfindv : (CEP.find v var2exprs) => [el|]; try done; rewrite Hfindv in H. 
          simpl; rewrite eq_sym Heq //.
          simpl; rewrite eq_sym Heq //.
          admit.
      - (* hd None *)
        apply IH with (v := v) in H; clear IH.
        case Heq : (v == hd).
        - (* eq *)
          move /eqP : Heq => Heq. 
          rewrite -Heq in H Hfind; rewrite -Heq; clear Heq hd. 
          rewrite CEP.Lemmas.find_add_eq in H; try apply PVM.SE.eq_refl.
          rewrite Hfind; simpl; rewrite eq_refl.
          assert (find_sub_expr4v v tl etl = Some nil) by admit. (* v = hd, tl中一定没有 *)
          rewrite H0 in H;clear H0.
          case Hfind0 : (CEP.find v var2exprs) => [el|]; try done; rewrite Hfind0 in H.
          move : H => [H H']; split; try done.
        - (* neq *)
          rewrite CEP.Lemmas.find_add_neq in H.
          case Hfind0 : (CEP.find v var2exprs0) => [el0|]; try done; rewrite Hfind0 in H.
          case Hfindv : (CEP.find v var2exprs) => [el|]; try done; rewrite Hfindv in H. 
          simpl; rewrite eq_sym Heq //.
          simpl; rewrite eq_sym Heq //.
          admit.
Admitted.

Lemma add_expr_connect_non_passive_findn : forall vl rhsl v var2exprs0 var2exprs, add_expr_connect_non_passive vl rhsl var2exprs0 = Some var2exprs ->
  match CEP.find v var2exprs0, CEP.find v var2exprs, find_sub_non_passive4v v vl rhsl with
  | Some el0, Some el, Some el' => TopoSort.subset el (el' ++ el0) /\ TopoSort.subset (el' ++ el0) el
  | None, Some el, Some el' => TopoSort.subset el el' /\ TopoSort.subset el' el
  | _, _, _ => true
  end.
Proof.
  elim.
  - (* nil *)
    intros; simpl in H.
    case Hr : rhsl; rewrite Hr in H; try discriminate.
    inversion H; clear H Hr rhsl.
    case Hfind : (CEP.find v var2exprs) => [el|]; try done.
    simpl; split; apply TopoSort.subset_refl.
  - (* cons *)
    intros [[hd gt] ori] tl IH.
    elim.
    - (* nil *)
      intros.
      simpl in H. case Hori : ori; rewrite Hori in H; try discriminate.
    - (* cons *)
      intros [[ehd gt'] ori'] etl IH'; clear IH'; intros.
      simpl in H.
      case Hori : ori; rewrite Hori in H.
      - (* flip *)
        admit.
      - (* nflip *)
        case Hfind : (CEP.find hd var2exprs0) => [ls|]; rewrite Hfind in H. 
        - (* hd Some *)
          apply IH with (v := v) in H; clear IH.
          case Heq : (v == hd).
          - (* eq *)
            move /eqP : Heq => Heq. 
            rewrite -Heq in H Hfind; rewrite -Heq; clear Heq hd. 
            rewrite CEP.Lemmas.find_add_eq in H; try apply PVM.SE.eq_refl.
            rewrite Hfind; simpl; rewrite eq_refl.
            assert (find_sub_non_passive4v v tl etl = Some nil) by admit. (* v = hd, tl中一定没有 *)
            rewrite H0 in H;clear H0.
            case Hfind0 : (CEP.find v var2exprs) => [el|]; try done; rewrite Hfind0 in H.
            move : H => [H H']; split; try done.
          - (* neq *)
            rewrite CEP.Lemmas.find_add_neq in H.
            case Hfind0 : (CEP.find v var2exprs0) => [el0|]; try done; rewrite Hfind0 in H.
            case Hfindv : (CEP.find v var2exprs) => [el|]; try done; rewrite Hfindv in H. 
            simpl; rewrite eq_sym Heq //.
            simpl; rewrite eq_sym Heq //.
            admit.
        - (* hd None *)
          apply IH with (v := v) in H; clear IH.
          case Heq : (v == hd).
          - (* eq *)
            move /eqP : Heq => Heq. 
            rewrite -Heq in H Hfind; rewrite -Heq; clear Heq hd. 
            rewrite CEP.Lemmas.find_add_eq in H; try apply PVM.SE.eq_refl.
            rewrite Hfind; simpl; rewrite eq_refl.
            assert (find_sub_non_passive4v v tl etl = Some nil) by admit. (* v = hd, tl中一定没有 *)
            rewrite H0 in H;clear H0.
            case Hfind0 : (CEP.find v var2exprs) => [el|]; try done; rewrite Hfind0 in H.
            move : H => [H H']; split; try done.
          - (* neq *)
            rewrite CEP.Lemmas.find_add_neq in H.
            case Hfind0 : (CEP.find v var2exprs0) => [el0|]; try done; rewrite Hfind0 in H.
            case Hfindv : (CEP.find v var2exprs) => [el|]; try done; rewrite Hfindv in H. 
            simpl; rewrite eq_sym Heq //.
            simpl; rewrite eq_sym Heq //.
            admit.
Admitted.

Lemma find_sub_expr_eq : forall s tmap0 tmap var2exprs0 var2exprs, stmt_tmap' tmap0 var2exprs0 s = Some (tmap, var2exprs) ->
  forall (v : ProdVarOrder.t), match CEP.find v var2exprs0, CEP.find v var2exprs, find_sub_expr v s tmap with
  | Some el0, Some el, Some el' => TopoSort.subset el (el' ++ el0) /\ TopoSort.subset (el' ++ el0) el
  | None, Some el, Some el' => TopoSort.subset el el' /\ TopoSort.subset el' el
  | _,_, _ => true
  end
with find_sub_exprs_eq : forall ss tmap0 tmap var2exprs0 var2exprs, stmts_tmap' tmap0 var2exprs0 ss = Some (tmap, var2exprs) ->
  forall (v : ProdVarOrder.t), match CEP.find v var2exprs0, CEP.find v var2exprs, find_sub_exprs v ss tmap with
  | Some el0, Some el, Some el' => TopoSort.subset el (el' ++ el0) /\ TopoSort.subset (el' ++ el0) el
  | None, Some el, Some el' => TopoSort.subset el el' /\ TopoSort.subset el' el
  | _,_, _ => true
  end.
Proof.
  clear find_sub_expr_eq.
  intros.
  case Hs : s => [|r t|r reg|r m||r e|r e|r|c s1 s2]; rewrite Hs in H; simpl in H; simpl.
  - (* skip *)
    inversion H;
    case Hfind : (CEP.find v var2exprs) => [el0|]; try done;
    split; apply TopoSort.subset_refl.
  - (* wire *)
    case Hr : (CEP.find r tmap0); rewrite Hr in H; try discriminate.
    inversion H.
    case Hfind : (CEP.find v var2exprs) => [el0|]; try done.
    split; apply TopoSort.subset_refl.
  - 2,3 : discriminate.
  - 4 : case Href : r => [ref|||]; rewrite Href in H; try discriminate;
    case Hr : (type_of_ref ref tmap0); rewrite Hr in H; try discriminate;
    inversion H;
    case Hfind : (CEP.find v var2exprs) => [el0|]; try done;
    split; apply TopoSort.subset_refl.
  - (* reg *)
    clear find_sub_exprs_eq.
    case Hr : (CEP.find r tmap0); rewrite Hr in H; try discriminate.
    case Ht : (type_of_expr (clock reg) tmap0); rewrite Ht in H; clear Ht; try discriminate.
    case Hrst : (reset reg) => [|rst_sig rst_val]; rewrite Hrst in H.
    - (* nrst *)
      inversion H; clear H H2 var2exprs0.
      case Hfind : (CEP.find v var2exprs) => [el0|]; try done.
      split; apply TopoSort.subset_refl.
    - (* rst *)
      case He : (type_of_expr rst_sig tmap0); rewrite He in H; try discriminate; clear He.
      case He : (type_of_expr rst_val tmap0) => [ft_src|]; rewrite He in H; try discriminate.
      case Hsplit : (list_gtypexpr rst_val ft_src) => [rstl|]; rewrite Hsplit in H; try discriminate.
      case Hadd : (add_expr_connect (list_gtypref r (type reg) false) rstl var2exprs0) => [emap'|]; rewrite Hadd in H; try discriminate.
      inversion H; clear H; rewrite H1 in He Hr; clear H1 tmap0; rewrite H2 in Hadd; clear H2 emap'. 
      apply add_expr_connect_findn with (v := v) in Hadd; try done.
      rewrite (ftype_equiv_split_eq _ _ ft_src). rewrite Hsplit. done.
      admit.
  - (* node *)
    clear find_sub_exprs_eq.
    case Hr : (CEP.find r tmap0); rewrite Hr in H; try discriminate.
    case Hte : (type_of_expr e tmap0) => [te|]; rewrite Hte in H; try discriminate.
    case Hsplit : (list_gtypexpr e te) => [rstl|]; rewrite Hsplit in H; try discriminate.
    case Hadd : (add_expr_connect (list_gtypref r te false) rstl var2exprs0) => [emap'|]; rewrite Hadd in H; try discriminate.
    inversion H; clear H. clear H1 tmap. rewrite H2 in Hadd; clear H2 emap'. 
    apply add_expr_connect_findn with (v := v) in Hadd; try done.
    assert (type_of_expr e (CEP.add r (te, HiF.Source) tmap0) = Some te) by admit. (* 不影响e *)
    rewrite H Hsplit; clear H. done.
  - (* fcnct *)
    clear find_sub_exprs_eq.
    case He : e =>[t c| c e1 | u e1 | op e1 e2 | c e1 e2 | c e1 | r2 ]; rewrite He in H; try done.
    - (* 一般connection *)
      1-6 : rewrite -He; rewrite -He in H;
      case Hr : r => [ref_tgt|||]; rewrite Hr in H Hs; try discriminate; clear Hr r;
      case Hbase : (type_of_ref ref_tgt tmap0) => [[t_tgt ori_tgt]|]; rewrite Hbase in H; try discriminate;
      case Hte : (type_of_expr e tmap0) => [t_src|]; rewrite Hte in H; try discriminate;
      case Hsplit : (list_gtypexpr e t_src) => [rstl|]; rewrite Hsplit in H; try discriminate;
      case Hadd : (add_expr_connect (list_gtypref ref_tgt t_tgt ori_tgt) rstl var2exprs0) => [emap'|]; rewrite Hadd in H; try discriminate;
      inversion H; clear H; rewrite H2 in Hadd; clear H2 emap'; rewrite H1 in Hte Hbase; clear H1 tmap0;
      rewrite Hbase Hte Hsplit;
      apply add_expr_connect_findn with (v := v) in Hadd; try done.
    - (* Eref connection *)
      case Hr : r => [ref_tgt|||]; rewrite Hr in H Hs; try discriminate; clear Hr r.
      case Hr2 : r2 => [ref_src|||]; rewrite Hr2 in H He; try discriminate; rewrite He in Hs; clear Hr2 r2 He e.
      case Hbase : (type_of_ref ref_tgt tmap0) => [[t_tgt ori_tgt]|]; rewrite Hbase in H; try discriminate.
      case Hbase2 : (type_of_ref ref_src tmap0) => [[t_src ori_src]|]; rewrite Hbase2 in H; try discriminate.
      case Hadd : (add_expr_connect_non_passive (list_gtypref ref_tgt t_tgt ori_tgt)
        (list_gtypref ref_src t_src ori_src) var2exprs0) => [emap'|]; rewrite Hadd in H; try discriminate.
      inversion H; clear H. rewrite H2 in Hadd; clear H2 emap'. rewrite H1 in Hbase Hbase2; clear H1 tmap0.
      rewrite Hbase Hbase2.
      apply add_expr_connect_non_passive_findn with (v := v) in Hadd; try done.
    - (* when *)
      case Hc : (type_of_expr c tmap0); rewrite Hc in H; try discriminate; clear Hc. 
      case Hstmts : (stmts_tmap' tmap0 var2exprs0 s1) => [[tmap_true emap_true]|]; rewrite Hstmts in H; try discriminate.
      generalize H; apply find_sub_exprs_eq with (v := v) in Hstmts; apply find_sub_exprs_eq with (v := v) in H; clear find_sub_exprs_eq.
      case Hfind0 : (CEP.find v var2exprs0) => [el0|]; rewrite Hfind0 in Hstmts; try done.
      - (* some v *)
        case Hfind : (CEP.find v var2exprs) => [el|]; rewrite Hfind in H; try done.
        case Hfindt : (CEP.find v emap_true) => [elt|]; rewrite Hfindt in H Hstmts.
        - (* define v in true *)
          intros H'. 
          (*specialize (stmts'_type_equiv _ _ _ _ _ H'); intros.
          apply find_subs_tmap_eq with (v := v) (ss := s1) in H0.
          rewrite -H0 in Hstmts; clear H0.
          case Hfind1 : (find_sub_exprs v s1 tmap) => [e1|]; rewrite Hfind1 in Hstmts; try done.
          case Hfind2 : (find_sub_exprs v s2 tmap) => [e2|]; rewrite Hfind2 in H; try done.*)
          admit. (* TBD *)
        - (* no v in true *)
          intros H'.
          case Hfind1 : (find_sub_exprs v s1 tmap) => [e1|]; try done.
          case Hfind2 : (find_sub_exprs v s2 tmap) => [e2|]; rewrite Hfind2 in H; try done.
          admit. (* TBD *)
      - (* none *)
        intros H'.
        case Hfind : (CEP.find v var2exprs) => [el|]; rewrite Hfind in H; try done.
        case Hfindt : (CEP.find v emap_true) => [elt|]; rewrite Hfindt in H Hstmts.
        - (* define v in true *)
          (*specialize (stmts'_type_equiv _ _ _ _ _ H'); intros.
          apply find_subs_tmap_eq with (v := v) (ss := s1) in H0.
          rewrite -H0 in Hstmts; clear H0.
          case Hfind1 : (find_sub_exprs v s1 tmap) => [e1|]; rewrite Hfind1 in Hstmts; try done.
          case Hfind2 : (find_sub_exprs v s2 tmap) => [e2|]; rewrite Hfind2 in H; try done.*)
          admit. (* TBD *)
        - (* no v in true *)
          assert (find_sub_exprs v s1 tmap = Some nil) by admit. (* 由Hfindt，v在s1没有被定义，一定是nil *)
          rewrite H0; clear H0; simpl.
          case Hfind2 : (find_sub_exprs v s2 tmap) => [e2|]; rewrite Hfind2 in H; try done.

  clear find_sub_exprs_eq.
  elim.
  - (* nil *)
    intros; simpl in H.
    inversion H; clear H H1 tmap0 H2 var2exprs0. 
    simpl.
    case Hfind : (CEP.find v var2exprs); try done; try split; try apply TopoSort.subset_refl.
  - (* cons *)
    intros hd tl IH; intros.
    simpl in H. 
    case Hstmts : (stmt_tmap' tmap0 var2exprs0 hd) => [[tmap' emap']|]; rewrite Hstmts in H; try discriminate.
    generalize H; generalize Hstmts; apply find_sub_expr_eq with (v := v) in Hstmts; apply IH with (v := v) in H; clear find_sub_expr_eq IH; intros Hstmts'.
    intros H'; case Hfind0 : (CEP.find v var2exprs0) => [el0|]; rewrite Hfind0 in Hstmts.
    - (* find some *)
      case Hfind : (CEP.find v var2exprs) => [el|]; rewrite Hfind in H; try done.
      simpl.
      case Hhd : (find_sub_expr v hd tmap) => [e|]; try done.
      case Htl : (find_sub_exprs v tl tmap) => [el1|]; rewrite Htl in H; try done.
      assert (Hfindt : exists elt, CEP.find v emap' = Some elt) by admit. (* Hstmts' Hfind0 *)
      destruct Hfindt as [elt Hfindt]; rewrite Hfindt in H Hstmts.
      (*specialize (stmts'_type_equiv _ _ _ _ _ H'); intros.
      apply find_sub_tmap_eq with (v := v) (ss := hd) in H0.
      rewrite -H0 Hhd in Hstmts; clear H0.*)
      admit.
    - (* find none *)
      case Hfind : (CEP.find v var2exprs) => [el|]; rewrite Hfind in H; try done.
      simpl.
      case Hhd : (find_sub_expr v hd tmap) => [e|]; try done.
      case Htl : (find_sub_exprs v tl tmap) => [el1|]; rewrite Htl in H; try done.
      case Hfindt : (CEP.find v emap') => [elt|]; rewrite Hfindt in H Hstmts. (* Hstmts' Hfind0 *)
      - (*specialize (stmts'_type_equiv _ _ _ _ _ H'); intros.
        apply find_sub_tmap_eq with (v := v) (ss := hd) in H0.
        rewrite -H0 Hhd in Hstmts; clear H0.*)
        admit.
      - (*specialize (stmts'_type_equiv _ _ _ _ _ H'); intros.
        apply find_sub_tmap_eq with (v := v) (ss := hd) in H0.
        rewrite H0 in Hhd; clear H0.
        assert (e = nil) by admit. (* Hstmt' hfindt Hhd *)
        rewrite H0; simpl; done.*)
Admitted.

Lemma find_sub_exprs_correct : forall v ps ss tmap var2exprs el el', ports_stmts_tmap' ps ss = Some (tmap, var2exprs) -> CEP.find v var2exprs = Some el -> find_sub_exprs v ss tmap = Some el' -> TopoSort.subset el el' /\ TopoSort.subset el' el.
Proof. 
  intros.
  rewrite /ports_stmts_tmap' in H.
  case Hp : (ports_tmap' ps) => [pmap|]; rewrite Hp in H; try discriminate.
  apply find_sub_exprs_eq with (v := v) in H.
  rewrite HiFP.PCELemmas.empty_o in H.
  rewrite H1 H0 in H. 
  case Hel : el'; rewrite Hel in H; done.
Qed.

Lemma preexpr_in: forall ps ss tmap newtm var2exprs ref_tgt t_tgt ori_tgt n pv0 gt ori0 expr inferorder, ports_stmts_tmap' ps ss = Some (tmap, var2exprs) -> InferWidths_fun inferorder var2exprs tmap = Some newtm -> 
  type_of_ref ref_tgt newtm = Some (t_tgt, ori_tgt) -> Qin (Sfcnct (Eid ref_tgt) expr) ss -> nth_error (list_gtypref ref_tgt t_tgt ori_tgt) n = Some (pv0, gt, ori0) -> 
  match expr with
  | Eref (Eid ref_src) => forall t_src ori_src pv1 gte ori1 el, type_of_ref ref_src newtm = Some (t_src, ori_src) -> nth_error (list_gtypref ref_src t_src ori_src) n = Some (pv1, gte, ori1) -> 
                          if ori0 then CEP.find pv1 var2exprs = Some el -> (Eref (Eid pv0)) \in el 
                            else CEP.find pv0 var2exprs = Some el -> (Eref (Eid pv1)) \in el 
  | Eref _ => true
  | _ => forall texpr t_expr rhs_expr_ls el, CEP.find pv0 var2exprs = Some el -> type_of_expr expr newtm = Some t_expr -> list_gtypexpr expr t_expr = Some rhs_expr_ls -> nth_error rhs_expr_ls n = Some texpr -> texpr \in el
  end.
Proof.
  intros.
  case He : expr => [ct c| c e1 | u e1 | op e1 e2 | c e1 e2 | c e1 | ref0 ]; try done.
  1-6 : rewrite -He; intros;
    generalize H; assert (exists el', find_sub_exprs pv0 ss tmap = Some el') by admit; destruct H8 as [el' H8];
    apply find_sub_exprs_correct with (el := el) (el' := el') (v := pv0) in H; try done;
    specialize (infer_type_equiv _ _ _ _ H0); intros H9 H';
    apply find_subs_tmap_eq with (v := pv0) (ss := ss) in H9;
    rewrite -H9 in H8;
    move : H => [_ H]; apply TopoSort.in_subset_trans with (s := el'); try done;
    apply split_exprs_connect_correct with (ss := ss) (expr := expr) (newtm := newtm) in H3; try done;
    rewrite He in H3; rewrite -He in H3;
    apply H3 with (t_expr := t_expr) (texpr := texpr) (rhsl := rhs_expr_ls) in H8; try done.
  case Hr : ref0 => [ref_src|||]; try done.
  intros.
  case Hori : ori0; intros.
    generalize H. assert (exists el', find_sub_exprs pv1 ss tmap = Some el') by admit. destruct H7 as [el' H8].
    apply find_sub_exprs_correct with (el := el) (el' := el') (v := pv1) in H; try done.
    specialize (infer_type_equiv _ _ _ _ H0); intros H9 H';
    apply find_subs_tmap_eq with (v := pv1) (ss := ss) in H9.
    rewrite -H9 in H8;
    move : H => [_ H]; apply TopoSort.in_subset_trans with (s := el'); try done.
    apply split_exprs_connect_correct with (ss := ss) (expr := expr) (newtm := newtm) in H3; try done.
    rewrite He Hr in H3. apply H3 with (el := el') in H5; try done; rewrite Hori in H5; apply H5; try done.

    generalize H. assert (exists el', find_sub_exprs pv0 ss tmap = Some el') by admit. destruct H7 as [el' H8].
    apply find_sub_exprs_correct with (el := el) (el' := el') (v := pv0) in H; try done.
    specialize (infer_type_equiv _ _ _ _ H0); intros H9 H';
    apply find_subs_tmap_eq with (v := pv0) (ss := ss) in H9.
    rewrite -H9 in H8;
    move : H => [_ H]; apply TopoSort.in_subset_trans with (s := el'); try done.
    apply split_exprs_connect_correct with (ss := ss) (expr := expr) (newtm := newtm) in H3; try done.
    rewrite He Hr in H3. apply H3 with (el := el') in H5; try done; rewrite Hori in H5; apply H5; try done.
Admitted.

Lemma InferWidths_fun_correct : forall pp ss (inferorder : seq ProdVarOrder.t) (var2exprs : CEP.t (seq HiFP.hfexpr)) (tmap0 newtm : CEP.t (ftype * HiF.forient)),
  InferWidths_fun inferorder var2exprs tmap0 = Some newtm -> ports_stmts_tmap' pp ss = Some (tmap0, var2exprs) -> 
  (forall (hfs : HiFP.hfstmt), Qin hfs ss -> match hfs with
    | Sfcnct (Eid ref_tgt) (Eref (Eid ref_src)) => match type_of_ref ref_tgt newtm, type_of_ref ref_src newtm with
                                      | Some (t_tgt, ori_tgt), Some (t_src, ori_src) => ftype_equiv t_tgt t_src -> connect_non_passive_type ref_tgt ref_src t_tgt t_src ori_tgt ori_src
                                      | _, _ => True
                                      end 
    | Sfcnct (Eid ref_tgt) (Eref _) => True
    | Sfcnct (Eid ref_tgt) expr_src => match type_of_ref ref_tgt newtm, type_of_expr expr_src newtm with
                                      | Some (t_tgt, ori), Some t_expr => ftype_equiv t_tgt t_expr -> connect_type ref_tgt t_tgt t_expr
                                      | _, _ => True
                                      end
    | _ => True
    end).
Proof. 
  intros ps ss inferorder var2exprs tmap newtm Hinfer Hpre hfs Hin.
  case Hs : hfs => [||||||ref expr||]; try done.
  case He : expr => [ct c| c e1 | u e1 | op e1 e2 | c e1 e2 | c e1 | ref0 ]; try done. 
  (* const *)
  1,2,3,4,5,6 : rewrite -He; rewrite Hs in Hin; clear Hs hfs;
                case Href : ref => [ref_tgt|||]; try done;
                case Htr : (type_of_ref ref_tgt newtm) => [[t_tgt ori]|]; try done;
                case Hte : (type_of_expr expr newtm) => [t_expr|] ; try done; intro Heq;
                rewrite /connect_type;
                apply rwP with (P := ftype_equiv t_tgt t_expr /\
    check_connect_type (list_gtypref ref_tgt t_tgt false)
    (list_gtypref (0%num, 0%num) t_expr false)).
  1,3,5,7,9,11 : apply andP.
  1,2,3,4,5,6 : split. 
  1,3,5,7,9,11 : apply Heq. (* hypo *)
  apply check_connect_type_correct with (ft := list_gtypref ref_tgt t_tgt false) (te := list_gtypref (0%num, 0%num) t_expr false).
  intros n.
  case Hlhs : (nth_error (list_gtypref ref_tgt t_tgt false) n) => [[[pv0 gt] ori0]|].
  case Hrhs : (nth_error (list_gtypref (0%num, 0%num) t_expr false) n) => [[[pv1 gte] ori1]|]; try done.
  rewrite /connect_fgtyp_compatible.
  apply rwP with (P := fgtyp_equiv gt gte /\
    (if not_implicit gt
    then true
    else sizeof_fgtyp gte <= sizeof_fgtyp gt)).
  apply andP.
  split. 
  move : Heq Hlhs Hrhs; apply listgtyp_eq.
  case Himpli : (not_implicit gt); try done.

  assert (exists order1 order2, (inferorder = order1 ++ (pv0 :: order2)) /\ (pv0 \notin order1) 
    /\ (pv0 \notin order2)).
  admit. (* inferorder 的正确性，是展开时的标号 *)
  move : H => [order1 [order2 [H [Horder1 Horder2]]]].
  generalize Hinfer; rewrite H in Hinfer; move => Hinfer'.
  case Hinfer1 : (InferWidths_fun order1 var2exprs tmap) => [tmap'|].
  assert (Hinfer2 : InferWidths_fun (pv0 :: order2) var2exprs tmap' = Some newtm).
  move : Hinfer Hinfer1.
  apply infer_cons_order.
  clear Hinfer.
  simpl in Hinfer2.
  case Hel : (CEP.find pv0 var2exprs) => [el|]; rewrite Hel in Hinfer2; try done.
  case Hinfer : (InferWidth_fun pv0 el tmap') => [newtm'|]; rewrite Hinfer in Hinfer2; try discriminate.
  case Hsplit : (list_gtypexpr expr t_expr) => [rhs_expr_ls|].

  (*generalize Hte; apply split_expr_type_correct with (rhs_expr_ls := rhs_expr_ls) (n := n) in Hte; try done; rewrite Hrhs in Hte; intro Hte'.
  case Htexpr : (nth_error rhs_expr_ls n) => [texpr|]; rewrite Htexpr in Hte.*)

  specialize split_expr_type_correct with (expr := expr); intro H0; rewrite He in H0; rewrite -He in H0.
  generalize Hte; apply H0 with (rhs_expr_ls := rhs_expr_ls) (n := n) in Hte; try done; rewrite Hrhs in Hte; intro Hte'; clear H0.
  case Htexpr : (nth_error rhs_expr_ls n) => [texpr|]; rewrite Htexpr in Hte.
  assert (Hin' : texpr \in el).
  rewrite Href in Hin.
  apply preexpr_in with (inferorder := inferorder) (ps := ps) (ss := ss) (tmap := tmap) (newtm := newtm) (var2exprs := var2exprs) (expr := expr) in Hlhs; try done.
  rewrite He in Hlhs; rewrite -He in Hlhs; move : Hel Hte' Hsplit Htexpr; apply Hlhs.
  admit. (* 一般expr一定是passive *)
  apply InferWidth_fun_correct with (pv := pv0) (el := el) (tmap := tmap') (newtm := newtm') (expr := texpr) in Hinfer; try done.
  generalize Htr; rewrite /type_of_ref in Htr; case Hcheckt : (CEP.find (ref_tgt.1, 0%num) newtm) => [[checkt ori_c]|]; rewrite Hcheckt in Htr; try discriminate; intro Htr'.
  generalize Hlhs; apply nth_error_In in Hlhs; apply list_fsteq in Hlhs; simpl in Hlhs.
  intro Hlhs'; generalize Hlhs'; apply list_gtypref_correct with (tmap := newtm) in Hlhs'; try done.
  intro Hlhs0; rewrite /type_of_ref -Hlhs in Hlhs'. rewrite -Hlhs in Hinfer.
  assert (exists checkt' ori_c', CEP.find (ref_tgt.1, 0%num) newtm' = Some (checkt', ori_c')).
  admit. (* 由 Hcheckt *)
  destruct H0 as [checkt' [ori_c' Htgt0]]; rewrite Htgt0 in Hinfer; rewrite Hcheckt in Hlhs'.
  assert (exists nt ori', ft_find_sub checkt' pv0.2 false = Some (nt, ori')).
  admit. (* 由 Hlhs' *)
  destruct H0 as [nt [ori' Hsub0]]; rewrite Hsub0 in Hinfer.
  apply infernotin_eq with (var2exprs := var2exprs) (tmap := newtm') (newtm := newtm) in Horder2; try done.
  rewrite /type_of_ref -Hlhs Htgt0 Hcheckt in Horder2; rewrite Horder2 in Hlhs'; rewrite Hlhs' in Hsub0; inversion Hsub0; clear Hsub0.
  rewrite -H1 in Hinfer; clear H1 nt H2 ori'.
  assert (Hvl : exists vl, expr2varlist texpr = Some vl) by admit.
  destruct Hvl as [vl Hvl].
  apply type_of_expr_eqs with (expr := texpr) (vl := vl) in Hinfer2; try done. rewrite Hinfer2 Hte in Hinfer; clear Hinfer2.
  assert (fgtyp_equiv gt gte).
  move : Heq Hlhs0 Hrhs; apply listgtyp_eq.
  apply Hinfer in H0; clear Hinfer; rewrite /connect_fgtyp_compatible in H0.
  move /andP : H0 => [_ H0]; rewrite Himpli in H0; done.
  admit. (* Topo的性质 *)
  admit. (* 一般expr一定是passive *)
  admit. (* 不是None *)
  admit. (* 不是None *)
  admit. (* 不是None *)
  admit. (* 不是None *)
  admit. (* 不是None *)

  admit.
  admit.
  admit.
  admit.
  admit. (* 5个相同case *)

  (* non_passive *)
  rewrite He in Hs; rewrite Hs in Hin; clear Hs hfs.
  case Href : ref => [ref_tgt|||]; rewrite Href in Hin; try done.
  case Href0 : ref0 => [ref_src|||]; rewrite Href0 in Hin; clear Href; try done.
  case Htgt : (type_of_ref ref_tgt newtm) => [[t_tgt ori_tgt]|]; try done.
  case Hsrc : (type_of_ref ref_src newtm) => [[t_src ori_src]|]; try done; intro Heq.
  rewrite /connect_non_passive_type.
  apply rwP with (P := ftype_equiv t_tgt t_src /\ check_connect_non_passive_type (list_gtypref ref_tgt t_tgt ori_tgt) (list_gtypref ref_src t_src ori_src)).
  apply andP.
  split; try done. 
  apply check_connect_non_passive_type_correct.
  intro n.
  case Hlhs : (nth_error (list_gtypref ref_tgt t_tgt ori_tgt) n) => [[[pv_tgt gt_tgt] ori_tgt0]|].
  case Hrhs : (nth_error (list_gtypref ref_src t_src ori_src) n) => [[[pv_src gt_src] ori_src0]|].
  case Hflip : (ori_tgt0).
  - (* flip *)
    rewrite /connect_fgtyp_compatible.
    apply rwP with (P := fgtyp_equiv gt_src gt_tgt /\
      (if not_implicit gt_src
      then true
      else sizeof_fgtyp gt_tgt <= sizeof_fgtyp gt_src)).
    apply andP.
    split. 
    apply fgtyp_equiv_comm; move : Heq Hlhs Hrhs; apply listgtyp_eq.
    case Himpli : (not_implicit gt_src); try done.
    assert (exists order1 order2, (inferorder = order1 ++ (pv_src :: order2)) /\ (pv_src \notin order1) 
      /\ (pv_src \notin order2)).
    admit. (* inferorder 的正确性，是展开时的标号 *)
    move : H => [order1 [order2 [H [Horder1 Horder2]]]].
    generalize Hinfer; rewrite H in Hinfer; move => Hinfer'.
    case Hinfer1 : (InferWidths_fun order1 var2exprs tmap) => [tmap'|].
    assert (Hinfer2 : InferWidths_fun (pv_src :: order2) var2exprs tmap' = Some newtm).
    move : Hinfer Hinfer1.
    apply infer_cons_order.
    clear Hinfer.
    simpl in Hinfer2.
    case Hel : (CEP.find pv_src var2exprs) => [el|]; rewrite Hel in Hinfer2; try done.
    case Hinfer : (InferWidth_fun pv_src el tmap') => [newtm'|]; rewrite Hinfer in Hinfer2; try discriminate.
    assert (Hin' : (Eref (Eid pv_tgt)) \in el).
    apply preexpr_in with (inferorder := inferorder) (ps := ps) (ss := ss) (tmap := tmap) (newtm := newtm) (var2exprs := var2exprs) (expr := expr) in Hlhs; try done.
    rewrite He Href0 in Hlhs; apply Hlhs with (pv1 := pv_src) (gte := gt_src) (ori1 := ori_src0) (el := el) in Hsrc; try done; clear Hlhs. 
    rewrite Hflip in Hsrc; apply Hsrc in Hel; clear Hsrc; done.
    rewrite He Href0 //.
    apply InferWidth_fun_correct with (pv := pv_src) (el := el) (tmap := tmap') (newtm := newtm') (expr := Eref (Eid pv_tgt)) in Hinfer; try done.
    generalize Hsrc; rewrite /type_of_ref in Hsrc; case Hcheckt : (CEP.find (ref_src.1, 0%num) newtm) => [[checkt ori_c]|]; rewrite Hcheckt in Hsrc; try discriminate; intro Hsrc'.
    generalize Hrhs; apply nth_error_In in Hrhs; apply list_fsteq in Hrhs; simpl in Hrhs.
    intro Hrhs'; generalize Hrhs'; apply list_gtypref_correct with (tmap := newtm) in Hrhs'; try done.
    intro Hrhs0; rewrite /type_of_ref -Hrhs in Hrhs'. rewrite -Hrhs in Hinfer.
    assert (exists checkt' ori_c', CEP.find (ref_src.1, 0%num) newtm' = Some (checkt', ori_c')).
    admit. (* 由 Hcheckt *)
    destruct H0 as [checkt' [ori_c' Hsrc0]]; rewrite Hsrc0 in Hinfer; rewrite Hcheckt in Hrhs'.
    assert (exists nt ori', ft_find_sub checkt' pv_src.2 false = Some (nt, ori')).
    admit. (* 由 Hrhs' *)
    destruct H0 as [nt [ori' Hsub0]]; rewrite Hsub0 in Hinfer.
    apply infernotin_eq with (var2exprs := var2exprs) (tmap := newtm') (newtm := newtm) in Horder2; try done.
    rewrite /type_of_ref -Hrhs Hcheckt Hrhs' Hsrc0 in Horder2; rewrite -Horder2 in Hsub0; inversion Hsub0; clear Hsub0.
    rewrite -H1 in Hinfer; clear H1 nt H2 ori'.
    assert (Hvl : exists vl, expr2varlist (Eref (Eid pv_tgt)) = Some vl) by (simpl; exists [:: pv_tgt]; done).
    destruct Hvl as [vl Hvl].
    apply type_of_expr_eqs with (expr := (Eref (Eid pv_tgt))) (vl := vl) in Hinfer2; try done. rewrite Hinfer2 in Hinfer; clear Hinfer2.
    simpl in Hinfer.
    generalize Htgt; rewrite /type_of_ref in Htgt; case Hcheckt0 : (CEP.find (ref_tgt.1, 0%num) newtm) => [[checkt0 ori_c0]|]; rewrite Hcheckt0 in Htgt; try discriminate; intro Htgt'.
    generalize Hlhs; apply nth_error_In in Hlhs; apply list_fsteq in Hlhs; simpl in Hlhs.
    intro Hlhs'; generalize Hlhs'; apply list_gtypref_correct with (tmap := newtm) in Hlhs'; try done; rewrite Hlhs' in Hinfer; intro Hlhs0.
    assert (fgtyp_equiv gt_src gt_tgt).
    apply ftype_equiv_comm in Heq; move : Heq Hrhs0 Hlhs0; apply listgtyp_eq.
    apply Hinfer in H0; clear Hinfer; rewrite /connect_fgtyp_compatible in H0.
    move /andP : H0 => [_ H0]; rewrite Himpli in H0; done.
    admit. (* Topo性质 *)
    admit. (* 不是None *)
  - (* nflip *)
    rewrite /connect_fgtyp_compatible.
    apply rwP with (P := fgtyp_equiv gt_tgt gt_src /\
      (if not_implicit gt_tgt
      then true
      else sizeof_fgtyp gt_src <= sizeof_fgtyp gt_tgt)).
    apply andP.
    split. 
    move : Heq Hlhs Hrhs; apply listgtyp_eq.
    case Himpli : (not_implicit gt_tgt); try done.
    assert (exists order1 order2, (inferorder = order1 ++ (pv_tgt :: order2)) /\ (pv_tgt \notin order1) 
      /\ (pv_tgt \notin order2)).
    admit. (* inferorder 的正确性，是展开时的标号 *)
    move : H => [order1 [order2 [H [Horder1 Horder2]]]].
    generalize Hinfer; rewrite H in Hinfer; move => Hinfer'.
    case Hinfer1 : (InferWidths_fun order1 var2exprs tmap) => [tmap'|].
    assert (Hinfer2 : InferWidths_fun (pv_tgt :: order2) var2exprs tmap' = Some newtm).
    move : Hinfer Hinfer1.
    apply infer_cons_order.
    clear Hinfer.
    simpl in Hinfer2.
    case Hel : (CEP.find pv_tgt var2exprs) => [el|]; rewrite Hel in Hinfer2; try done.
    case Hinfer : (InferWidth_fun pv_tgt el tmap') => [newtm'|]; rewrite Hinfer in Hinfer2; try discriminate.
    assert (Hin' : (Eref (Eid pv_src)) \in el).
    apply preexpr_in with (inferorder := inferorder) (ps := ps) (ss := ss) (tmap := tmap) (newtm := newtm) (var2exprs := var2exprs) (expr := expr) in Hlhs; try done.
    rewrite He Href0 in Hlhs; apply Hlhs with (pv1 := pv_src) (gte := gt_src) (ori1 := ori_src0) (el := el) in Hsrc; try done; clear Hlhs. 
    rewrite Hflip in Hsrc; apply Hsrc in Hel; clear Hsrc; done.
    rewrite He Href0 //.
    apply InferWidth_fun_correct with (pv := pv_tgt) (el := el) (tmap := tmap') (newtm := newtm') (expr := Eref (Eid pv_src)) in Hinfer; try done.
    generalize Htgt; rewrite /type_of_ref in Htgt; case Hcheckt0 : (CEP.find (ref_tgt.1, 0%num) newtm) => [[checkt0 ori_c0]|]; rewrite Hcheckt0 in Htgt; try discriminate; intro Htgt'.
    generalize Hlhs; apply nth_error_In in Hlhs; apply list_fsteq in Hlhs; simpl in Hlhs.
    intro Hlhs'; generalize Hlhs'; apply list_gtypref_correct with (tmap := newtm) in Hlhs'; try done.
    intro Hlhs0; rewrite /type_of_ref -Hlhs in Hlhs'. rewrite -Hlhs in Hinfer.
    assert (exists checkt' ori_c', CEP.find (ref_tgt.1, 0%num) newtm' = Some (checkt', ori_c')).
    admit. (* 由 Hcheckt0 *)
    destruct H0 as [checkt' [ori_c' Htgt0]]; rewrite Htgt0 in Hinfer; rewrite Hcheckt0 in Hlhs'.
    assert (exists nt ori', ft_find_sub checkt' pv_tgt.2 false = Some (nt, ori')).
    admit. (* 由 Hrhs' *)
    destruct H0 as [nt [ori' Hsub0]]; rewrite Hsub0 in Hinfer.
    apply infernotin_eq with (var2exprs := var2exprs) (tmap := newtm') (newtm := newtm) in Horder2; try done.
    rewrite /type_of_ref -Hlhs Hcheckt0 Hlhs' Htgt0 in Horder2; rewrite -Horder2 in Hsub0; inversion Hsub0; clear Hsub0.
    rewrite -H1 in Hinfer; clear H1 nt H2 ori'.
    assert (Hvl : exists vl, expr2varlist (Eref (Eid pv_src)) = Some vl) by (simpl; exists [:: pv_src]; done).
    destruct Hvl as [vl Hvl].
    apply type_of_expr_eqs with (expr := (Eref (Eid pv_src))) (vl := vl) in Hinfer2; try done. rewrite Hinfer2 in Hinfer; clear Hinfer2.
    simpl in Hinfer.
    generalize Hsrc; rewrite /type_of_ref in Hsrc; case Hcheckt : (CEP.find (ref_src.1, 0%num) newtm) => [[checkt ori_c]|]; rewrite Hcheckt in Hsrc; try discriminate; intro Hsrc'.
    generalize Hrhs; apply nth_error_In in Hrhs; apply list_fsteq in Hrhs; simpl in Hrhs.
    intro Hrhs'; generalize Hrhs'; apply list_gtypref_correct with (tmap := newtm) in Hrhs'; try done.
    rewrite Hrhs' in Hinfer; intro Hrhs0.
    assert (fgtyp_equiv gt_tgt gt_src).
    move : Heq Hlhs0 Hrhs0; apply listgtyp_eq.
    apply Hinfer in H0; clear Hinfer; rewrite /connect_fgtyp_compatible in H0.
    move /andP : H0 => [_ H0]; rewrite Himpli in H0; done.
    admit. (* Topo性质 *)
    admit. (* 不是None *)
    admit. (* 不是None *)
  case Hrhs : (nth_error (list_gtypref ref_src t_src ori_src) n); try done.
Admitted.

Lemma InferWidths_trans_correct : forall pp ss nps nss newtm vm' vm'' vm (*pv*), (*InferWidths_stage1 (FInmod pv pp ss) = Some newtm ->*) InferWidths_transps pp newtm = Some nps -> InferWidths_transss ss newtm = Some nss ->
  make_ps_implicit vm' (CEP.empty vertex_type) pp = Some vm'' -> make_ss_implicit vm' vm'' ss = Some vm -> ports_stmts_tmap pp ss vm = Some newtm.
Proof.
  (* TBD
  rewrite /ports_stmts_tmap.
  elim.
  elim.
  - simpl; done.
  - intros s st IH; intros nps nss newtm vm' vm'' vm pv Hinfer Hps Hss Himplips Himpliss.
    simpl; simpl in Hps; simpl in Hss; simpl in Himplips; simpl in Himpliss.
    inversion Hps; clear Hps H0 nps; inversion Himplips; rewrite -H0 in Himpliss; clear Himplips H0 vm''.
    case Htrans : (InferWidths_transs s newtm) => [ns|]; rewrite Htrans in Hss; try discriminate.
    case Htranss : (InferWidths_transss st newtm) => [nst|]; rewrite Htranss in Hss; try discriminate.
    case Himplis : (make_s_implicit vm' (CEP.empty vertex_type) s) => [vm0|]; rewrite Himplis in Himpliss; try discriminate.
    inversion Hss as [Hnss]; clear Hss.
    case Hss : (stmt_tmap (CEP.empty (ftype * bool), CEP.empty (ftype * bool)) s vm) => [tmap_scope'|].
    case Hsst : (stmts_tmap tmap_scope' st vm) => [[tmap' emap']|].
    (*apply IH with (nps := [::]) (nss := nst) (newtm := newtm) (pv := pv) in Himpliss; try done.

    case Hsp : (stmt_tmap' (CEP.empty (ftype * bool)) (CEP.empty (seq HiFP.hfexpr)) s) => [[tmap0 emap0]|]; rewrite Hsp in Hinfer; try discriminate.
    case Hsps : (stmts_tmap' tmap0 emap0 st) => [[tmap' var2exprs]|]; rewrite Hsps in Hinfer; try discriminate.
    case Hrl : (lsreg_stmt s) => [rl|]; rewrite Hrl in Hinfer; try discriminate.
    case Hrls : (lsreg_stmts st) => [rls|]; rewrite Hrls in Hinfer; try discriminate.*)
    *)

Admitted.

Lemma Qin_cons : forall a tl, @Qin (ProdVarOrder.T) a (Qcons a tl).
Proof.
Admitted.

Definition legal_module F vm vm': Prop := match F with 
  | FInmod mv pp ss => (exists tmap', ports_stmts_tmap pp ss vm = Some tmap') 
    /\ (forall vm'' newtm, make_ps_implicit vm' (CEP.empty vertex_type) pp = Some vm'' -> InferWidths_stage1 (FInmod mv pp ss) = Some newtm -> exists ct', Sem_frag_ports (CEP.empty vertex_type) (CEP.empty def_expr) pp vm'' ct' newtm)
    /\ (forall tmap0 var2exprs lsreg theg vertices regg reg_vertices inferorder newtm, ports_stmts_tmap' pp ss = Some (tmap0, var2exprs) -> lsreg_stmts ss = Some lsreg 
      -> drawg (CEP.elements var2exprs) tmap0 lsreg emptyg emptyg [::] [::] = Some (theg, vertices, regg, reg_vertices) -> TopoSort.topo_sort vertices theg = TopoSort.Sorted inferorder
      -> InferWidths_fun inferorder var2exprs tmap0 = Some newtm 
      -> (forall ref e t_expr t_tgt ori, Qin (Sfcnct (Eid (var:=ProdVarOrder.T) ref) e) ss -> type_of_expr e newtm = Some t_expr -> type_of_ref ref newtm = Some (t_tgt, ori) -> ftype_equiv t_tgt t_expr))
    /\ (forall tmap0 var2exprs lsreg theg vertices regg reg_vertices inferorder newtm, ports_stmts_tmap' pp ss = Some (tmap0, var2exprs) -> lsreg_stmts ss = Some lsreg 
      -> drawg (CEP.elements var2exprs) tmap0 lsreg emptyg emptyg [::] [::] = Some (theg, vertices, regg, reg_vertices) -> TopoSort.topo_sort vertices theg = TopoSort.Sorted inferorder
      -> InferWidths_fun inferorder var2exprs tmap0 = Some newtm 
      -> (forall ref e, Qin (Sfcnct (Eid (var:=ProdVarOrder.T) ref) e) ss -> (exists t_expr, type_of_expr e newtm = Some t_expr) /\ (exists t_tgt ori, type_of_ref ref newtm = Some (t_tgt, ori))))
    /\ (forall ref e, Qin (Sfcnct ref e) ss 
      -> match e with | Eref (Eid _) => true | Eref _ => false | _ => true end /\ match ref with | Eid _ => true | _ => false end)
  | FExmod _ _ _ => false
  end.

Theorem InferWidths_correct :
  forall (F : HiFP.hfmodule) (vm' : CEP.t vertex_type),
    match InferWidths_m F, make_vm_implicit F vm' with
    | Some (F', _), Some vm => Sem F' vm' -> Sem F vm
    | _, _ => True
    end.
Proof.
  intros.
  case Hinfer : (InferWidths_m F) => [[F' t]|]; try done.
  case Himplivm : (make_vm_implicit F vm') => [vm|]; try done.
  rewrite {2}/Sem; rewrite /InferWidths_m in Hinfer.
  case Hinfer1 : (InferWidths_stage1 F) => [newtm|]; rewrite Hinfer1 in Hinfer; try discriminate.
  case Hinfer2 : (InferWidths_stage2 F newtm) => [nm|]; rewrite Hinfer2 in Hinfer; try discriminate.
  inversion Hinfer; clear Hinfer.
  rewrite H0 in Hinfer2; clear H0 nm H1 t.
  case HF : F => [[v0 v1 pp ss]|f]; rewrite HF in Himplivm Hinfer1 Hinfer2; rewrite /InferWidths_stage2 in Hinfer2; try discriminate.
  case Htransp : (InferWidths_transps pp newtm) => [nps|]; rewrite Htransp in Hinfer2; try discriminate.
  case Htranss : (InferWidths_transss ss newtm) => [nss|]; rewrite Htranss in Hinfer2; try discriminate.
  inversion Hinfer2; clear Hinfer2 H0 F' HF.
  rewrite /make_vm_implicit in Himplivm.
  case Himplips : (make_ps_implicit vm' (CEP.empty vertex_type) pp) => [vm''|]; rewrite Himplips in Himplivm; try discriminate.
  intros Hsem.
  assert (Hlegal : legal_module (FInmod (v0, v1) pp ss) vm vm').
    move : Hinfer1 Htransp Htranss Himplips Himplivm Hsem.
    admit.
  rewrite /legal_module in Hlegal; move : Hlegal => [Hlegal [Hlegal1 [Hlegal2 [Hlegal3 Hlegal4]]]].
  (*assert (exists tmap', ports_stmts_tmap pp ss vm = Some tmap').
  admit. (* 由 Hps' *) *)
  destruct Hlegal as [tmap' Hps]; rewrite Hps.
  generalize Htransp; apply InferWidths_trans_correct with (ss := ss) (nss := nss) (vm' := vm') (vm'' := vm'') (vm := vm) in Htransp; try done.
  rewrite Hps in Htransp; inversion Htransp; clear Htransp; rewrite H0 in Hps; clear H0 tmap'; intro Htransp.
  specialize (Hlegal1 _ _ Himplips Hinfer1); destruct Hlegal1 as [ct' Hlegal1].
  exists vm''; exists (ct'). (* 先不check任何关于connection *)
  split; try done; clear Hlegal1.
  - rewrite /InferWidths_stage1 in Hinfer1.
    case Hps0 : (ports_stmts_tmap' pp ss) => [[tmap0 var2exprs]|]; rewrite Hps0 in Hinfer1; try discriminate.
    case Hreg : (lsreg_stmts ss) => [lsreg|]; rewrite Hreg in Hinfer1; try discriminate.
    case Hdraw : (drawg (CEP.elements var2exprs) tmap0 lsreg emptyg emptyg [::] [::]) => [[[[theg vertices] regg] reg_vertices]|]; rewrite Hdraw in Hinfer1; try discriminate.
    case Htopo : (TopoSort.topo_sort vertices theg) => [inferorder||]; rewrite Htopo in Hinfer1; try discriminate.
    case Htopo' : (TopoSort.topo_sort reg_vertices regg) => [t||]; rewrite Htopo' in Hinfer1; try discriminate; clear Htopo' t.
    rewrite /ports_stmts_tmap in Hps. 
    case Hpps : (ports_tmap pp vm) => [pmap|]; rewrite Hpps in Hps; try discriminate.
    case Hpss : (stmts_tmap (pmap, pmap) ss vm) => [[tmap1 tmap2]|]; rewrite Hpss in Hps; try discriminate.
    inversion Hps; clear Hps; rewrite H0 in Hpss; clear H0 tmap1.
    clear Hpps.
    specialize (Hlegal2 _ _ _ _ _ _ _ _ _ Hps0 Hreg Hdraw Htopo Hinfer1).
    specialize (Hlegal3 _ _ _ _ _ _ _ _ _ Hps0 Hreg Hdraw Htopo Hinfer1).
    specialize (InferWidths_fun_correct pp ss inferorder var2exprs tmap0 newtm Hinfer1 Hps0); intro Hinfer.
    move : Hpss Himplivm Hinfer Hlegal2 Hlegal3 Hlegal4.
    clear.
    move : ss vm' vm pmap tmap2 vm'' newtm.
    elim.
    - simpl; intros; inversion Himplivm; apply CEP.Lemmas.Equal_refl.
    - intros s st IH vm0 vm pmap tmap2 nvm newtm Hmaps Himplis Hinfer Hlegal2 Hlegal3 Hlegal4.
      simpl; simpl in Hmaps; simpl in Himplis.
      case Hmap : (stmt_tmap (pmap, pmap) s vm) => [[tmap' tmap2']|]; rewrite Hmap in Hmaps; try discriminate.
      case Himpli : (make_s_implicit vm0 nvm s) => [vm'|]; rewrite Himpli in Himplis; try discriminate.
      exists vm'; split.
      - clear IH.
        (*apply InferWidths_fun_correct with (pp := pp) (ss := (Qcons s st)) (hfs := s) in Hinfer1; try done.*)
        specialize Hinfer with (hfs := s).
        case Hs : s => [|r t|r reg|||r e|r e|r|c s1 s2]; rewrite Hs in Hmap Himpli Hinfer Hlegal2 Hlegal3 Hlegal4; simpl; try done.
        - simpl in Hmap; simpl in Himpli; inversion Himpli; apply CEP.Lemmas.Equal_refl.
        - (* reg *)
          (*case Hrst : (reset reg) => [|rst_sig rst_val]; try done.
          case Hft : (CEP.find r newtm) => [[ft ori]|].
          - case Hval : (type_of_expr rst_val newtm) => [[ft_val p_val]|].
            rewrite /connect_type; apply rwP with (P := ftype_equiv ft ft_val /\
            check_connect_type
              (list_gtypref (0%num, 0%num) ft false)
              (list_gtypref (0%num, 0%num) ft_val false)). apply andP. split.
            admit. (* cnct 要求 ftype_equiv *)
            simpl in Hmap; simpl in Himpli.
            case Hfindp : (CEP.find r pmap); rewrite Hfindp in Hmap; try discriminate.
            destruct (type_of_expr (clock reg) pmap); try discriminate.
            case Hft_vm : (code_type_find_vm_widths (type reg) r vm) => [[newt n]|]; rewrite Hft_vm in Hmap; try discriminate.
            rewrite Hrst in Hmap.
            case Hsig : (type_of_expr rst_sig pmap) => [[tf t]|]; rewrite Hsig in Hmap; try discriminate.
            case Htf : tf => [f1||]; rewrite Htf in Hmap; try discriminate.
            case Hf1 : f1 => [n1||||||]; rewrite Hf1 in Hmap; try discriminate.
            - (* Fuint1 rst *) 
              case Hn1 : n1 => [|n0]; rewrite Hn1 in Hmap; try discriminate.
              destruct n0; try discriminate; clear Hsig Htf Hf1 Hn1 n1 f1 t tf.
              assert (exists ft_val', type_of_expr rst_val (CEP.add r (newt, false) pmap) = Some ft_val').
              admit.
              destruct H as [[ft_val' p_val'] Hval']; rewrite Hval' in Hmap; clear Hval' ft_val' p_val'.
              inversion Hmap; clear Hmap.
              assert (CEP.find r tmap = CEP.find r tmap').
              admit. (* s = Sreg r reg 不在 st 中，由Hmaps *)
              rewrite H -H0 in Hft; clear H Hmaps H1 H0 f Hfindp.
              rewrite CEP.Lemmas.find_add_eq in Hft; try apply PVM.SE.eq_refl.
              inversion Hft; clear Hft; rewrite H0 in Hft_vm; clear H0 H1 ori newt.
              admit.
            - (* aync *)
              clear Hsig Htf Hf1 f1 t tf.
              assert (exists ft_val', type_of_expr rst_val pmap = Some ft_val').
              admit.
              destruct H as [[ft_val' p_val'] Hval']; rewrite Hval' in Hmap; clear Hval' ft_val' p_val'.
              inversion Hmap; clear Hmap.
              assert (CEP.find r tmap = CEP.find r tmap').
              admit. (* s = Sreg r reg 不在 st 中，由Hmaps *)
              rewrite H -H0 in Hft; clear H Hmaps H1 H0 f Hfindp.
              rewrite CEP.Lemmas.find_add_eq in Hft; try apply PVM.SE.eq_refl.
              inversion Hft; clear Hft; rewrite H0 in Hft_vm; clear H0 H1 ori newt.
              admit. (* TBD *)
          - admit. (* None则有错 *)
          - admit. (* None则有错 *)*)
          admit.
        - (* cnct *)
          case Hr : r => [ref|||]; rewrite Hr in Hs Hinfer Hlegal2 Hlegal3 Hlegal4.
          case He : e => [t c| c e1 | u e1 | op e1 e2 | c e1 e2 | c e1 | r2 ]; rewrite He in Hs Hinfer Hlegal2 Hlegal3 Hlegal4.
          - (* expr *)
          1,2,3,4,5,6 : rewrite -He; rewrite -He in Hinfer Hlegal2 Hlegal3; clear He Hs Hr.
          1,2,3,4,5,6 : case Hreft : (type_of_ref ref newtm) => [[t_tgt ori]|]; rewrite Hreft in Hinfer.
          1,3,5,7,9,11 : case Hexprt : (type_of_expr e newtm) => [t_expr|]; rewrite Hexprt in Hinfer.
          1,3,5,7,9,11 : apply Hinfer; try done.
          1,3,5,7,9,11 : apply Qin_cons.
          1-6 : apply (Hlegal2 ref e t_expr t_tgt ori); try done; try apply Qin_cons.
          1-6 : specialize (Hlegal3 ref e (Qin_cons (Sfcnct (Eid (var:=ProdVarOrder.T) ref) e) st));
            move : Hlegal3 => [Hlegal3 _]; destruct Hlegal3 as [t_expr Hlegal3]; rewrite Hlegal3 in Hexprt; discriminate.
          1-6 : specialize (Hlegal3 ref e (Qin_cons (Sfcnct (Eid (var:=ProdVarOrder.T) ref) e) st));
            move : Hlegal3 => [_ Hlegal3]; destruct Hlegal3 as [t_tgt [ori Hlegal3]]; rewrite Hlegal3 in Hreft; discriminate.
          - (* ref *)
          case Hr2 : r2 => [ref_src|||]; rewrite Hr2 in Hinfer.
          case Hreft : (type_of_ref ref newtm) => [[t_tgt ori]|]; rewrite Hreft in Hinfer.
          case Hexprt : (type_of_ref ref_src newtm) => [[t_expr p_expr]|]; rewrite Hexprt in Hinfer; try done.
          apply Hinfer; try done.
          apply Qin_cons. (* Qin_cons *)
          apply (Hlegal2 ref (Eref r2) t_expr t_tgt ori); try done; try apply Qin_cons. rewrite Hr2; simpl; rewrite Hexprt //.
          specialize (Hlegal3 ref (Eref r2) (Qin_cons (Sfcnct (Eid (var:=ProdVarOrder.T) ref) (Eref r2)) st));
            move : Hlegal3 => [Hlegal3 _]; destruct Hlegal3 as [t_expr Hlegal3]. rewrite Hr2 in Hlegal3; simpl in Hlegal3; rewrite Hexprt in Hlegal3; discriminate.
          specialize (Hlegal3 ref (Eref r2) (Qin_cons (Sfcnct (Eid (var:=ProdVarOrder.T) ref) (Eref r2)) st));
            move : Hlegal3 => [_ Hlegal3]. destruct Hlegal3 as [t_tgt [ori Hlegal3]]; rewrite Hlegal3 in Hreft; discriminate.
          1-3 : specialize (Hlegal4 (Eid ref) (Eref r2) (Qin_cons (Sfcnct (Eid (var:=ProdVarOrder.T) ref) (Eref r2)) st));
            move : Hlegal4 => [Hlegal4 _]; rewrite Hr2 in Hlegal4; discriminate.          
          1-3 : rewrite -Hr in Hlegal4; specialize (Hlegal4 r e (Qin_cons (Sfcnct r e) st));
            move : Hlegal4 => [_ Hlegal4]; rewrite Hr in Hlegal4; discriminate.      

        - (* when *)
          admit.
      - apply IH with (vm' := vm0) (pmap := tmap') (tmap2 := tmap2); try done.
        admit.
        (*intros.
        apply Hinfer with (hfs := hfs) in H; try done.*)
Admitted.

Definition type_of_vx (x : vertex_type) : fgtyp :=
  match x with
  | InPort i
  | OutPort i
  | Node i
  | Register i _ _ _
  | Wire i => i 
  end.

Definition vm_le (vm : CEP.t vertex_type) (vm' : CEP.t vertex_type) : Prop := 
  forall (v : ProdVarOrder.t), match CEP.find v vm', CEP.find v vm with
  | Some t', Some t => if (not_implicit (type_of_vx t')) then true else (sizeof_fgtyp (type_of_vx t)) >= (sizeof_fgtyp (type_of_vx t'))
  | None, None => true
  | _, _ => false
  end.

Lemma Sem_wd_geq : forall v mv ps ss vm t tmap' var2exprs el order1 tmap0, Sem (FInmod mv ps ss) vm -> 
  CEP.find v vm = Some t -> ports_stmts_tmap' ps ss = Some (tmap', var2exprs) -> find_sub_exprs v ss tmap' = Some el -> 
  InferWidths_fun order1 var2exprs tmap' = Some tmap0 -> (* 且拓扑排序上order1在v之前 *) 
  (forall e gt, e \in el -> type_of_expr e tmap0 = Some (Gtyp gt) -> sizeof_fgtyp (type_of_vx t) >= sizeof_fgtyp gt).
Proof.
  intros.
  simpl in H. 
  case Hpre : (ports_stmts_tmap ps ss vm) => [tmap|]; rewrite Hpre in H; try done.
  destruct H as [vm' [ct [_ H]]]; clear ct mv.
  move : H0 H1 H2 H3 H4 H5 Hpre H. 
  move : ss v ps vm t tmap' var2exprs el order1 tmap0 e gt tmap vm'.
  
  elim.
  - (* nil *) 
    intros. simpl in H; simpl in Hpre; simpl in H1; simpl in H2; inversion H2; clear H2.
    rewrite -H7 in H4; rewrite in_nil in H4; discriminate.
  - (* cons *)
    intros hd tl IH; intros.
    simpl in H; destruct H as [vm0 [Hsem0 Hsem]].
    rewrite /ports_stmts_tmap' in H1; case Hps' : (ports_tmap' ps) => [pmap|]; rewrite Hps' in H1; try discriminate.
    simpl in H1; case Hss' : (stmt_tmap' pmap (CEP.empty (seq HiFP.hfexpr)) hd) => [[tmap1 emap1]|]; rewrite Hss' in H1; try discriminate.
    simpl in H2; case Hfind : (find_sub_expr v hd tmap') => [e0|]; rewrite Hfind in H2; try discriminate.
    case Hfinds : (find_sub_exprs v tl tmap') => [el0|]; rewrite Hfinds in H2; try discriminate.
    rewrite /ports_stmts_tmap in Hpre. case Hps : (ports_tmap ps vm) => [pmap0|]; rewrite Hps in Hpre; try discriminate.
    case Hss : (stmts_tmap (pmap0, pmap0) (Qcons hd tl) vm) => [[tmap2 emap2]|]; rewrite Hss in Hpre; try discriminate.
    inversion Hpre; clear Hpre; rewrite H6 in Hss; clear H6 tmap2.
    simpl in Hss; case Hss0 : (stmt_tmap (pmap0, pmap0) hd vm) => [tmap3|]; rewrite Hss0 in Hss; try discriminate.
    move :  Hsem. (* 要把ports_stmts_tmap'拆开 *)
    (*apply IH.
    intros v t el Hv Hfinde e te Hin Hte. 
    simpl in Hfinde.
    case Hfinde0 : (find_sub_expr v h tmap) => [e0|]; rewrite Hfinde0  in Hfinde; try discriminate.
    case Hfinde1 : (find_sub_exprs v ss tmap) => [e1|]; rewrite Hfinde1 in Hfinde; try discriminate.
    inversion Hfinde; clear Hfinde.
    rewrite -H0 in Hin; clear H0 el.
    rewrite mem_cat in Hin.
    case Hin0 : (e \in e0); rewrite Hin0 in Hin. 
    clear Hin Hsem Hfinde1. 

    admit.
    clear Hin0; rewrite orb_false_l in Hin.
    apply IHss with (v := v) (t := t) (el := e1) (e := e) (te := te) in Hsem; try done.*)
Admitted. (* Sem_wdgeqmax *)

Lemma geq_conj2mux : forall tmap (gt initt : fgtyp) (el : seq HiFP.hfexpr) eftl (nt : fgtyp), (forall (texpr : HiFP.hfexpr) (te : fgtyp), texpr \in el -> type_of_expr texpr tmap = Some (Gtyp te) -> ((sizeof_fgtyp gt) >= (sizeof_fgtyp te))) ->
  fil_ftlist [seq type_of_expr e tmap | e <- el] = Some eftl -> sizeof_fgtyp initt = 0 -> max_ftlist eftl initt = Some nt -> ((sizeof_fgtyp gt) >= (sizeof_fgtyp nt)).
Proof.
  intros tmap gt initt.
  elim.
  intros.
  simpl in H0.
  inversion H0; clear H0.
  rewrite -H4 in H2.
  simpl in H2.
  inversion H2; clear H2.
  rewrite -H3 H1.
  rewrite /sizeof_fgtyp.
  case Het : gt; try done.

  intros hd tl IH eftl nt H Heftl Hinitt Hmax.
  simpl in Heftl.
  case Hhd : (type_of_expr hd tmap) => [f|]; rewrite Hhd in Heftl; try discriminate.
  case Hf : f => [hdt||]; rewrite Hf in Hhd Heftl; clear Hf; try discriminate.
  case Heftl' : (fil_ftlist [seq type_of_expr e tmap | e <- tl]) => [eftl'|]; rewrite Heftl' in Heftl; try discriminate.
  inversion Heftl; clear Heftl.
  rewrite -H1 in Hmax.
  simpl in Hmax.
  case Hmax' : (max_ftlist eftl' initt) => [nt'|]; rewrite Hmax' in Hmax; try discriminate.

  assert (max_fgtyp hdt nt' = Some nt -> sizeof_fgtyp nt' <= sizeof_fgtyp gt -> sizeof_fgtyp hdt <= sizeof_fgtyp gt -> sizeof_fgtyp nt <= sizeof_fgtyp gt).
  clear.
  intros.
  rewrite /max_fgtyp in H.
  case Hhd : hdt => [w|w|w|w|||]; rewrite Hhd in H H1; try discriminate.
  case Hnt' : nt' => [w'|w'|w'|w'|||]; rewrite Hnt' in H H0; try discriminate.
  inversion H; clear H.
  simpl in H1; simpl in H0; simpl.

  (*specialize Nat.max_spec_le with (n := w) (m := w'); intro.*)
  move : H1 H0.
  admit. (* TBD *) (* geq_max *)
  case Hnt' : nt' => [w'|w'|w'|w'|||]; rewrite Hnt' in H H0; try discriminate.
  inversion H; clear H.
  simpl in H1; simpl in H0; simpl.
  move : H1 H0.
  admit.
  case Hnt' : nt' => [w'|w'|w'|w'|||]; rewrite Hnt' in H H0; try discriminate.
  inversion H; clear H.
  simpl in H1; simpl in H0; simpl.
  move : H1 H0.
  admit.
  case Hnt' : nt' => [w'|w'|w'|w'|||]; rewrite Hnt' in H H0; try discriminate.
  inversion H; clear H.
  simpl in H1; simpl in H0; simpl.
  move : H1 H0.
  admit.

  apply H0 in Hmax; try done; clear H0.
  apply IH with (eftl := eftl'); try done.
  intros expr tge Hin.
  apply H.
  rewrite in_cons Hin.
  rewrite orb_true_r; done.
  apply H with (texpr := hd); try done.
  rewrite in_cons.
  rewrite eq_refl.
  rewrite orb_true_l; done.
Admitted.

Theorem InferWidths_correct' :
  forall (F : HiFP.hfmodule) (vm : CEP.t vertex_type) (vm' : CEP.t vertex_type),
    match InferWidths_m F with
    | Some (F', _) => Sem F' vm' -> Sem F vm -> vm_le vm vm'
    | _ => True
    end.
Proof.
  intros F vm vm'.
  case Hinfer : (InferWidths_m F) => [[F' newtm]|]; try done.
  intros Hsem' Hsem.
  rewrite /vm_le; intro v.
  case Ht' : (CEP.find v vm') => [t'|].
  case Ht : (CEP.find v vm) => [t|]; try done.
  case Himpli : (not_implicit (type_of_vx t')); try done.
  rewrite /InferWidths_m in Hinfer.
  case Hinfer1 : (InferWidths_stage1 F) => [newtm'|]; rewrite Hinfer1 in Hinfer; try discriminate.
  case Hinfer2 : (InferWidths_stage2 F newtm') => [nm|]; rewrite Hinfer2 in Hinfer; try discriminate.
  inversion Hinfer; clear Hinfer; rewrite H0 in Hinfer2; clear H0 nm; rewrite H1 in Hinfer1 Hinfer2; clear H1 newtm'.
  generalize Hinfer1; rewrite /InferWidths_stage1 in Hinfer1; intros Hstage1.
  case HF : F => [mv ps ss|]; rewrite HF in Hinfer1 Hstage1; try discriminate.
  rewrite HF in Hsem Hinfer2; clear HF F.
  case Hpre : (ports_stmts_tmap' ps ss) => [[tmap' var2exprs]|]; rewrite Hpre in Hinfer1; try discriminate.
  case Hrl : (lsreg_stmts ss) => [rl|]; rewrite Hrl in Hinfer1; try discriminate.
  case Hdraw : (drawg (CEP.elements var2exprs) tmap' rl emptyg emptyg [::] [::]) => [[[[theg vertices]regg] reg_vertices]|]; rewrite Hdraw in Hinfer1; try discriminate.
  case Htopo : (TopoSort.topo_sort vertices theg) => [inferorder||]; rewrite Htopo in Hinfer1; try discriminate.
  destruct (TopoSort.topo_sort reg_vertices regg); try discriminate; clear l.

  assert (v \in inferorder).
  admit. (* inferorder 的正确性，是展开时的标号 *)
  assert (exists order1 order2, inferorder = order1 ++ (v :: order2) /\ v \notin order1 /\ v \notin order2).
  admit. (* 由H推出 *)
  clear H.
  move : H0 => [order1 [order2 [H2 [Horder1 Horder2]]]].
  rewrite H2 in Hinfer1; rewrite /InferWidths_fun in Hinfer1.
  case Hinfer1' : (InferWidths_fun order1 var2exprs tmap') => [tmap0|].
  assert (Hinfer2' : InferWidths_fun (v :: order2) var2exprs tmap0 = Some newtm).
  move : Hinfer1 Hinfer1'.
  apply infer_cons_order.
  clear Hinfer1 Hdraw Htopo theg vertices regg reg_vertices.
  generalize Hinfer2'; simpl in Hinfer2'; intros Hod2.
  case Hel : (CEP.find v var2exprs) => [el|]; rewrite Hel in Hinfer2'; try discriminate.
  case Hinfer1 : (InferWidth_fun v el tmap0) => [newtm'|]; rewrite Hinfer1 in Hinfer2'; try discriminate.
  rewrite /InferWidth_fun in Hinfer1.
  case Hfil : (fil_ftlist [seq type_of_expr e tmap0 | e <- el]) => [eftl|]; rewrite Hfil in Hinfer1; try done.
  case Hinit : (CEP.find (v.1, 0%num) tmap0) => [[init ori_v]|]; rewrite Hinit in Hinfer1; try discriminate.
  case Hf : (ft_find_sub init v.2 false) => [[f ori]|]; rewrite Hf in Hinfer1; try discriminate.
  case Hinitt : f => [initt||]; rewrite Hinitt in Hinfer1; try discriminate.
  rewrite Hinitt in Hf; clear Hinitt f.
  (*assert (Himpli' : not_implicit initt = false) by admit. (* drawg只考虑implicit *)*)
  case Hmax : (max_ftlist eftl initt) => [nt|]; rewrite Hmax in Hinfer1; try discriminate.
  case Hset : (ft_set_sub init nt v.2) => [nt0|]; rewrite Hset in Hinfer1; try discriminate. 
  inversion Hinfer1; clear Hinfer1.

  simpl in Hinfer2.
  case Hnps : (InferWidths_transps ps newtm) => [nps|]; rewrite Hnps in Hinfer2; try discriminate.
  case Hnss : (InferWidths_transss ss newtm) => [nss|]; rewrite Hnss in Hinfer2; try discriminate.
  inversion Hinfer2; clear Hinfer2; rewrite -H1 in Hsem'; clear H1 F'.
  assert (forall v ft ori, CEP.find v vm' = Some t' -> type_of_ref v newtm = Some (ft, ori) -> expli_ftype ft = Gtyp (type_of_vx t')).
    move : Hnps Hnss Hsem'.
    admit.
  (*apply InferWidths_trans_correct' with (F' := F') (mv := mv) (ps := ps) (ss := ss) (newtm := newtm) (ft := Gtyp nt) (ori := ori) in Ht'; try done.
  inversion Ht'; clear Ht'; rewrite -H1; clear H1.*)
  apply H with (ft := (Gtyp nt)) (ori := ori) in Ht'; clear H.
  assert (sizeof_fgtyp nt = sizeof_fgtyp (type_of_vx t')) by
    (move : Ht'; clear; 
    intros; rewrite /expli_ftype in Ht'; 
    case Hnt : nt =>[w|w|w|w|||]; rewrite Hnt in Ht'; inversion Ht'; clear Ht'; simpl; try done).
  rewrite -H; clear H.
  move : Ht Hpre Hel Hfil Hinfer1' Hod2 Hinit Hf Hmax Hsem; clear; intros.
  assert (exists el', find_sub_exprs v ss tmap' = Some el') by admit.
  destruct H as [el' H].
  generalize H; apply (find_sub_exprs_correct _ _ _ _ _ _ _ Hpre Hel) in H; intros H'.
  specialize (Sem_wd_geq _ _ _ _ _ _ _ _ el' order1 tmap0 Hsem Ht Hpre H' Hinfer1'); intros.
  (*generalize Hsem; rewrite /Sem in Hsem.
  case Hpre0 : (ports_stmts_tmap ps ss vm) => [tmap0'|]; rewrite Hpre0 in Hsem; try done.
  destruct Hsem as [vm0 [ct0 [_ Hsems]]]; intro Hsem.*)
  assert (forall (e : hfexpr_eqType ProdVarOrder.T) (gt : fgtyp),
     e \in el -> type_of_expr e tmap0 = Some (Gtyp gt) -> sizeof_fgtyp gt <= sizeof_fgtyp (type_of_vx t)).
    intros.
    apply H0 with (e := e); try done.
    move : H => [H _]; move : H1 H; apply TopoSort.in_subset_trans.
  clear H0 H.
  apply (geq_conj2mux _ _ _ _ _ _ H1) in Hmax; try done.
  admit. (* implicit原始都为0 *)
  apply (infernotin_eq _ _ _ _ _ Horder2) in Hinfer2'; rewrite Hinfer2'.
  rewrite /type_of_ref -H0 CEP.Lemmas.find_add_eq; try apply PVM.SE.eq_refl.
    assert (ftype_equiv init nt0).
    admit.
  admit. (* 要改set_find_sub关于ori *)
  admit. (* None则有错 *)
  admit. (* None则有错 *)
  case Ht : (CEP.find v vm); try done.
Admitted.

Search (list_gtypref).