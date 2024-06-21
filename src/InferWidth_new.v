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
                        | Nflip => list_gtypref (v.1, N.add v.2 1%num) ft ori ++ list_gtypref_ff (v.1, N.add v.2 (N.of_nat (num_ref ft + 1))) ff' ori
                        | Flipped => list_gtypref (v.1, N.add v.2 1%num) ft (~~ori) ++ list_gtypref_ff (v.1, N.add v.2 (N.of_nat (num_ref ft + 1))) ff' ori
                        end
   end.

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
  (*assert (nth_error (hd :: tl) (n + 1) = nth_error tl n).
  rewrite H0.
  admit.
  assert (nth_error (hd' :: tl') (n + 1) = nth_error tl' n).
  admit.
  rewrite H1 H2 in IH; done.
  nth_error_app1 *)
Admitted.

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
    admit.
  - (* nflip *) 
    apply rwP with (P := connect_fgtyp_compatible gt0 gt1 /\ check_connect_non_passive_type tl tl').
    apply andP. split.
    specialize IH with (n := 0); simpl in IH; done.
    apply H.
    intro.
    specialize IH with (n := n+1).
    admit.
Admitted.

Lemma listgtyp_eq t_tgt t_expr : forall n ref0 ref1 ori0 ori1 ori2 ori3 pv0 pv1 gt gte, ftype_equiv t_tgt t_expr -> nth_error (list_gtypref ref0 t_tgt ori0) n =
  Some (pv0, gt, ori2) -> nth_error (list_gtypref ref1 t_expr ori1) n = Some (pv1, gte, ori3) -> fgtyp_equiv gt gte.
Proof.
Admitted.

Lemma infer_cons_order : forall order1 order2 var2exprs tmap tmap' newtm, InferWidths_fun (order1 ++ order2) var2exprs tmap = Some newtm -> InferWidths_fun order1 var2exprs tmap = Some tmap' ->
  InferWidths_fun order2 var2exprs tmap' = Some newtm.
Proof.
Admitted.

Lemma find_mux_types_n : forall t1 t2 t_expr tt1 tt2 n tte, mux_types t1 t2 = Some t_expr -> nth_error (list_gtypref (0%num, 0%num) t1 false) n = Some tt1 -> 
  nth_error (list_gtypref (0%num, 0%num) t2 false) n = Some tt2 -> nth_error (list_gtypref (0%num, 0%num) t_expr false) n = Some tte -> mux_gtyp tt1.1.2 tt2.1.2 = Some tte.1.2
with find_mux_types_n_f : forall t1 t2 t_expr tt1 tt2 n tte, mux_btyps t1 t2 = Some t_expr -> nth_error (list_gtypref_ff (0%num, 0%num) t1 false) n = Some tt1 -> 
  nth_error (list_gtypref_ff (0%num, 0%num) t2 false) n = Some tt2 -> nth_error (list_gtypref_ff (0%num, 0%num) t_expr false) n = Some tte -> mux_gtyp tt1.1.2 tt2.1.2 = Some tte.1.2.
Proof.
  (*clear find_mux_types_n.
  elim.
  intros.
  case Ht2 : t2 => [gt||]; rewrite Ht2 in H H1; simpl in H; try discriminate.
  case Hmux : (mux_gtyp f gt) => [gte|]; rewrite Hmux in H; try discriminate.
  inversion H. 
  simpl in H0; simpl in H1; simpl.
  case Hn : n; rewrite Hn in H0 H1.
  simpl in H0; simpl in H1.
  inversion H0; clear H0.
  inversion H1; clear H1.
  rewrite -H2 -H4 Hmux.
  simpl; done.
  admit. (* H0 H1 为None *)

  intros.
  case Ht2 : t2 => [|atyp na|]; rewrite Ht2 in H0 H2; simpl in H0; try discriminate.
  case Hn : (n == na); rewrite Hn in H0; try discriminate.
  case Hmux : (mux_types f atyp) => [natyp|]; rewrite Hmux in H0; try discriminate.
  inversion H0; clear H0.
  simpl in H1; simpl in H2; simpl.
  apply H with (tt1 := tt1) (tt2 := tt2) (n :=n0) in Hmux; try done.

  intros.
  case Ht2 : t2 => [||btyp]; rewrite Ht2 in H H1; simpl in H; try discriminate.
  case Hmux : (mux_btyps f btyp) => [ff|]; rewrite Hmux in H; try discriminate.
  inversion H; clear H H3. 
  simpl in H0; simpl in H1; simpl.
  move : Hmux H0 H1.
  apply find_mux_types_n_f.

  clear find_mux_types_n_f.
  elim.
  intros.
  case Ht2 : t2; rewrite Ht2 in H; simpl in H; try discriminate.
  simpl in H0.
  apply nth_error_In in H0.
  apply List.in_nil in H0; done.
  intros.
  case Ht2 : t2 => [|v' f' f0' f1']; rewrite Ht2 in H0 H2; simpl in H0; case Hf : f ;rewrite Hf in H0; try discriminate.
  case Hf' : f'; rewrite Hf' in H0; try discriminate.
  case Hv : (v == v'); rewrite Hv in H0; try discriminate.
  case Hmux : (mux_types f0 f0') => [nt|]; rewrite Hmux in H0; try discriminate.
  case Hmux' : (mux_btyps f1 f1') => [nf|]; rewrite Hmux' in H0; try discriminate.
  simpl in H1; simpl in H2.
  inversion H0; clear H0 H4.
  simpl.
  case Hn : (n < length (list_gtyp nt)).
  assert (nth_error (list_gtyp nt ++ list_gtyp_ff nf) n = nth_error (list_gtyp nt) n).
  admit. (* nth_error_app1 *)
  assert (nth_error (list_gtyp f0 ++ list_gtyp_ff f1) n = nth_error (list_gtyp f0) n).
  admit. (* nth_error_app1 *)
  assert (nth_error (list_gtyp f0' ++ list_gtyp_ff f1') n = nth_error (list_gtyp f0') n).
  admit. (* nth_error_app1 *)
  rewrite H0; rewrite H3 in H1; rewrite H4 in H2.
  move : Hmux H1 H2.
  apply find_mux_types_n.
  assert (nth_error (list_gtyp nt ++ list_gtyp_ff nf) n = nth_error (list_gtyp_ff nf) (n - (length (list_gtyp nt)))).
  admit. (* nth_error_app2 *)
  assert (nth_error (list_gtyp f0 ++ list_gtyp_ff f1) n = nth_error (list_gtyp_ff f1) (n - (length (list_gtyp nt)))).
  admit. (* nth_error_app2 *)
  assert (nth_error (list_gtyp f0' ++ list_gtyp_ff f1') n = nth_error (list_gtyp_ff f1') (n - (length (list_gtyp nt)))).
  admit. (* nth_error_app2 *)
  rewrite H0; rewrite H3 in H1; rewrite H4 in H2.
  move : Hmux' H1 H2.
  apply H.*)
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

Lemma ftype_equiv_split_eq : forall s t1 t2, ftype_equiv t1 t2 -> list_gtypexpr s t1 = list_gtypexpr s t2.
Proof.
Admitted.

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

Lemma list_gtypref_sndeq: forall ft n pv0 gt ori0, nth_error (list_gtypref (N0,N0) ft false) n = Some (pv0, gt, ori0) -> (forall r, (exists pv, nth_error (list_gtypref r ft false) n = Some (pv, gt, ori0))).
Proof.
Admitted.

Lemma list_gtypref_correct : forall r tmap ft ori n pv gt ori0, type_of_ref r tmap = Some (ft, ori) -> nth_error (list_gtypref r ft false) n = Some (pv, gt, ori0) -> type_of_ref pv tmap = Some (Gtyp (gt), ori0).
Proof.
Admitted.

Lemma split_expr_type_correct : forall expr newtm(*, match expr with
  | Eref (Eid ref_src) => (*forall ft ori, type_of_ref ref_src newtm = Some (ft, ori) -> 
    forall n, match nth_error (list_gtypref ref_src ft ori) n with
    | Some (ref0, gt, ori0) => type_of_ref ref0 newtm = Some (Gtyp gt, ori0)
    | _ => true
    end*) true
  | Eref _ => true
  | _ => forall *)rhs_expr_ls t_expr, type_of_expr expr newtm = Some t_expr -> list_gtypexpr expr t_expr = Some rhs_expr_ls ->
    forall n, match nth_error (list_gtypref (0%num, 0%num) t_expr false) n, nth_error rhs_expr_ls n with
    | Some (_, gt, _), Some texpr => type_of_expr texpr newtm = Some (Gtyp gt)
    | _, _ => true
    end
  (*end*).
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
    apply Hs1 with (rhs_expr_ls := el1) (n:= n) in Hs1e; try done; clear Hs1.
    move => Hs1e'.
    apply Hs2 with (rhs_expr_ls := el2) (n:= n) in Hs2e; try done; clear Hs2.
    case Hs1n : (nth_error (list_gtypref (0%num, 0%num) t1 false) n) => [[[pv1 tt1] ori1]|]; rewrite Hs1n in Hs1e.
    case Hs2n : (nth_error (list_gtypref (0%num, 0%num) t2 false) n) => [[[pv2 tt2] ori2]|]; rewrite Hs2n in Hs2e.
    case Hten : (nth_error (list_gtypref (0%num, 0%num) t_expr false) n) => [[[tpv gte] ori0]|]; try done.
    apply find_mux_types_n with (n := n) (tt1 := (pv1, tt1, ori1)) (tt2 := (pv2, tt2, ori2)) (tte := (tpv, gte, ori0)) in Hte; try done.
    simpl in Hte; clear Hc.
    assert (exists e1, nth_error el1 n = Some e1).
    admit. (* t_expr 和 t1 满足ftype_equiv，由Hs1n 和 Hsplit1知el1的长度小于n *)
    destruct H as [e1 He1].
    assert (exists e2, nth_error el2 n = Some e2).
    admit.
    destruct H as [e2 He2].
    rewrite He1 in Hs1e; rewrite He2 in Hs2e.
    apply combine_mux_expr_n with (n := n) (el1 := el1) (el2 := el2) (e1 := e1) (e2 := e2) in Hsplit; try done.
    rewrite Hsplit in Hrhsn; clear Hsplit.
    inversion Hrhsn; clear Hrhsn H0.
    simpl.
    rewrite Hce Hcf Hs1e Hs2e.
    simpl; rewrite Hte; done.
    admit. (* not None *)
    admit. (* not None *)
    specialize ftype_equiv_split_eq with (s := s2) (t1 := t_expr) (t2 := t2); intro.
    rewrite H in Hsplit2.
    done.
    apply mux_expr_type_equiv with (c := c) (s1 := s1) (s2 := s2) (te := t_expr) (te1 := t1) (te2 := t2) in Hte'; try done.
    move : Hte' => [_ Hte']; done.
    specialize ftype_equiv_split_eq with (s := s1) (t1 := t_expr) (t2 := t1); intro.
    rewrite H in Hsplit1.
    done.
    apply mux_expr_type_equiv with (c := c) (s1 := s1) (s2 := s2) (te := t_expr) (te1 := t1) (te2 := t2) in Hte'; try done.
    move : Hte' => [Hte' _]; done.
    admit. (* not None *)
  - (* case2 : c 为 uint_implicit1 *)
    admit.

  (* validif *)
  admit. 

  (* ref *)
  intros ref.
  intros tmap rhs_expr_ls t_expr Hte Hsplit.
  simpl in Hsplit.
  case Href : ref => [r|||]; rewrite Href in Hsplit; try discriminate.
  inversion Hsplit; clear Hsplit H0.
  simpl in Hte; rewrite Href in Hte. 
  intros n.
  case Ht : (type_of_ref r tmap) => [[ft ori]|]; rewrite Ht in Hte; try discriminate; inversion Hte; rewrite H0 in Ht; clear Hte H0 ft.
  case Hfind : (nth_error (list_gtypref (0%num, 0%num) t_expr false) n) => [[[pv0 gt] ori0]|]; try done.
  specialize list_gtypref_sndeq with (r := r); intro.
  apply H in Hfind; clear H; destruct Hfind as [pv Hfind].
  rewrite nth_error_map Hfind; simpl.
  apply list_gtypref_correct with (tmap := tmap) (ori := ori) in Hfind; try done; rewrite Hfind //.
Admitted.

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
  case Hnt' : nt'; rewrite Hnt' in Hl Htl; try discriminate; inversion Hl; simpl; try done.
  case Hnt' : nt'; rewrite Hnt' in Hl Htl; try discriminate; inversion Hl; simpl; try done.
  case Hnt' : nt'; rewrite Hnt' in Hl Htl; try discriminate; inversion Hl; simpl; try done.
  case Hnt' : nt'; rewrite Hnt' in Hl Htl; try discriminate; inversion Hl; simpl; try done.

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

Lemma type_of_expr_eq : forall pv el tmap newtm, InferWidth_fun pv el tmap = Some newtm -> forall expr, expr \in el -> type_of_expr expr tmap = type_of_expr expr newtm.
Proof.
Admitted.

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
  apply type_of_expr_eq with (expr := expr) in Hinfer'; try done; rewrite -Hinfer'; clear Hinfer'.
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
Admitted.

Lemma list_fsteq : forall ref_tgt tgt v_tgt ori, In v_tgt (list_gtypref ref_tgt tgt ori) -> ref_tgt.1 = v_tgt.1.1.1.
Proof.
Admitted.

Lemma list_typeq ref_tgt : forall tmap t_tgt ori n pv0 gt ori0, type_of_ref ref_tgt tmap = Some (t_tgt, ori) -> nth_error (list_gtypref ref_tgt t_tgt ori) n = Some (pv0, gt, ori0) -> type_of_ref pv0 tmap = Some (Gtyp gt, ori).
Proof.
Admitted.

Lemma infernotin_eq : forall pv inferorder var2exprs tmap newtm, pv \notin inferorder -> InferWidths_fun inferorder var2exprs tmap = Some newtm ->
type_of_ref pv newtm = type_of_ref pv tmap /\ (match CEP.find pv var2exprs with
                                              | Some el => forall e, e \in el -> type_of_expr e newtm = type_of_expr e tmap
                                              |  _ => true
                                              end). 
Proof.
Admitted.

Lemma preexpr_in: forall ps ss tmap newtm var2exprs ref_tgt t_tgt ori_tgt n pv0 gt ori0 expr, ports_stmts_tmap' ps ss = Some (tmap, var2exprs) -> type_of_ref ref_tgt newtm = Some (t_tgt, ori_tgt) -> 
  Qin (Sfcnct (Eid ref_tgt) expr) ss -> nth_error (list_gtypref ref_tgt t_tgt ori_tgt) n = Some (pv0, gt, ori0) -> 
  match expr with
  | Eref (Eid ref_src) => forall t_src ori_src pv1 gte ori1 el, type_of_ref ref_src newtm = Some (t_src, ori_src) -> nth_error (list_gtypref ref_src t_src ori_src) n = Some (pv1, gte, ori1) -> 
                          if ori0 then CEP.find pv1 var2exprs = Some el -> (Eref (Eid pv0)) \in el 
                            else CEP.find pv0 var2exprs = Some el -> (Eref (Eid pv1)) \in el 
  | Eref _ => true
  | _ => forall texpr t_expr rhs_expr_ls el, CEP.find pv0 var2exprs = Some el -> type_of_expr expr newtm = Some t_expr -> list_gtypexpr expr t_expr = Some rhs_expr_ls -> nth_error rhs_expr_ls n = Some texpr -> texpr \in el
  end.
Proof.
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

  generalize Hte; apply split_expr_type_correct with (rhs_expr_ls := rhs_expr_ls) (n := n) in Hte; try done; rewrite Hrhs in Hte; intro Hte'.
  case Htexpr : (nth_error rhs_expr_ls n) => [texpr|]; rewrite Htexpr in Hte.

  (*specialize split_expr_type_correct with (expr := expr); intro H0; rewrite He in H0; rewrite -He in H0.
  generalize Hte; apply H0 with (rhs_expr_ls := rhs_expr_ls) (n := n) in Hte; try done; rewrite Hrhs in Hte; intro Hte'; clear H0.
  case Htexpr : (nth_error rhs_expr_ls n) => [texpr|]; rewrite Htexpr in Hte.*)
  assert (Hin' : texpr \in el).
  rewrite Href in Hin.
  apply preexpr_in with (ps := ps) (ss := ss) (tmap := tmap) (newtm := newtm) (var2exprs := var2exprs) (expr := expr) in Hlhs; try done.
  rewrite He in Hlhs; rewrite -He in Hlhs; move : Hel Hte' Hsplit Htexpr; apply Hlhs.
  admit. (* 一般expr一定是passive *)
  apply InferWidth_fun_correct with (pv := pv0) (el := el) (tmap := tmap') (newtm := newtm') (expr := texpr) in Hinfer; try done.
  generalize Htr; rewrite /type_of_ref in Htr; case Hcheckt : (CEP.find (ref_tgt.1, 0%num) newtm) => [[checkt ori_c]|]; rewrite Hcheckt in Htr; try discriminate; intro Htr'.
  generalize Hlhs; apply nth_error_In in Hlhs; apply list_fsteq in Hlhs; simpl in Hlhs.
  intro Hlhs'; generalize Hlhs'; apply list_typeq with (tmap := newtm) in Hlhs'; try done.
  intro Hlhs0; rewrite /type_of_ref -Hlhs in Hlhs'. rewrite -Hlhs in Hinfer.
  assert (exists checkt' ori_c', CEP.find (ref_tgt.1, 0%num) newtm' = Some (checkt', ori_c')).
  admit. (* 由 Hcheckt *)
  destruct H0 as [checkt' [ori_c' Htgt0]]; rewrite Htgt0 in Hinfer; rewrite Hcheckt in Hlhs'.
  assert (exists nt ori', ft_find_sub checkt' pv0.2 false = Some (nt, ori')).
  admit. (* 由 Hlhs' *)
  destruct H0 as [nt [ori' Hsub0]]; rewrite Hsub0 in Hinfer.
  apply infernotin_eq with (var2exprs := var2exprs) (tmap := newtm') (newtm := newtm) in Horder2; try done; move : Horder2 => [Horder2 Horder2'].
  rewrite /type_of_ref -Hlhs Htgt0 Hcheckt in Horder2; rewrite Horder2 in Hlhs'; rewrite Hlhs' in Hsub0; inversion Hsub0; clear Hsub0.
  rewrite -H1 in Hinfer; clear H1 nt H2 ori'.
  rewrite Hel in Horder2'; specialize Horder2' with (e := texpr); apply Horder2' in Hin'; rewrite -Hin' Hte in Hinfer; clear Horder2' Hin'.
  assert (fgtyp_equiv gt gte).
  move : Heq Hlhs0 Hrhs; apply listgtyp_eq.
  apply Hinfer in H0; clear Hinfer; rewrite /connect_fgtyp_compatible in H0.
  move /andP : H0 => [_ H0]; rewrite Himpli in H0; done.
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
    apply preexpr_in with (ps := ps) (ss := ss) (tmap := tmap) (newtm := newtm) (var2exprs := var2exprs) (expr := expr) in Hlhs; try done.
    rewrite He Href0 in Hlhs; apply Hlhs with (pv1 := pv_src) (gte := gt_src) (ori1 := ori_src0) (el := el) in Hsrc; try done; clear Hlhs. 
    rewrite Hflip in Hsrc; apply Hsrc in Hel; clear Hsrc; done.
    rewrite He Href0 //.
    apply InferWidth_fun_correct with (pv := pv_src) (el := el) (tmap := tmap') (newtm := newtm') (expr := Eref (Eid pv_tgt)) in Hinfer; try done.
    generalize Hsrc; rewrite /type_of_ref in Hsrc; case Hcheckt : (CEP.find (ref_src.1, 0%num) newtm) => [[checkt ori_c]|]; rewrite Hcheckt in Hsrc; try discriminate; intro Hsrc'.
    generalize Hrhs; apply nth_error_In in Hrhs; apply list_fsteq in Hrhs; simpl in Hrhs.
    intro Hrhs'; generalize Hrhs'; apply list_typeq with (tmap := newtm) in Hrhs'; try done.
    intro Hrhs0; rewrite /type_of_ref -Hrhs in Hrhs'. rewrite -Hrhs in Hinfer.
    assert (exists checkt' ori_c', CEP.find (ref_src.1, 0%num) newtm' = Some (checkt', ori_c')).
    admit. (* 由 Hcheckt *)
    destruct H0 as [checkt' [ori_c' Hsrc0]]; rewrite Hsrc0 in Hinfer; rewrite Hcheckt in Hrhs'.
    assert (exists nt ori', ft_find_sub checkt' pv_src.2 false = Some (nt, ori')).
    admit. (* 由 Hrhs' *)
    destruct H0 as [nt [ori' Hsub0]]; rewrite Hsub0 in Hinfer.
    apply infernotin_eq with (var2exprs := var2exprs) (tmap := newtm') (newtm := newtm) in Horder2; try done; move : Horder2 => [Horder2 Horder2'].
    rewrite /type_of_ref -Hrhs Hcheckt Hrhs' Hsrc0 in Horder2; rewrite -Horder2 in Hsub0; inversion Hsub0; clear Hsub0.
    rewrite -H1 in Hinfer; clear H1 nt H2 ori'.
    rewrite Hel in Horder2'; specialize Horder2' with (e := Eref (Eid pv_tgt)); apply Horder2' in Hin'; rewrite -Hin' in Hinfer; clear Horder2' Hin'.
    simpl in Hinfer.
    generalize Htgt; rewrite /type_of_ref in Htgt; case Hcheckt0 : (CEP.find (ref_tgt.1, 0%num) newtm) => [[checkt0 ori_c0]|]; rewrite Hcheckt0 in Htgt; try discriminate; intro Htgt'.
    generalize Hlhs; apply nth_error_In in Hlhs; apply list_fsteq in Hlhs; simpl in Hlhs.
    intro Hlhs'; generalize Hlhs'; apply list_typeq with (tmap := newtm) in Hlhs'; try done; rewrite Hlhs' in Hinfer; intro Hlhs0.
    assert (fgtyp_equiv gt_src gt_tgt).
    apply ftype_equiv_comm in Heq; move : Heq Hrhs0 Hlhs0; apply listgtyp_eq.
    apply Hinfer in H0; clear Hinfer; rewrite /connect_fgtyp_compatible in H0.
    move /andP : H0 => [_ H0]; rewrite Himpli in H0; done.
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
    apply preexpr_in with (ps := ps) (ss := ss) (tmap := tmap) (newtm := newtm) (var2exprs := var2exprs) (expr := expr) in Hlhs; try done.
    rewrite He Href0 in Hlhs; apply Hlhs with (pv1 := pv_src) (gte := gt_src) (ori1 := ori_src0) (el := el) in Hsrc; try done; clear Hlhs. 
    rewrite Hflip in Hsrc; apply Hsrc in Hel; clear Hsrc; done.
    rewrite He Href0 //.
    apply InferWidth_fun_correct with (pv := pv_tgt) (el := el) (tmap := tmap') (newtm := newtm') (expr := Eref (Eid pv_src)) in Hinfer; try done.
    generalize Htgt; rewrite /type_of_ref in Htgt; case Hcheckt0 : (CEP.find (ref_tgt.1, 0%num) newtm) => [[checkt0 ori_c0]|]; rewrite Hcheckt0 in Htgt; try discriminate; intro Htgt'.
    generalize Hlhs; apply nth_error_In in Hlhs; apply list_fsteq in Hlhs; simpl in Hlhs.
    intro Hlhs'; generalize Hlhs'; apply list_typeq with (tmap := newtm) in Hlhs'; try done.
    intro Hlhs0; rewrite /type_of_ref -Hlhs in Hlhs'. rewrite -Hlhs in Hinfer.
    assert (exists checkt' ori_c', CEP.find (ref_tgt.1, 0%num) newtm' = Some (checkt', ori_c')).
    admit. (* 由 Hcheckt0 *)
    destruct H0 as [checkt' [ori_c' Htgt0]]; rewrite Htgt0 in Hinfer; rewrite Hcheckt0 in Hlhs'.
    assert (exists nt ori', ft_find_sub checkt' pv_tgt.2 false = Some (nt, ori')).
    admit. (* 由 Hrhs' *)
    destruct H0 as [nt [ori' Hsub0]]; rewrite Hsub0 in Hinfer.
    apply infernotin_eq with (var2exprs := var2exprs) (tmap := newtm') (newtm := newtm) in Horder2; try done; move : Horder2 => [Horder2 Horder2'].
    rewrite /type_of_ref -Hlhs Hcheckt0 Hlhs' Htgt0 in Horder2; rewrite -Horder2 in Hsub0; inversion Hsub0; clear Hsub0.
    rewrite -H1 in Hinfer; clear H1 nt H2 ori'.
    rewrite Hel in Horder2'; specialize Horder2' with (e := Eref (Eid pv_src)); apply Horder2' in Hin'; rewrite -Hin' in Hinfer; clear Horder2' Hin'.
    simpl in Hinfer.
    generalize Hsrc; rewrite /type_of_ref in Hsrc; case Hcheckt : (CEP.find (ref_src.1, 0%num) newtm) => [[checkt ori_c]|]; rewrite Hcheckt in Hsrc; try discriminate; intro Hsrc'.
    generalize Hrhs; apply nth_error_In in Hrhs; apply list_fsteq in Hrhs; simpl in Hrhs.
    intro Hrhs'; generalize Hrhs'; apply list_typeq with (tmap := newtm) in Hrhs'; try done.
    rewrite Hrhs' in Hinfer; intro Hrhs0.
    assert (fgtyp_equiv gt_tgt gt_src).
    move : Heq Hlhs0 Hrhs0; apply listgtyp_eq.
    apply Hinfer in H0; clear Hinfer; rewrite /connect_fgtyp_compatible in H0.
    move /andP : H0 => [_ H0]; rewrite Himpli in H0; done.
    admit. (* 不是None *)
    admit. (* 不是None *)
  case Hrhs : (nth_error (list_gtypref ref_src t_src ori_src) n); try done.
Admitted.

Lemma InferWidths_trans_correct : forall pp ss nps nss newtm vm' vm'' vm (*pv*), (*InferWidths_stage1 (FInmod pv pp ss) = Some newtm ->*) InferWidths_transps pp newtm = Some nps -> InferWidths_transss ss newtm = Some nss ->
make_ps_implicit vm' (CEP.empty vertex_type) pp = Some vm'' -> make_ss_implicit vm' vm'' ss = Some vm -> ports_stmts_tmap pp ss vm = Some newtm.
Proof.
  (*rewrite /ports_stmts_tmap.
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
  rewrite /Sem; rewrite /InferWidths_m in Hinfer.
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
  intro Hps.
  case Hps' : (ports_stmts_tmap nps nss vm') => [tmap|]; rewrite Hps' in Hps; try done.
  assert (exists tmap', ports_stmts_tmap pp ss vm = Some tmap').
  admit. (* 由 Hps' *)
  destruct Hps as [vm0 [ct0 [Hports Hstmts]]].
  destruct H as [tmap' Hps]; rewrite Hps.
  generalize Htransp; apply InferWidths_trans_correct with (ss := ss) (nss := nss) (vm' := vm') (vm'' := vm'') (vm := vm) in Htransp; try done.
  rewrite Hps in Htransp; inversion Htransp; clear Htransp; rewrite H0 in Hps; clear H0 tmap'; intro Htransp.
  clear Hports Hstmts vm0 ct0 Hps' tmap. (* vm'全为expli，不包括任何前提 *)

  (*InferWidths_transps pp newtm = Some nps -> InferWidths_transss ss newtm = Some nss ->
  make_ps_implicit vm' (CEP.empty vertex_type) pp = Some vm'' -> make_ss_implicit vm' vm'' ss = Some vm -> ports_stmts_tmap pp ss vm = Some newtm *)

  (* ports_stmts_tmap pp ss vm = Some tmap' -> type_of_ref pv tmap' = Some () -> 
     code_type_find_vm_widths (type reg) pv vm = Some () *)


  exists vm''; exists (CEP.empty def_expr). (* 不是empty，但先不check任何关于connection *)
  split.
  - admit.
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

    specialize InferWidths_fun_correct with (pp := pp) (ss := ss) (inferorder := inferorder) (var2exprs := var2exprs) (tmap0 := tmap0) (newtm := newtm); intro Hinfer.
    rewrite Hinfer1 Hps0 in Hinfer.
    move : Hpss Himplivm Hinfer.
    clear.
    move : ss vm' vm pmap tmap2 vm'' newtm.
    elim.
    - simpl; intros; inversion Himplivm; apply CEP.Lemmas.Equal_refl.
    - intros s st IH vm0 vm pmap tmap2 nvm newtm Hmaps Himplis Hinfer.
      simpl; simpl in Hmaps; simpl in Himplis.
      case Hmap : (stmt_tmap (pmap, pmap) s vm) => [[tmap' tmap2']|]; rewrite Hmap in Hmaps; try discriminate.
      case Himpli : (make_s_implicit vm0 nvm s) => [vm'|]; rewrite Himpli in Himplis; try discriminate.
      exists vm'; split.
      - clear IH.
        (*apply InferWidths_fun_correct with (pp := pp) (ss := (Qcons s st)) (hfs := s) in Hinfer1; try done.*)
        specialize Hinfer with (hfs := s).
        case Hs : s => [|r t|r reg|||r e|r e|r|c s1 s2]; rewrite Hs in Hmap Himpli Hinfer; simpl; try done.
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
          case Hr : r => [ref|||]; rewrite Hr in Hs Hinfer.
          case He : e => [t c| c e1 | u e1 | op e1 e2 | c e1 e2 | c e1 | r2 ]; rewrite He in Hs Hinfer.
          - (* expr *)
          1,2,3,4,5,6 : rewrite -He; rewrite -He in Hinfer; clear He Hs Hr.
          1,2,3,4,5,6 : case Hreft : (type_of_ref ref newtm) => [[t_tgt ori]|]; rewrite Hreft in Hinfer.
          1,3,5,7,9,11 : case Hexprt : (type_of_expr e newtm) => [t_expr|]; rewrite Hexprt in Hinfer.
          1,3,5,7,9,11 : apply Hinfer; try done.
          admit. (* Qin_cons *)
          admit. (* Hypo *)
          admit. (* Qin_cons *)
          admit. (* Hypo *)
          admit. (* Qin_cons *)
          admit. (* Hypo *)
          admit. (* Qin_cons *)
          admit. (* Hypo *)
          admit. (* Qin_cons *)
          admit. (* Hypo *)
          admit. (* Qin_cons *)
          admit. (* Hypo *)
          admit. (* None则有错 *)
          admit. (* None则有错 *)
          admit. (* None则有错 *)
          admit. (* None则有错 *)
          admit. (* None则有错 *)
          admit. (* None则有错 *)
          admit. (* None则有错 *)
          admit. (* None则有错 *)
          admit. (* None则有错 *)
          admit. (* None则有错 *)
          admit. (* None则有错 *)
          admit. (* None则有错 *)
          - (* ref *)
          case Hr2 : r2 => [ref_src|||]; rewrite Hr2 in Hinfer.
          case Hreft : (type_of_ref ref newtm) => [[t_tgt ori]|]; rewrite Hreft in Hinfer.
          case Hexprt : (type_of_ref ref_src newtm) => [[t_expr p_expr]|]; rewrite Hexprt in Hinfer; try done.
          apply Hinfer; try done.
          admit. (* Qin_cons *)
          admit. (* Hypo *)
          admit. (* None则有错 *)
          admit. (* None则有错 *)
          admit. (* no subfield *)
          admit. (* no subindex *)
          admit. (* no subaccess *)
          admit. (* no subfield *)
          admit. (* no subindex *)
          admit. (* no subaccess *)
        - (* when *)
          admit.
      - apply IH with (vm' := vm0) (pmap := tmap') (tmap2 := tmap2); try done.
        admit.
        intros.
        apply Hinfer with (hfs := hfs) in H; try done.
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

Lemma InferWidths_trans_correct' : forall v vm' t' F' mv ps ss newtm ft ori, CEP.find v vm' = Some t' -> Sem F' vm' -> InferWidths_stage2 (FInmod mv ps ss) newtm = Some F' ->
  type_of_ref v newtm = Some (ft, ori) -> ft = (Gtyp (type_of_vx t')).
Proof.
Admitted.

Lemma geq_conj2mux : forall tmap (gt initt : fgtyp) (el : seq HiFP.hfexpr) eftl (nt : fgtyp), (forall (texpr : HiFP.hfexpr) (te : fgtyp), texpr \in el -> type_of_expr texpr tmap = Some (Gtyp te) -> ((sizeof_fgtyp gt) >= (sizeof_fgtyp te))) ->
  fil_ftlist [seq type_of_expr e tmap | e <- el] = Some eftl -> sizeof_fgtyp initt = 0 -> max_ftlist eftl initt = Some nt -> ((sizeof_fgtyp gt) >= (sizeof_fgtyp nt)).
Proof.
Admitted.

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

Lemma Sem_wdgeqmax ss : forall vm_old vm_new tmap, Sem_frag_stmts vm_old ss vm_new tmap -> (forall v t el, CEP.find v vm_new = Some t -> 
  find_sub_exprs v ss tmap = Some el -> (forall e te , e \in el -> type_of_expr e tmap = Some (Gtyp te) -> sizeof_fgtyp (type_of_vx t) >= sizeof_fgtyp te)).
Proof.
Admitted.

Lemma Semgeqinfer : forall pp ss mv vm tmap newtm, Sem (FInmod mv pp ss) vm -> ports_stmts_tmap pp ss vm = Some tmap -> InferWidths_stage1 (FInmod mv pp ss) = Some newtm -> (forall e t0 t1 , type_of_expr e tmap = Some (Gtyp t0) -> type_of_expr e newtm = Some (Gtyp t1) -> sizeof_fgtyp t0 >= sizeof_fgtyp t1).
Proof.
Admitted.

Lemma find_sub_exprs_correct : forall v ps ss tmap var2exprs, ports_stmts_tmap' ps ss = Some (tmap, var2exprs) -> CEP.find v var2exprs = find_sub_exprs v ss tmap.
Proof.
Admitted.

Lemma ft_find_sub_orieq : forall init v a b nt nt0, ft_find_sub init v false = Some a -> ft_set_sub init nt v = Some nt0 -> ft_find_sub nt0 v false = Some b -> a.2 = b.2.
Proof.
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
  assert (exists order1 order2, inferorder = order1 ++ (v :: order2) /\ ~ v \in order1 /\ ~ v \in order2).
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
  assert (Himpli' : not_implicit initt = false). 
  admit. (* drawg只考虑implicit *)
  case Hmax : (max_ftlist eftl initt) => [nt|]; rewrite Hmax in Hinfer1; try discriminate.
  case Hset : (ft_set_sub init nt v.2) => [nt0|]; rewrite Hset in Hinfer1; try discriminate. 
  inversion Hinfer1; clear Hinfer1.
  apply InferWidths_trans_correct' with (F' := F') (mv := mv) (ps := ps) (ss := ss) (newtm := newtm) (ft := Gtyp nt) (ori := ori) in Ht'; try done.
  inversion Ht'; clear Ht'; rewrite -H1; clear H1.
  generalize Hsem; rewrite /Sem in Hsem.
  case Hpre0 : (ports_stmts_tmap ps ss vm) => [tmap0'|]; rewrite Hpre0 in Hsem; try done.
  destruct Hsem as [vm0 [ct0 [_ Hsems]]]; intro Hsem.
  apply geq_conj2mux with (tmap := tmap0) (initt := initt) (el := el) (eftl := eftl); try done.
  intros.
  assert (Hte : exists t0, type_of_expr texpr tmap0' = Some (Gtyp t0)).
  admit. (* tl中应全为gtyp expr *)
  destruct Hte as [t0 Hte].
  apply Semgeqinfer with (tmap := tmap0') (newtm := newtm) (e := texpr) (t0 := t0) (t1 := te) in Hsem; try done.
  apply Sem_wdgeqmax with (v := v) (t := t) (el := el) (e := texpr) (te := t0) in Hsems; try done.
  move : Hsem Hsems; apply leq_trans.
  generalize Hpre; apply find_sub_exprs_correct with (v := v) in Hpre; try done; rewrite -Hel Hpre.
  move : Hpre0.
  admit.
  move : H1 Hod2.
  admit. (* infer后面的部分不影响expr的type *)
  admit.
  assert (type_of_ref v newtm = type_of_ref v newtm').
  move : Horder2 Hinfer2'.
  admit.
  rewrite H /type_of_ref -H0 CEP.Lemmas.find_add_eq; clear H; try apply PVM.SE.eq_refl. 
  specialize set_find_sub with (checkt := init) (nt := nt) (n := v.2) (nt0 := nt0) (b := false); intro.
  generalize Hset; apply H in Hset; clear H; try done.
  intro Hset'; destruct Hset as [b0 Hset].
  apply ft_find_sub_orieq with (a := (Gtyp initt, ori)) (b := (Gtyp nt, b0)) in Hset'; try done; simpl in Hset'.
  rewrite -Hset' in Hset; clear Hset' b0; done.
  apply ft_set_sub_eq with (nt' := nt) (nt0 := nt0) in Hf; try done.
  simpl.
  apply max_ftlist_correct in Hmax; move : Hmax => [_ Hmax]; done.
  admit. (* None则有错 *)
  admit. (* None则有错 *)
  case Ht : (CEP.find v vm); try done.
Admitted.
