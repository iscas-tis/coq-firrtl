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

Fixpoint list_gtypref (v : ProdVarOrder.t) (ft : ftype) (ori : HiF.forient) : seq (ProdVarOrder.t * fgtyp * HiF.forient) :=
match ft with
   | Gtyp gt => [::(v, gt, ori)]
   | Atyp atyp n => list_gtypref (v.1, N.add v.2 1%num) atyp ori
   | Btyp ff => list_gtypref_ff v ff ori
   end
with list_gtypref_ff (v : ProdVarOrder.t) (ff : ffield) (ori : HiF.forient) : seq (ProdVarOrder.t * fgtyp * HiF.forient) :=
   match ff with
   | Fnil => [::]
   | Fflips _ fl ft ff' => match fl, ori with
                        | Nflip, _ 
                        | Flipped, HiF.Duplex => list_gtypref (v.1, N.add v.2 1%num) ft ori ++ list_gtypref_ff (v.1, N.add v.2 (N.of_nat (num_ref ft + 1))) ff' ori
                        | Flipped, HiF.Sink => list_gtypref (v.1, N.add v.2 1%num) ft HiF.Source ++ list_gtypref_ff (v.1, N.add v.2 (N.of_nat (num_ref ft + 1))) ff' ori
                        | Flipped, HiF.Source => list_gtypref (v.1, N.add v.2 1%num) ft HiF.Sink ++ list_gtypref_ff (v.1, N.add v.2 (N.of_nat (num_ref ft + 1))) ff' ori
                        | _, _ => [::]
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

Fixpoint make_gtyp_implicit (vm nvm : CEP.t vertex_type) (tl : seq (ProdVarOrder.t * fgtyp * HiF.forient)) : option (CEP.t vertex_type) := 
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
   | Finput v t => let tl := list_gtypref v t HiF.Source in
                   make_gtyp_implicit vm nvm tl
   | Foutput v t => let tl := list_gtypref v t HiF.Sink in
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
  | Swire v t => let tl := list_gtypref v t HiF.Duplex in
                 make_gtyp_implicit vm nvm tl
  | Sreg v r => let tl := list_gtypref v (type r) HiF.Duplex in
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

Fixpoint ft_find_sub (checkt : ftype) (num : N) (ori : HiF.forient) : option (ftype * HiF.forient) :=
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
with ft_find_sub_f (ff : ffield) (num : N) (ori : HiF.forient) : option (ftype * HiF.forient) :=
  match ff, ori with
  | Fflips _ Nflip ft ff', _ 
  | Fflips _ Flipped ft ff', HiF.Duplex => if num == 1%num (* 找到被更新的标号, 所对应的field *)
                              then Some (ft, ori)
                              else if (N.to_nat num) > (num_ref ft) (* 不在该field中, 找下一个field *)
                                  then ft_find_sub_f ff' (N.of_nat ((N.to_nat num) - (num_ref ft))) ori
                              else (* 在field v0中 *)
                                  ft_find_sub ft (N.sub num 1%num) ori
   | Fflips _ Flipped ft ff', HiF.Source => if num == 1%num (* 找到被更新的标号, 所对应的field *)
                              then Some (ft, HiF.Sink)
                              else if (N.to_nat num) > (num_ref ft) (* 不在该field中, 找下一个field *)
                                  then ft_find_sub_f ff' (N.of_nat ((N.to_nat num) - (num_ref ft))) HiF.Source
                              else (* 在field v0中 *)
                                  ft_find_sub ft (N.sub num 1%num) HiF.Sink
   | Fflips _ Flipped ft ff', HiF.Sink => if num == 1%num (* 找到被更新的标号, 所对应的field *)
                              then Some (ft, HiF.Source)
                              else if (N.to_nat num) > (num_ref ft) (* 不在该field中, 找下一个field *)
                                  then ft_find_sub_f ff' (N.of_nat ((N.to_nat num) - (num_ref ft))) HiF.Sink
                              else (* 在field v0中 *)
                                  ft_find_sub ft (N.sub num 1%num) HiF.Source
  | _, _ => None
  end.
  
Definition type_of_ref (v : ProdVarOrder.t) (tmap : CEP.t (ftype * HiF.forient)) : option (ftype * HiF.forient) :=
  match CEP.find (fst v, N0) tmap with
  | Some (checkt, ori) => ft_find_sub checkt (snd v) ori
  | None => None
  end.

Fixpoint type_of_expr (expr : HiFP.hfexpr) (tmap: CEP.t (ftype * HiF.forient)) : option ftype_explicit :=
   (* Find the type of expression expr for reading.

   Similar to type_of_hfexpr in InferWidths *)
   match expr with
   | Econst t bs => match t with
                    | Fuint_implicit w => Some (exist ftype_not_implicit_width (Gtyp (Fuint w)) I)
                    | Fsint_implicit w => Some (exist ftype_not_implicit_width (Gtyp (Fsint w)) I)
                    | t => Some (exist ftype_not_implicit_width (Gtyp t) I)
                    end
   | Eref (Eid r) => match type_of_ref r tmap with
               | Some (t, HiF.Source)
               | Some (t, HiF.Duplex) => Some (make_ftype_explicit t)
               | _ => None
               end
   | Ecast AsUInt e1 => match type_of_expr e1 tmap with
                         | Some (exist (Gtyp (Fsint w)) _)
                         | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w)) I)
                         | Some (exist (Gtyp Fclock) _)
                         | Some (exist (Gtyp Freset) _)
                         | Some (exist (Gtyp Fasyncreset) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I)
                         | _ => None
                         end
   | Ecast AsSInt e1 => match type_of_expr e1 tmap with
                         | Some (exist (Gtyp (Fsint w)) _)
                         | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w)) I)
                         | Some (exist (Gtyp Fclock) _)
                         | Some (exist (Gtyp Freset) _)
                         | Some (exist (Gtyp Fasyncreset) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint 1)) I)
                         | _ => None
                         end
   | Ecast AsClock e1 => match type_of_expr e1 tmap with
                         | Some (exist (Gtyp _) _) => Some (exist ftype_not_implicit_width (Gtyp Fclock) I)
                         | _ => None
                         end
   | Ecast AsAsync e1 => match type_of_expr e1 tmap with
                         | Some (exist (Gtyp _) _) => Some (exist ftype_not_implicit_width (Gtyp Fasyncreset) I)
                         | _ => None
                         end
   | Eprim_unop (Upad n) e1 => match type_of_expr e1 tmap with
                                | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn w n))) I)
                                | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w n))) I)
                                | _ => None
                                end
   | Eprim_unop (Ushl n) e1 => match type_of_expr e1 tmap with
                                | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + n))) I)
                                | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w + n))) I)
                                | _ => None
                                end
   | Eprim_unop (Ushr n) e1 => match type_of_expr e1 tmap with
                                | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn (w - n) 1))) I)
                                | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn (w - n) 0))) I)
                                | _ => None
                                end
   | Eprim_unop Ucvt e1 => match type_of_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w)) I)
                            | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + 1))) I)
                            | _ => None
                            end
   | Eprim_unop Uneg e1 => match type_of_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _)
                            | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + 1))) I)
                            | _ => None
                            end
   | Eprim_unop Unot e1 => match type_of_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _)
                            | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w)) I)
                            | _ => None
                            end
   | Eprim_unop (Uextr n1 n2) e1 => match type_of_expr e1 tmap with
                                     | Some (exist (Gtyp (Fsint w)) _)
                                     | Some (exist (Gtyp (Fuint w)) _) =>
                                          if (n2 <= n1) && (n1 < w) then Some (exist ftype_not_implicit_width (Gtyp (Fuint (n1 - n2 + 1))) I)
                                                                    else None
                                     | _ => None
                                     end
   | Eprim_unop (Uhead n) e1 => match type_of_expr e1 tmap with
                                 | Some (exist (Gtyp (Fsint w)) _)
                                 | Some (exist (Gtyp (Fuint w)) _) =>
                                      if n <= w then Some (exist ftype_not_implicit_width (Gtyp (Fuint n)) I)
                                                else None
                                 | _ => None
                                 end
   | Eprim_unop (Utail n) e1 => match type_of_expr e1 tmap with
                                 | Some (exist (Gtyp (Fsint w)) _)
                                 | Some (exist (Gtyp (Fuint w)) _) =>
                                      if n <= w then Some (exist ftype_not_implicit_width (Gtyp (Fuint (w - n))) I)
                                                else None
                                 | _ => None
                                 end
   | Eprim_unop _ e1 => match type_of_expr e1 tmap with
                         | Some (exist (Gtyp (Fsint _)) _)
                         | Some (exist (Gtyp (Fuint _)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I)
                         | _ => None
                         end
   | Eprim_binop (Bcomp _) e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                                     | Some (exist (Gtyp (Fsint _)) _), Some (exist (Gtyp (Fsint _)) _)
                                     | Some (exist (Gtyp (Fuint _)) _), Some (exist (Gtyp (Fuint _)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I)
                                     | _, _ => None
                                     end
   | Eprim_binop Badd e1 e2
   | Eprim_binop Bsub e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w1 w2 + 1))) I)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn w1 w2 + 1))) I)
                                | _, _ => None
                                end
   | Eprim_binop Bmul e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w1 + w2))) I)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w1 + w2))) I)
                                | _, _ => None
                                end
   | Eprim_binop Bdiv e1 e2  => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                                 | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w1)) I)
                                 | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w1 + 1))) I)
                                 | _, _ => None
                                 end
   | Eprim_binop Brem e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                                 | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (minn w1 w2))) I)
                                 | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (minn w1 w2))) I)
                                 | _, _ => None
                                 end
   | Eprim_binop Bdshl e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                                 | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (2 ^ w2 + w1 - 1))) I)
                                 | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (2 ^ w2 + w1 - 1))) I)
                                 | _, _ => None
                                 end
   | Eprim_binop Bdshr e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                                 | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w1)) I)
                                 | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w1)) I)
                                 | _, _ => None
                                 end
   | Eprim_binop Bcat e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w1 + w2))) I)
                                | _, _ => None
                                end
   | Eprim_binop Band e1 e2
   | Eprim_binop Bor e1 e2
   | Eprim_binop Bxor e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w1 w2))) I)
                                | _, _ => None
                                end
   | Emux c e1 e2 => match type_of_expr c tmap, type_of_expr e1 tmap, type_of_expr e2 tmap with
                      | Some (exist (Gtyp (Fuint 1)) _), Some t1, Some t2 => ftype_mux t1 t2
                      | _, _, _ => None
                      end
   | Evalidif c e1 => match type_of_expr c tmap with
                      | Some (exist (Gtyp (Fuint 1)) _) => type_of_expr e1 tmap
                      | _ => None
                      end
   | _ => None
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
            | Some (exist (Gtyp Fasyncreset) _) =>
                (* rst_val needs to be constant. At least it cannot be the register itself.
                   Otherwise we do not check whether the value is actually constant. *)
                match type_of_expr rst_val (snd tmap_scope) with
                | Some _ => Some (CEP.add v (newt, HiF.Duplex) (fst tmap_scope), CEP.add v (newt, HiF.Duplex) (snd tmap_scope))
                | None => None (* something undefined or out-of-scope is accessed *)
                end
             | Some (exist (Gtyp (Fuint 1)) _) =>
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
    | None, Some (exist newt _) =>
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

Fixpoint check_connect_non_passive_type (t_tgt t_src : seq (ProdVarOrder.T * fgtyp * HiF.forient)) : bool :=
  match t_tgt, t_src with
  | nil, nil => true
  | (_, thd, HiF.Sink) :: ttl, (_, shd, HiF.Source) :: stl 
  | (_, thd, HiF.Sink) :: ttl, (_, shd, HiF.Duplex) :: stl 
  | (_, thd, HiF.Duplex) :: ttl, (_, shd, HiF.Duplex) :: stl 
  | (_, thd, HiF.Duplex) :: ttl, (_, shd, HiF.Source) :: stl => connect_fgtyp_compatible thd shd && check_connect_non_passive_type ttl stl
  | (_, thd, HiF.Source) :: ttl, (_, shd, HiF.Sink) :: stl 
  | (_, thd, HiF.Source) :: ttl, (_, shd, HiF.Duplex) :: stl 
  | (_, thd, HiF.Duplex) :: ttl, (_, shd, HiF.Sink) :: stl => connect_fgtyp_compatible shd thd && check_connect_non_passive_type ttl stl
  | _, _ => false
  end.

Fixpoint check_connect_type (t_tgt t_src : seq (ProdVarOrder.T * fgtyp * HiF.forient)) : bool :=
  match t_tgt, t_src with
  | nil, nil => true
  | (_, thd, _) :: ttl, (_, shd, _) :: stl => connect_fgtyp_compatible thd shd && check_connect_type ttl stl
  | _, _ => false
  end.

Definition connect_non_passive_type (ref_tgt ref_src : ProdVarOrder.T) (t_tgt t_src : ftype) (ori_tgt ori_src : HiF.forient) : Prop :=
  ftype_equiv t_tgt t_src && check_connect_non_passive_type (list_gtypref ref_tgt t_tgt ori_tgt) (list_gtypref ref_src t_src ori_src). 

Definition connect_type (ref : ProdVarOrder.T) (t_tgt t_src : ftype) (ori_tgt ori_src : HiF.forient) : Prop :=
  ftype_equiv t_tgt t_src && check_connect_type (list_gtypref ref t_tgt ori_tgt) (list_gtypref (N0, N0) t_src ori_src).

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
          | Some (ft_tgt, ori_tgt), Some (exist ft_src _) => connect_type ref ft_tgt ft_src ori_tgt HiF.Source
          | _, _ => False
          end
   | Sreg v reg =>
       match reset reg with
        | Rst _ rst_val => match CEP.find v tmap, type_of_expr rst_val tmap with
            | Some (newft, _), Some (exist rst_val_type _) => connect_type v newft rst_val_type HiF.Duplex HiF.Duplex
            | _, _ => false
            end
        | NRst => True (* type check newft: we only need to verify newft is passive *)
        end
   | Smem v mem => False (* ? *)
   | Sinst var1 var2 => False (* ? *)
   | Swhen cond ss_true ss_false =>
       if type_of_expr cond tmap is Some (exist (Gtyp (Fuint 1)) _)
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
  | Eref (Eid ref) => let refl := list_gtypref ref t HiF.Duplex in 
                        Some (map (fun tref => (Eref (Eid (fst (fst tref))))) refl)
  | Eref _ => None
  | Emux c e1 e2 => match list_gtypexpr e1 t, list_gtypexpr e2 t with
                  | Some el1, Some el2 => combine_mux_expr c el1 el2
                  | _ ,_ => None
                  end
  | _ => Some [:: expr_src] 
  end.

Fixpoint add_expr_connect_non_passive (el1 el2 : seq (ProdVarOrder.t * fgtyp * HiF.forient)) (var2exprs : CEP.t (seq HiFP.hfexpr)) : option (CEP.t (seq HiFP.hfexpr)) :=
  match el1, el2 with
  | nil, nil => Some var2exprs
  | (ref1, _, HiF.Sink) :: tl1, (ref2, _, HiF.Source) :: tl2 
  | (ref1, _, HiF.Sink) :: tl1, (ref2, _, HiF.Duplex) :: tl2 
  | (ref1, _, HiF.Duplex) :: tl1, (ref2, _, HiF.Duplex) :: tl2 
  | (ref1, _, HiF.Duplex) :: tl1, (ref2, _, HiF.Source) :: tl2 => 
                match CEP.find ref1 var2exprs with
                | Some ls => add_expr_connect_non_passive tl1 tl2 (CEP.add ref1 ((Eref (Eid ref2)) :: ls) var2exprs)
                | None => add_expr_connect_non_passive tl1 tl2 (CEP.add ref1 [::(Eref (Eid ref2))] var2exprs)
                end
  | (ref1, _, HiF.Source) :: tl1, (ref2, _, HiF.Sink) :: tl2 
  | (ref1, _, HiF.Duplex) :: tl1, (ref2, _, HiF.Sink) :: tl2 
  | (ref1, _, HiF.Source) :: tl1, (ref2, _, HiF.Duplex) :: tl2 => 
                match CEP.find ref2 var2exprs with
                | Some ls => add_expr_connect_non_passive tl1 tl2 (CEP.add ref2 ((Eref (Eid ref1)) :: ls) var2exprs)
                | None => add_expr_connect_non_passive tl1 tl2 (CEP.add ref2 [::(Eref (Eid ref1))] var2exprs)
                end
  | _, _ => None
  end.

Fixpoint add_expr_connect (el1 : seq (ProdVarOrder.t * fgtyp * HiF.forient)) (el2 : seq HiFP.hfexpr) (var2exprs : CEP.t (seq HiFP.hfexpr)) : option (CEP.t (seq HiFP.hfexpr)) :=
  match el1, el2 with
  | nil, nil => Some var2exprs
  | (ref1, _, HiF.Sink) :: tl1, hd2 :: tl2 
  | (ref1, _, HiF.Duplex) :: tl1, hd2 :: tl2 => 
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
    | Some (ft_tgt, ori_tgt), Some (exist ft_src _) =>  match list_gtypref ref ft_tgt ori_tgt, list_gtypexpr expr ft_src with
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
            | Some _, Some (exist ft_src _) => match list_gtypref v (type reg) HiF.Duplex, list_gtypexpr rst_val ft_src with
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
                | None, Some (exist newt _) => match list_gtypref v newt HiF.Sink, list_gtypexpr expr newt with
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
  | Sreg v r => Some (map (fun temp => (fst (fst temp))) (list_gtypref v (type r) HiF.Duplex))
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

Fixpoint fil_ftlist (l : seq (option ftype_explicit)) : option (seq fgtyp) :=
  match l with
  | nil => Some [::]
  | (Some (exist (Gtyp gt) _)) :: tl => match fil_ftlist tl with
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
                | Some (init, ori) => match ft_find_sub init (snd v) ori with
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
Admitted.

Lemma check_connect_non_passive_type_correct : forall ft te, (forall n, 
  match nth_error ft n, nth_error te n with
  | Some (_, thd, HiF.Sink), Some (_, shd, HiF.Source)
  | Some (_, thd, HiF.Sink), Some (_, shd, HiF.Duplex)
  | Some (_, thd, HiF.Duplex), Some (_, shd, HiF.Duplex)
  | Some (_, thd, HiF.Duplex), Some (_, shd, HiF.Source) => connect_fgtyp_compatible thd shd
  | Some (_, thd, HiF.Source), Some (_, shd, HiF.Sink)
  | Some (_, thd, HiF.Source), Some (_, shd, HiF.Duplex)
  | Some (_, thd, HiF.Duplex), Some (_, shd, HiF.Sink)=> connect_fgtyp_compatible shd thd
  | None, None => true
  |  _, _ => false
  end) -> check_connect_non_passive_type ft te.
Proof.
Admitted.

Lemma listgtyp_eq t_tgt t_expr : forall n ref0 ref1 ori0 ori1 ori2 ori3 pv0 pv1 gt gte, ftype_equiv t_tgt t_expr -> nth_error (list_gtypref ref0 t_tgt ori0) n =
  Some (pv0, gt, ori2) -> nth_error (list_gtypref ref1 t_expr ori1) n = Some (pv1, gte, ori3) -> fgtyp_equiv gt gte.
Proof.
Admitted.

Lemma infer_cons_order : forall order1 order2 var2exprs tmap tmap' newtm, InferWidths_fun (order1 ++ order2) var2exprs tmap = Some newtm -> InferWidths_fun order1 var2exprs tmap = Some tmap' ->
  InferWidths_fun order2 var2exprs tmap' = Some newtm.
Proof.
Admitted.

Lemma split_expr_type_correct : forall expr rhs_expr_ls t_expr newtm (p : ftype_not_implicit_width t_expr), type_of_expr expr newtm = Some (exist ftype_not_implicit_width t_expr p) -> list_gtypexpr expr t_expr = Some rhs_expr_ls ->
  forall n, match nth_error (list_gtypref (0%num, 0%num) t_expr HiF.Source) n, nth_error rhs_expr_ls n with
            | Some (_, gt, _), Some texpr => exists p0, type_of_expr texpr newtm = Some (exist ftype_not_implicit_width (Gtyp gt) p0)
            | _, _ => true
            end.
Proof.
Admitted.

Lemma InferWidth_fun_correct : forall pv el tmap newtm, InferWidth_fun pv el tmap = Some newtm -> forall expr, expr \in el -> 
      match CEP.find (fst pv, N0) newtm with
      | Some (checkt, ori) => match ft_find_sub checkt pv.2 ori, type_of_expr expr newtm with
                              | Some (Gtyp nt, _), Some (exist (Gtyp te) p) => fgtyp_equiv nt te -> connect_fgtyp_compatible nt te
                              | _,_ => true
                              end
      | _ => true
      end.
Proof.
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

Lemma preexpr_in: forall ps ss tmap newtm var2exprs ref_tgt t_tgt ori expr texpr t_expr rhs_expr_ls pe n pv0 gt ori0 el, ports_stmts_tmap' ps ss = Some (tmap, var2exprs) -> Qin (Sfcnct (Eid ref_tgt) expr) ss -> type_of_ref ref_tgt newtm = Some (t_tgt, ori) ->
type_of_expr expr newtm = Some (exist ftype_not_implicit_width t_expr pe) -> list_gtypexpr expr t_expr = Some rhs_expr_ls -> nth_error rhs_expr_ls n = Some texpr -> CEP.find pv0 var2exprs = Some el -> 
nth_error (list_gtypref ref_tgt t_tgt ori) n = Some (pv0, gt, ori0) -> texpr \in el.
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
                                      | Some (t_tgt, ori), Some (exist t_expr _) => ftype_equiv t_tgt t_expr -> connect_type ref_tgt t_tgt t_expr ori HiF.Source
                                      | _, _ => True
                                      end
    | _ => True
    end).
Proof.
  intros ps ss inferorder var2exprs tmap newtm Hinfer Hpre hfs Hin.
  case Hs : hfs => [||||||ref expr||]; try done.
  case He : expr => [ct c| c e1 | u e1 | op e1 e2 | c e1 e2 | c e1 | ref0 ]; try done. 
  (* const *)
  1,2,3,4,5,6 : rewrite -He; clear He; rewrite Hs in Hin; clear Hs hfs;
                case Href : ref => [ref_tgt|||]; try done;
                case Htr : (type_of_ref ref_tgt newtm) => [[t_tgt ori]|]; try done;
                case Hte : (type_of_expr expr newtm) => [[t_expr pe]|] ; try done; intro Heq;
                rewrite /connect_type;
                apply rwP with (P := ftype_equiv t_tgt t_expr /\
    check_connect_type (list_gtypref ref_tgt t_tgt ori)
    (list_gtypref (0%num, 0%num) t_expr HiF.Source)).
  1,3,5,7,9,11 : apply andP.
  1,2,3,4,5,6 : split. 
  1,3,5,7,9,11 : apply Heq. (* hypo *)
  apply check_connect_type_correct with (ft := list_gtypref ref_tgt t_tgt ori) (te := list_gtypref (0%num, 0%num) t_expr HiF.Source).
  intros n.
  case Hlhs : (nth_error (list_gtypref ref_tgt t_tgt ori) n) => [[[pv0 gt] ori0]|].
  case Hrhs : (nth_error (list_gtypref (0%num, 0%num) t_expr HiF.Source) n) => [[[pv1 gte] ori1]|]; try done.
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
  case Htexpr : (nth_error rhs_expr_ls n) => [texpr|]; rewrite Htexpr in Hte. destruct Hte as [p0 Hte].
  apply InferWidth_fun_correct with (pv := pv0) (el := el) (tmap := tmap') (newtm := newtm') (expr := texpr) in Hinfer; try done.
  generalize Htr; rewrite /type_of_ref in Htr; case Hcheckt : (CEP.find (ref_tgt.1, 0%num) newtm) => [[checkt ori_c]|]; rewrite Hcheckt in Htr; try discriminate; intro Htr'.
  generalize Hlhs; apply nth_error_In in Hlhs; apply list_fsteq in Hlhs; simpl in Hlhs.
  intro Hlhs'; generalize Hlhs'; apply list_typeq with (tmap := newtm) in Hlhs'; try done.
  intro Hlhs0; rewrite /type_of_ref -Hlhs in Hlhs'. rewrite -Hlhs in Hinfer.
  assert (exists checkt' ori_c', CEP.find (ref_tgt.1, 0%num) newtm' = Some (checkt', ori_c')).
  admit. (* 由 Hcheckt *)
  destruct H0 as [checkt' [ori_c' Htgt0]]; rewrite Htgt0 in Hinfer.
  assert (exists nt ori', ft_find_sub checkt' pv0.2 ori_c' = Some (nt, ori')).
  admit. (* 由 Htr *)
  destruct H0 as [nt [ori' Hsub0]]; rewrite Hsub0 in Hinfer; rewrite Hcheckt in Hlhs'.
  apply infernotin_eq with (var2exprs := var2exprs) (tmap := newtm') (newtm := newtm) in Horder2; try done; move : Horder2 => [Horder2 Horder2'].
  rewrite /type_of_ref -Hlhs Htgt0 Hcheckt in Horder2; rewrite Horder2 in Hlhs'; rewrite Hlhs' in Hsub0; inversion Hsub0; clear Hsub0.
  rewrite -H1 in Hinfer; clear H1 nt H2 ori'.
  assert (texpr \in el).
  rewrite Href in Hin; move : Hpre Hin Htr' Hte' Hsplit Htexpr Hel Hlhs0.
  apply preexpr_in.
  rewrite Hel in Horder2'; specialize Horder2' with (e := texpr); apply Horder2' in H0; rewrite -H0 Hte in Hinfer; clear Horder2' H0.
  assert (fgtyp_equiv gt gte).
  move : Heq Hlhs0 Hrhs; apply listgtyp_eq.
  apply Hinfer in H0; clear Hinfer; rewrite /connect_fgtyp_compatible in H0.
  move /andP : H0 => [_ H0]; rewrite Himpli in H0; done.
  rewrite Href in Hin; move : Hpre Hin Htr Hte' Hsplit Htexpr Hel Hlhs.
  apply preexpr_in.
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
  rewrite He in Hs; clear He expr; rewrite Hs in Hin; clear Hs hfs.
  case Href : ref => [ref_tgt|||]; rewrite Href in Hin; try done.
  case Href0 : ref0 => [ref_src|||]; rewrite Href0 in Hin; clear Href; try done.
  case Htgt : (type_of_ref ref_tgt newtm) => [[t_tgt ori_tgt]|]; clear Href0 ref ref0; try done.
  case Hsrc : (type_of_ref ref_src newtm) => [[t_src ori_src]|]; try done; intro Heq.
  rewrite /connect_non_passive_type.
  apply rwP with (P := ftype_equiv t_tgt t_src /\ check_connect_non_passive_type (list_gtypref ref_tgt t_tgt ori_tgt) (list_gtypref ref_src t_src ori_src)).
  apply andP.
  split; try done. 
  apply check_connect_non_passive_type_correct.
  intro n.

  case Hlhs : (nth_error (list_gtypref ref_tgt t_tgt ori_tgt) n) => [[[pv_tgt gt_tgt] ori_tgt0]|].
  case Hrhs : (nth_error (list_gtypref ref_src t_src ori_src) n) => [[[pv_src gt_src] ori_src0]|].
  case Hori_tgt : ori_tgt0.
  (*rewrite /connect_fgtyp_compatible.
  apply rwP with (P := fgtyp_equiv gt gte /\
    (if not_implicit gt
    then true
    else sizeof_fgtyp gte <= sizeof_fgtyp gt)).
  apply andP.
  split. 
  move : Heq Hlhs Hrhs; apply listgtyp_eq.
  case Himpli : (not_implicit gt); try done.*)
  - (* tgt : source *)
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
  case Htexpr : (nth_error rhs_expr_ls n) => [texpr|]; rewrite Htexpr in Hte. destruct Hte as [p0 Hte].
  apply InferWidth_fun_correct with (pv := pv0) (el := el) (tmap := tmap') (newtm := newtm') (expr := texpr) in Hinfer; try done.
  generalize Htr; rewrite /type_of_ref in Htr; case Hcheckt : (CEP.find (ref_tgt.1, 0%num) newtm) => [[checkt ori_c]|]; rewrite Hcheckt in Htr; try discriminate; intro Htr'.
  generalize Hlhs; apply nth_error_In in Hlhs; apply list_fsteq in Hlhs; simpl in Hlhs.
  intro Hlhs'; generalize Hlhs'; apply list_typeq with (tmap := newtm) in Hlhs'; try done.
  intro Hlhs0; rewrite /type_of_ref -Hlhs in Hlhs'. rewrite -Hlhs in Hinfer.
  assert (exists checkt' ori_c', CEP.find (ref_tgt.1, 0%num) newtm' = Some (checkt', ori_c')).
  admit. (* 由 Hcheckt *)
  destruct H0 as [checkt' [ori_c' Htgt0]]; rewrite Htgt0 in Hinfer.
  assert (exists nt ori', ft_find_sub checkt' pv0.2 ori_c' = Some (nt, ori')).
  admit. (* 由 Htr *)
  destruct H0 as [nt [ori' Hsub0]]; rewrite Hsub0 in Hinfer; rewrite Hcheckt in Hlhs'.
  apply infernotin_eq with (var2exprs := var2exprs) (tmap := newtm') (newtm := newtm) in Horder2; try done; move : Horder2 => [Horder2 Horder2'].
  rewrite /type_of_ref -Hlhs Htgt0 Hcheckt in Horder2; rewrite Horder2 in Hlhs'; rewrite Hlhs' in Hsub0; inversion Hsub0; clear Hsub0.
  rewrite -H1 in Hinfer; clear H1 nt H2 ori'.
  assert (texpr \in el).
  rewrite Href in Hin; move : Hpre Hin Htr' Hte' Hsplit Htexpr Hel Hlhs0.
  apply preexpr_in.
  rewrite Hel in Horder2'; specialize Horder2' with (e := texpr); apply Horder2' in H0; rewrite -H0 Hte in Hinfer; clear Horder2' H0.
  assert (fgtyp_equiv gt gte).
  move : Heq Hlhs0 Hrhs; apply listgtyp_eq.
  apply Hinfer in H0; clear Hinfer; rewrite /connect_fgtyp_compatible in H0.
  move /andP : H0 => [_ H0]; rewrite Himpli in H0; done.
  rewrite Href in Hin; move : Hpre Hin Htr Hte' Hsplit Htexpr Hel Hlhs.
  apply preexpr_in.

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
    case Hss : (stmt_tmap (CEP.empty (ftype * HiF.forient), CEP.empty (ftype * HiF.forient)) s vm) => [tmap_scope'|].
    case Hsst : (stmts_tmap tmap_scope' st vm) => [[tmap' emap']|].
    (*apply IH with (nps := [::]) (nss := nst) (newtm := newtm) (pv := pv) in Himpliss; try done.

    case Hsp : (stmt_tmap' (CEP.empty (ftype * HiF.forient)) (CEP.empty (seq HiFP.hfexpr)) s) => [[tmap0 emap0]|]; rewrite Hsp in Hinfer; try discriminate.
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
              (list_gtypref (0%num, 0%num) ft HiF.Duplex)
              (list_gtypref (0%num, 0%num) ft_val HiF.Duplex)). apply andP. split.
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
              assert (exists ft_val', type_of_expr rst_val (CEP.add r (newt, HiF.Duplex) pmap) = Some ft_val').
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
          1,3,5,7,9,11 : case Hexprt : (type_of_expr e newtm) => [[t_expr p_expr]|]; rewrite Hexprt in Hinfer.
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

Lemma geq_conj2mux : forall tmap (gt initt : fgtyp) (el : seq HiFP.hfexpr) eftl (nt : fgtyp), (forall (texpr : HiFP.hfexpr) (te : fgtyp) (p : ftype_not_implicit_width (Gtyp te)), texpr \in el -> type_of_expr texpr tmap = Some (exist ftype_not_implicit_width (Gtyp te) p) -> ((sizeof_fgtyp gt) >= (sizeof_fgtyp te))) ->
  fil_ftlist [seq type_of_expr e tmap | e <- el] = Some eftl -> sizeof_fgtyp initt = 0 -> max_ftlist eftl initt = Some nt -> ((sizeof_fgtyp gt) >= (sizeof_fgtyp nt)).
Proof.
Admitted.

Fixpoint find_sub_expr4v (pv : ProdVarOrder.t) (lhsl : seq (ProdVarOrder.t * fgtyp * HiF.forient)) (rstl : seq HiFP.hfexpr) : option (seq HiFP.hfexpr) :=
  match lhsl, rstl with
  | nil, nil => Some nil
  | (hd, _, _) :: tl, hde :: tle => if (hd == pv) then Some [:: hde]
                              else find_sub_expr4v pv tl tle
  | _, _ => None
  end.

Fixpoint find_sub_non_passive4v (pv : ProdVarOrder.t) (lhsl rhsl : seq (ProdVarOrder.t * fgtyp * HiF.forient)) : option (seq HiFP.hfexpr) :=
  match lhsl, rhsl with
  | nil, nil => Some nil
  | (hd, _, HiF.Duplex) :: tl, (hde, _, HiF.Source) :: tle 
  | (hd, _, HiF.Sink) :: tl, (hde, _, HiF.Source) :: tle 
  | (hd, _, HiF.Sink) :: tl, (hde, _, HiF.Duplex) :: tle 
  | (hd, _, HiF.Duplex) :: tl, (hde, _, HiF.Duplex) :: tle => if (hd == pv) then Some [:: (Eref (Eid hde))]
                                                            else find_sub_non_passive4v pv tl tle
  | (hd, _, HiF.Source) :: tl, (hde, _, HiF.Sink) :: tle 
  | (hd, _, HiF.Source) :: tl, (hde, _, HiF.Duplex) :: tle 
  | (hd, _, HiF.Duplex) :: tl, (hde, _, HiF.Sink) :: tle => if (hde == pv) then Some [:: (Eref (Eid hd))]
                                                            else find_sub_non_passive4v pv tl tle
  | _, _ => None
  end.

Fixpoint find_sub_expr (pv : ProdVarOrder.t) (s : HiFP.hfstmt) (tmap : CEP.t (ftype * HiF.forient)) : option (seq HiFP.hfexpr) :=
  match s with
  | Sreg v r => match reset r with
                | NRst => Some nil
                | Rst _ rst_val => match list_gtypexpr rst_val (type r), list_gtypref v (type r) HiF.Duplex with
                                  | Some rstl, lhsl => find_sub_expr4v pv lhsl rstl
                                  | _, _ => None
                                  end
                end
  | Snode v e => match type_of_expr e tmap with
                | Some (exist t _) => match list_gtypexpr e t, list_gtypref v t HiF.Sink with
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
                | Some (t_tgt, ori_tgt), Some (exist t_src _) =>
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
  find_sub_exprs v ss tmap = Some el -> (forall e te (p : ftype_not_implicit_width (Gtyp te)), e \in el -> type_of_expr e tmap = Some (exist ftype_not_implicit_width (Gtyp te) p) -> sizeof_fgtyp (type_of_vx t) >= sizeof_fgtyp te)).
Proof.
Admitted.

Lemma Semgeqinfer : forall pp ss mv vm tmap newtm, Sem (FInmod mv pp ss) vm -> ports_stmts_tmap pp ss vm = Some tmap -> InferWidths_stage1 (FInmod mv pp ss) = Some newtm -> (forall e t0 t1 (p0 : ftype_not_implicit_width (Gtyp t0)) (p1 : ftype_not_implicit_width (Gtyp t1)), type_of_expr e tmap = Some (exist ftype_not_implicit_width (Gtyp t0) p0) -> type_of_expr e newtm = Some (exist ftype_not_implicit_width (Gtyp t1) p1) -> sizeof_fgtyp t0 >= sizeof_fgtyp t1).
Proof.
Admitted.

Lemma find_sub_exprs_correct : forall v ps ss tmap var2exprs, ports_stmts_tmap' ps ss = Some (tmap, var2exprs) -> CEP.find v var2exprs = find_sub_exprs v ss tmap.
Proof.
Admitted.

Lemma set_find_sub : forall checkt nt nt0 n ori ori_v initt, ft_find_sub checkt n ori_v = Some (Gtyp initt, ori) -> ft_set_sub checkt nt n = Some nt0 -> ft_find_sub nt0 n ori_v = Some (Gtyp nt, ori)
with set_find_sub_f : forall checkf nf nf0 n ori ori_v initt, ft_find_sub_f checkf n ori_v = Some (Gtyp initt, ori) -> ft_set_sub_f checkf nf n = Some nf0 -> ft_find_sub_f nf0 n ori_v = Some (Gtyp nf, ori).
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
  case Hf : (ft_find_sub init v.2 ori_v) => [[f ori]|]; rewrite Hf in Hinfer1; try discriminate.
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
  assert (Hte : exists t0 p0, type_of_expr texpr tmap0' = Some (exist ftype_not_implicit_width (Gtyp t0) p0)).
  admit. (* tl中应全为gtyp expr *)
  destruct Hte as [t0 [p0 Hte]].
  apply Semgeqinfer with (tmap := tmap0') (newtm := newtm) (e := texpr) (t0 := t0) (t1 := te) (p0 := p0) (p1 := p) in Hsem; try done.
  apply Sem_wdgeqmax with (v := v) (t := t) (el := el) (e := texpr) (te := t0) (p := p0) in Hsems; try done.
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
  move : Hf Hset.
  apply set_find_sub.

  admit. (* None则有错 *)
  admit. (* None则有错 *)
  case Ht : (CEP.find v vm); try done.
Admitted.

Search (type_of_ref).