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

Fixpoint make_gtyp_implicit (vm : CEP.t vertex_type) (tl : seq (ProdVarOrder.t * fgtyp * HiF.forient)) : option (CEP.t vertex_type) := 
match tl with
    | nil => Some vm
    | (pv, gt, _) :: tl => if not_implicit gt then make_gtyp_implicit vm tl
                         else match CEP.find pv vm with
                             | Some vx => let vm' := CEP.add pv (make_vx_implicit vx) vm in make_gtyp_implicit vm' tl
                             | None => None
                             end
    end.

Definition make_p_implicit (vm : CEP.t vertex_type) (p : HiFP.hfport) : option (CEP.t vertex_type) :=
   match p with
   | Finput v t => let tl := list_gtypref v t HiF.Source in
                   make_gtyp_implicit vm tl
   | Foutput v t => let tl := list_gtypref v t HiF.Sink in
                   make_gtyp_implicit vm tl
   end.

Fixpoint  make_ps_implicit (vm : CEP.t vertex_type) (ps : seq HiFP.hfport) : option (CEP.t vertex_type) :=
    match ps with
    | nil => Some vm
    | hd :: tl => match make_p_implicit vm hd with
                | Some vm' => make_ps_implicit vm' tl
                | None => None
                end
    end.

Fixpoint make_s_implicit (vm : CEP.t vertex_type) (st : HiFP.hfstmt) : option (CEP.t vertex_type) :=
(* change the vertex of statement st in vm to implicit-width if st defines an implicit-width component *)
   match st with
  | Sskip => Some vm
  | Swire v t => let tl := list_gtypref v t HiF.Duplex in
                 make_gtyp_implicit vm tl
  | Sreg v r => let tl := list_gtypref v (type r) HiF.Duplex in
                make_gtyp_implicit vm tl
  | Smem v m => (*TBD*) Some vm
  | Sinst v inst => (*TBD*) Some vm
  | Swhen _ s1 s2 => match make_ss_implicit vm s1 with
                    | Some vm' => make_ss_implicit vm s2
                    | None => None
                    end
  | _ => Some vm 
  end
with make_ss_implicit (vm : CEP.t vertex_type) (ss : HiFP.hfstmt_seq) : option (CEP.t vertex_type) :=
(* change the vertices of statements ss in vm to implicit-width if ss defines implicit-width components *)
   match ss with
  | Qnil => Some vm
  | Qcons s st => match make_s_implicit vm s with
                | Some vm' => make_ss_implicit vm st
                | None => None
                end
  end.

Definition make_vm_implicit (F : HiFP.hfmodule) (vm : CEP.t vertex_type) : option (CEP.t vertex_type) :=
   (* in vm, change the type of vertex (explicit to implicit) according to its declaration in F. *)
   match F with
   | FInmod _ pp ss => match make_ps_implicit vm pp with
                      | Some vm' => make_ss_implicit vm' ss
                      | None => None
                      end
   | FExmod _ _ _ => Some vm
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
  | (_, thd, HiF.Sink) :: ttl, (_, shd, HiF.Duplex) :: stl => connect_fgtyp_compatible thd shd && check_connect_non_passive_type ttl stl
  | (_, thd, HiF.Source) :: ttl, (_, shd, HiF.Sink) :: stl 
  | (_, thd, HiF.Source) :: ttl, (_, shd, HiF.Duplex) :: stl => connect_fgtyp_compatible shd thd && check_connect_non_passive_type ttl stl
  | _, _ => false
  end.

Fixpoint check_connect_type (t_tgt t_src : seq (ProdVarOrder.T * fgtyp * HiF.forient)) : bool :=
  match t_tgt, t_src with
  | nil, nil => true
  | (_, thd, _) :: ttl, (_, shd, _) :: stl => connect_fgtyp_compatible thd shd && check_connect_type ttl stl
  | _, _ => false
  end.

Definition connect_non_passive_type (t_tgt t_src : ftype) (ori_tgt ori_src : HiF.forient) : Prop :=
  ftype_equiv t_tgt t_src && check_connect_non_passive_type (list_gtypref (N0, N0) t_tgt ori_tgt) (list_gtypref (N0, N0) t_src ori_src). 

Definition connect_type (t_tgt t_src : ftype) (ori_tgt ori_src : HiF.forient) : Prop :=
  ftype_equiv t_tgt t_src && check_connect_type (list_gtypref (N0, N0) t_tgt ori_tgt) (list_gtypref (N0, N0) t_src ori_src).

Fixpoint Sem_frag_stmt (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (s : HiFP.hfstmt) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t (ftype * HiF.forient)) : Prop :=
   (* The predicate returns True if vm_new/ct_new can be constructed from vm_old/ct_old by applying s.
   type checking, constraints *)
   match s with
   | Sskip => CEP.Equal vm_old vm_new /\ CEP.Equal ct_old ct_new
   | Sfcnct (Eid ref_tgt) (Eref (Eid ref_src)) => (* allow non-passive types *)
          match type_of_ref ref_tgt tmap, type_of_ref ref_src tmap with
          | Some (ft_tgt, ori_tgt), Some (ft_src, ori_src) => connect_non_passive_type ft_tgt ft_src ori_tgt ori_src
          | _, _ => False
          end
   | Sfcnct (Eid ref) expr =>
          match type_of_ref ref tmap, type_of_expr expr tmap with
          | Some (ft_tgt, ori_tgt), Some (exist ft_src _) => connect_type ft_tgt ft_src ori_tgt HiF.Source
          | _, _ => False
          end
   | Sreg v reg =>
       match reset reg with
        | Rst _ rst_val => match CEP.find v tmap, type_of_expr rst_val tmap with
            | Some (newft, _), Some (exist rst_val_type _) => connect_type newft rst_val_type HiF.Duplex HiF.Duplex
            | _, _ => false
            end
        | NRst => True (* type check newft: we only need to verify newft is passive *)
        end
   | Smem v mem => False (* ? *)
   | Sinst var1 var2 => False (* ? *)
   | Swhen cond ss_true ss_false =>
       if type_of_expr cond tmap is Some (exist (Gtyp (Fuint 1)) _)
       then exists (vm_true : CEP.t vertex_type) (ct_true ct_false : CEP.t def_expr),
                   Sem_frag_stmts vm_old ct_old ss_true vm_true ct_true tmap
                /\
                   Sem_frag_stmts vm_true (extend_map_with ct_old ct_true) ss_false vm_new ct_false tmap
       else False
   | Sinvalid _
   | Swire _ _
   | Snode _ _ => True
   | _ => False
   end
with Sem_frag_stmts (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (ss : HiFP.hfstmt_seq) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t (ftype * HiF.forient)) : Prop :=
match ss with
| Qnil =>
       CEP.Equal vm_old vm_new
| Qcons s ss' =>
    exists (vm' : CEP.t vertex_type) (ct' : CEP.t def_expr),
           Sem_frag_stmt vm_old ct_old s vm' ct' tmap
        /\
           Sem_frag_stmts vm' ct' ss' vm_new ct_new tmap
end.

Definition Sem (F : HiFP.hfmodule) (vm : CEP.t vertex_type) (ct : CEP.t def_expr) : Prop :=
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
                  Sem_frag_stmts vm' ct' ss vm ct tmap)
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
  | (ref1, _, HiF.Duplex) :: tl1, (ref2, _, HiF.Source) :: tl2 => 
                match CEP.find ref1 var2exprs with
                | Some ls => add_expr_connect_non_passive tl1 tl2 (CEP.add ref1 ((Eref (Eid ref2)) :: ls) var2exprs)
                | None => add_expr_connect_non_passive tl1 tl2 (CEP.add ref1 [::(Eref (Eid ref2))] var2exprs)
                end
  | (ref1, _, HiF.Source) :: tl1, (ref2, _, HiF.Sink) :: tl2 
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

Theorem InferWidths_correct :
  forall (F : HiFP.hfmodule) (vm' : CEP.t vertex_type) (ct : CEP.t def_expr),
    match InferWidths_m F, make_vm_implicit F vm' with
    | Some (F', _), Some vm => Sem F' vm' ct -> Sem F vm ct
    | _, _ => True
    end.
Proof.
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

Theorem InferWidths_correct' :
  forall (F : HiFP.hfmodule) (vm : CEP.t vertex_type) (vm' : CEP.t vertex_type) (ct : CEP.t def_expr),
    match InferWidths_m F with
    | Some (F', _) => Sem F' vm' ct -> Sem F vm ct -> vm_le vm vm'
    | _ => True
    end.
Proof.
Admitted.