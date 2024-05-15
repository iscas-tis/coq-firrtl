(* Expand Whens pass

   This is part of the Hardware Verification project of ISCAS,
   under the leadership of Prof. Zhilin Wu.
   This file has been written mainly by David N. Jansen.

   Expand Whens is part of the translation from HiFirrtl to LoFirrtl.
   Before Expand Whens, all widths have been inferred and all types
   lowered, so we just assume this as preconditions.
   The main duty of the Expand Whens pass is to replace all when
   statements with suitable multiplexers.  In this process, also
   the “last connect” semantics is ensured.

   The main function of Expand Whens is ExpandBranch_funs.  This
   function extracts the component definition statements from a
   statement sequence, puts them in a linear statement sequence
   (i.e. removes all when statements here), and it also extracts
   a connection map that describes how every component is connected.
   This connection map is then written out as a sequence of
   connect statements (and possibly “is invalid” statements).

   A compiler (part) is correct if: every semantics of a translated
   design is also a semantics of the original design.  In
   particular, an incorrect design -- a program without semantics --
   is not translated to a correct design.  Therefore, ExpandBranch_funs
   also has to check for some errors, namely those that could
   disappear by expanding when statements.  These are:
   - scoping errors: a component is defined within a branch of a
     when statement but accesses outside.
   - connection errors: an erroneous connection (type or flow
     direction) is made but later overwritten.
   - condition type errors: a when statement condition contains
     an error but the condition actually never needs to be evaluated
     in the translated design.
   Note that strictly speaking, some errors can be left alone;
   for example, if multiple components have the same name in a
   single module, scopes do not matter, so the design will be
   erroneous before and after Expand Whens.

   Internally speaking, because all types have been lowered before,
   the tmap (which contained the type of every component) is not
   needed.  Expand Whens will only use the vertex set of the module
   graph vm to decide what type and flow direction an expression has.

   A remark on style: many definitions are mutually recursive because
   statements and statement sequences are mutually recursive.  We
   prefer to place the statement sequence function before the
   single-statement function.
   *)

From Coq Require Import BinNat ZArith.
From mathcomp Require Import ssreflect ssrbool eqtype seq fintype ssrnat div ssrfun.
From simplssrlib Require Import SsrOrder Var FMaps.
From firrtl Require Import Firrtl Env HiEnv HiFirrtl ModuleGraph_oriented.



(*****************************************************************************)
(*                                                                           *)
(*                    P R E C O N D I T I O N   C H E C K S                  *)
(*                                                                           *)
(*****************************************************************************)



(* The following functions allow to verify some preconditions for
   Expand Whens.  In particular,
   - whether everything has been fully inferred
   - type checking functions *)

(*---------------------------------------------------------------------------*)
(* Ensuring that all types are fully inferred                                *)

Definition fully_inferred (gt : fgtyp) : bool :=
match gt with
| Fuint_implicit _
| Fsint_implicit _
| Freset => false
| _ => true
end.

Fixpoint ports_have_fully_inferred_ground_types (pp : seq HiFP.hfport) : bool :=
match pp with
| [::] => true
| Finput  _ (Gtyp gt) :: pp'
| Foutput _ (Gtyp gt) :: pp' => fully_inferred gt && ports_have_fully_inferred_ground_types pp'
| _ => false
end.

Definition tmap_has_fully_inferred_ground_types (tmap : CEP.t (ftype * HiF.forient)) : Prop :=
forall (v : ProdVarOrder.T),
   match CEP.find v tmap return Prop with
   | Some (Gtyp gt, _) => fully_inferred gt
   | Some _ => False
   | None => True
   end.

(*---------------------------------------------------------------------------*)
(* Type checking references and expressions                                  *)

Definition lhs_type_of_ref
    (* finds the type of a ground-type reference that can be written
       (i.e. no input ports and no nodes) *)
    (ref : HiFP.href)         (* reference that is being written *)
    (vm  : CEP.t vertex_type) (* part of the module graph that is in scope *)
:   option fgtyp
:=  match ref with
    | Eid v =>
        match CEP.find v vm with
        | Some (OutPort gt)
        | Some (Register gt _ _ _)
        | Some (Wire gt) => Some gt
        | _ => None
        end
    | _ => None (* TBD for memory and instances *)
    end.

Definition rhs_type_of_ref
    (* finds the type of a ground-type reference that can be read
       (i.e. no output ports) *)
    (ref : HiFP.href)         (* reference that is being read *)
    (vm  : CEP.t vertex_type) (* part of the module graph that is in scope *)
:   option fgtyp
:=  match ref with
    | Eid v =>
        match CEP.find v vm with
        | Some (InPort gt)
        | Some (Register gt _ _ _)
        | Some (Wire gt)
        | Some (Node gt) => Some gt
        | _ => None
        end
    | _ => None (* TBD for memory and instances *)
    end.

Definition fgtyp_mux
    (* Find the type of a multiplexer whose two inputs have types x and y, for ground types *)
    (x y : fgtyp_explicit) (* the two inputs of the multiplexer *)
:   option fgtyp_explicit
:=  match x, y with
    | exist (Fuint wx) _, exist (Fuint wy) _ => Some (Fuint_exp (maxn wx wy))
    | exist (Fsint wx) _, exist (Fsint wy) _ => Some (Fsint_exp (maxn wx wy))
    | exist Fclock _, exist Fclock _ => Some Fclock_exp
    | exist Fasyncreset _, exist Fasyncreset _ => Some Fasyncreset_exp
    | _, _ => None
    end.

Fixpoint rhs_type_of_expr 
    (* Find the type of expression expr. It must be of a ground type. *)
    (expr : HiFP.hfexpr)     (* expression whose type is constructed *)
    (vm : CEP.t vertex_type) (* part of the module graph that is in scope *)
:   option fgtyp_explicit
:=  match expr with
    | Econst t bs =>
        match t with
        | Fuint_implicit w => Some (Fuint_exp w)
        | Fsint_implicit w => Some (Fsint_exp w)
        | t => Some (exist not_implicit_width t I)
        end
    | Eref r =>
        match rhs_type_of_ref r vm with
        | Some (Fuint_implicit w) => Some (Fuint_exp w)
        | Some (Fsint_implicit w) => Some (Fsint_exp w)
        | Some t => Some (exist not_implicit_width t I)
        | _ => None
        end
    | Ecast AsUInt e1 =>
        match rhs_type_of_expr e1 vm with
        | Some (exist (Fsint w) _)
        | Some (exist (Fuint w) _) => Some (Fuint_exp w)
        | Some (exist Fclock _)
        | Some (exist Fasyncreset _) => Some (Fuint_exp 1)
        | _ => None
        end
    | Ecast AsSInt e1 =>
        match rhs_type_of_expr e1 vm with
        | Some (exist (Fsint w) _)
        | Some (exist (Fuint w) _) => Some (Fsint_exp w)
        | Some (exist Fclock _)
        | Some (exist Fasyncreset _) => Some (Fsint_exp 1)
        | _ => None
        end
    | Ecast AsClock e1 =>
        match rhs_type_of_expr e1 vm with
        | Some _ => Some Fclock_exp
        | _ => None
        end
    | Ecast AsAsync e1 =>
        match rhs_type_of_expr e1 vm with
        | Some _ => Some Fasyncreset_exp
        | _ => None
        end
    | Eprim_unop (Upad n) e1 =>
        match rhs_type_of_expr e1 vm with
        | Some (exist (Fsint w) _) => Some (Fsint_exp (maxn w n))
        | Some (exist (Fuint w) _) => Some (Fuint_exp (maxn w n))
        | _ => None
        end
    | Eprim_unop (Ushl n) e1 =>
        match rhs_type_of_expr e1 vm with
        | Some (exist (Fsint w) _) => Some (Fsint_exp (w + n))
        | Some (exist (Fuint w) _) => Some (Fuint_exp (w + n))
        | _ => None
        end
    | Eprim_unop (Ushr n) e1 =>
        match rhs_type_of_expr e1 vm with
        | Some (exist (Fsint w) _) => Some (Fsint_exp (maxn (w - n) 1))
        | Some (exist (Fuint w) _) => Some (Fuint_exp (maxn (w - n) 0))
        | _ => None
        end
    | Eprim_unop Ucvt e1 =>
        match rhs_type_of_expr e1 vm with
        | Some (exist (Fsint w) _) => Some (Fsint_exp w)
        | Some (exist (Fuint w) _) => Some (Fsint_exp (w + 1))
        | _ => None
        end
    | Eprim_unop Uneg e1 =>
        match rhs_type_of_expr e1 vm with
        | Some (exist (Fsint w) _)
        | Some (exist (Fuint w) _) => Some (Fsint_exp (w + 1))
        | _ => None
        end
    | Eprim_unop Unot e1 =>
        match rhs_type_of_expr e1 vm with
        | Some (exist (Fsint w) _)
        | Some (exist (Fuint w) _) => Some (Fuint_exp w)
        | _ => None
        end
    | Eprim_unop (Uextr n1 n2) e1 =>
        match rhs_type_of_expr e1 vm with
        | Some (exist (Fsint w) _)
        | Some (exist (Fuint w) _) =>
            if (n2 <= n1) && (n1 < w) then Some (Fuint_exp (n1 - n2 + 1))
                                      else None
        | _ => None
        end
    | Eprim_unop (Uhead n) e1 =>
        match rhs_type_of_expr e1 vm with
        | Some (exist (Fsint w) _)
        | Some (exist (Fuint w) _) =>
            if n <= w then Some (Fuint_exp n)
                      else None
        | _ => None
        end
    | Eprim_unop (Utail n) e1 =>
        match rhs_type_of_expr e1 vm with
        | Some (exist (Fsint w) _)
        | Some (exist (Fuint w) _) =>
            if n <= w then Some (Fuint_exp (w - n))
                      else None
        | _ => None
        end
    | Eprim_unop _ e1 =>
        match rhs_type_of_expr e1 vm with
        | Some (exist (Fsint _) _)
        | Some (exist (Fuint _) _) => Some (Fuint_exp 1)
        | _ => None
        end
    | Eprim_binop (Bcomp _) e1 e2 =>
        match rhs_type_of_expr e1 vm, rhs_type_of_expr e2 vm with
        | Some (exist (Fsint _) _), Some (exist (Fsint _) _)
        | Some (exist (Fuint _) _), Some (exist (Fuint _) _) => Some (Fuint_exp 1)
        | _, _ => None
        end
    | Eprim_binop Badd e1 e2
    | Eprim_binop Bsub e1 e2 =>
        match rhs_type_of_expr e1 vm, rhs_type_of_expr e2 vm with
        | Some (exist (Fuint w1) _), Some (exist (Fuint w2) _) => Some (Fuint_exp (maxn w1 w2 + 1))
        | Some (exist (Fsint w1) _), Some (exist (Fsint w2) _) => Some (Fsint_exp (maxn w1 w2 + 1))
        | _, _ => None
        end
    | Eprim_binop Bmul e1 e2 =>
        match rhs_type_of_expr e1 vm, rhs_type_of_expr e2 vm with
        | Some (exist (Fuint w1) _), Some (exist (Fuint w2) _) => Some (Fuint_exp (w1 + w2))
        | Some (exist (Fsint w1) _), Some (exist (Fsint w2) _) => Some (Fsint_exp (w1 + w2))
        | _, _ => None
        end
    | Eprim_binop Bdiv e1 e2 =>
        match rhs_type_of_expr e1 vm, rhs_type_of_expr e2 vm with
        | Some (exist (Fuint w1) _), Some (exist (Fuint w2) _) => Some (Fuint_exp w1)
        | Some (exist (Fsint w1) _), Some (exist (Fsint w2) _) => Some (Fsint_exp (w1 + 1))
        | _, _ => None
        end
    | Eprim_binop Brem e1 e2 =>
        match rhs_type_of_expr e1 vm, rhs_type_of_expr e2 vm with
        | Some (exist (Fuint w1) _), Some (exist (Fuint w2) _) => Some (Fuint_exp (minn w1 w2))
        | Some (exist (Fsint w1) _), Some (exist (Fsint w2) _) => Some (Fsint_exp (minn w1 w2))
        | _, _ => None
        end
    | Eprim_binop Bdshl e1 e2 =>
        match rhs_type_of_expr e1 vm, rhs_type_of_expr e2 vm with
        | Some (exist (Fuint w1) _), Some (exist (Fuint w2) _) => Some (Fuint_exp (2 ^ w2 + w1 - 1))
        | Some (exist (Fsint w1) _), Some (exist (Fuint w2) _) => Some (Fsint_exp (2 ^ w2 + w1 - 1))
        | _, _ => None
        end
    | Eprim_binop Bdshr e1 e2 =>
        match rhs_type_of_expr e1 vm, rhs_type_of_expr e2 vm with
        | Some (exist (Fuint w1) _), Some (exist (Fuint w2) _) => Some (Fuint_exp w1)
        | Some (exist (Fsint w1) _), Some (exist (Fuint w2) _) => Some (Fsint_exp w1)
        | _, _ => None
        end
    | Eprim_binop Bcat e1 e2 =>
        match rhs_type_of_expr e1 vm, rhs_type_of_expr e2 vm with
        | Some (exist (Fuint w1) _), Some (exist (Fuint w2) _)
        | Some (exist (Fsint w1) _), Some (exist (Fsint w2) _) => Some (Fuint_exp (w1 + w2))
        | _, _ => None
        end
    | Eprim_binop Band e1 e2
    | Eprim_binop Bor e1 e2
    | Eprim_binop Bxor e1 e2 =>
        match rhs_type_of_expr e1 vm, rhs_type_of_expr e2 vm with
        | Some (exist (Fuint w1) _), Some (exist (Fuint w2) _)
        | Some (exist (Fsint w1) _), Some (exist (Fsint w2) _) => Some (Fuint_exp (maxn w1 w2))
        | _, _ => None
        end
    | Emux c e1 e2 =>
        match rhs_type_of_expr c vm, rhs_type_of_expr e1 vm, rhs_type_of_expr e2 vm with
        | Some (exist (Fuint 1) _), Some t1, Some t2 => fgtyp_mux t1 t2
        | _, _, _ => None
        end
    | Evalidif c e1 =>
        match rhs_type_of_expr c vm with
        | Some (exist (Fuint 1) _) => rhs_type_of_expr e1 vm
        | _ => None
        end
    end.



(*****************************************************************************)
(*                                                                           *)
(*                          M A I N   F U N C T I O N                        *)
(*                                                                           *)
(*****************************************************************************)



Definition combine_when_connections
    (* a helper function that takes two connection maps, generated
       by the two branches of a when statement, and combines them
       into one connection map containing suitable multiplexers *)
    (cond           : HiFP.hfexpr)    (* condition under which to decide whether to take the value from true_conn_map *)
    (true_conn_map  : CEP.t def_expr) (* connections made before or in the true branch *)
    (false_conn_map : CEP.t def_expr) (* connections made before or in the false branch *)
:   CEP.t def_expr
:=  CEP.map2 (fun true_expr false_expr : option def_expr =>
                      match true_expr, false_expr with
                      | Some (D_fexpr te), Some (D_fexpr fe) =>
                          if te == fe then true_expr
                          else Some (D_fexpr (Emux cond te fe))
                      | Some D_undefined, _
                      | _, Some D_undefined => Some D_undefined
                      | None, _ => false_expr
                      | _, None => true_expr
                      | Some D_invalidated, _ => false_expr
                      | _, Some D_invalidated => true_expr
                      end)
             true_conn_map false_conn_map.

Fixpoint ExpandBranches_funs
    (* split a statement sequence (possibly containing when
       statements) into a sequence that defines components and a
       connection map.  The output does not contain when statements. *)
    (ss           : HiFP.hfstmt_seq)   (* sequence of statements being translated *)
    (old_comp_ss  : HiFP.hfstmt_seq)   (* component statements of earlier statements in the sequence (used for recursion) *)
    (old_conn_map : CEP.t def_expr)    (* connections made by earlier statements in the sequence (used for recursion) *)
    (old_scope    : CEP.t vertex_type) (* part of module graph vertices that is currently in scope *)
:   option (HiFP.hfstmt_seq * CEP.t def_expr * CEP.t vertex_type)
    (* old_comp_ss, extended with the component statements in ss,
       old_conn_map, extended with the connection statements in ss,
       and old_scope, extended with the component statements in ss that remain in scope *)
:=  match ss with
    | Qnil => Some (old_comp_ss, old_conn_map, old_scope)
    | Qcons s ss =>
        match ExpandBranch_fun s old_comp_ss old_conn_map old_scope with
        | Some (temp_comp_ss, temp_conn_map, temp_scope) =>
            ExpandBranches_funs ss temp_comp_ss temp_conn_map temp_scope
        | None => None
        end
    end
with ExpandBranch_fun
    (* split a single statement (possibly consisting of a when
       statement) into a sequence that defines components and a
       connection map.  The output does not contain when statements. *)
    (s            : HiFP.hfstmt)       (* a single statement being translated *)
    (old_comp_ss  : HiFP.hfstmt_seq)   (* component statements of earlier statements in the sequence (used for recursion) *)
    (old_conn_map : CEP.t def_expr)    (* connections made by earlier statements in the sequence (used for recursion) *)
    (old_scope    : CEP.t vertex_type) (* part of module graph vertices that is currently in scope *)
:   option (HiFP.hfstmt_seq * CEP.t def_expr * CEP.t vertex_type)
    (* old_comp_ss, extended with the component statements in s,
       old_conn_map, extended with the connection statements in s,
       and old_scope, extended with the component statements in s that remain in scope *)
:=  match s with
    | Sskip => Some (old_comp_ss, old_conn_map, old_scope)
    | Swire var (Gtyp typ) =>
        (* no need to check whether var has been defined already.
           It might still be handy though... we’ll see later. *)
        Some (Qrcons old_comp_ss s, old_conn_map, CEP.add var (Wire typ) old_scope)
    | Sreg var reg =>
        (* we need to check whether the register definition contains
           any expression with scoping errors *)
        match type reg, rhs_type_of_expr (clock reg) old_scope, reset reg with
        | Gtyp gt, Some _, Rst rst_sig rst_val =>
            match rhs_type_of_expr rst_sig old_scope, rhs_type_of_expr rst_val old_scope with
            | Some (exist Fasyncreset _), Some _ => Some (Qrcons old_comp_ss s, old_conn_map, CEP.add var (Register gt (clock reg) (reset reg) true) old_scope)
            | Some (exist (Fuint 1) _), Some _ => Some (Qrcons old_comp_ss s, old_conn_map, CEP.add var (Register gt (clock reg) (reset reg) false) old_scope)
            | _, _ => None
            end
        | Gtyp gt, Some _, NRst =>
            Some (Qrcons old_comp_ss s, old_conn_map, CEP.add var (Register gt (clock reg) (reset reg) false) old_scope)
        | _, _, _ => None
        end
    | Smem var mem => None
    | Sinst var1 var2 => None
    | Snode var expr =>
        (* check whether the expression is in scope *)
        match rhs_type_of_expr expr old_scope with
        | Some (exist gt _) =>
            Some (Qrcons old_comp_ss s, old_conn_map, CEP.add var (Node gt) old_scope)
        | _ => None
        end
    | Sfcnct (Eid var) expr =>
        (* The following code needs to be moved to a helper function
           because ref can be more complex than just (Eid var). *)
        (* check whether the two sides are in scope, and their flow direction is correct *)
        match lhs_type_of_ref (Eid var) old_scope, rhs_type_of_expr expr old_scope with
        | Some gt_tgt, Some (exist gt_src _) =>
            if connect_type_compatible false (Gtyp gt_tgt) (Gtyp gt_src) false
            then Some (old_comp_ss, CEP.add var (D_fexpr expr) old_conn_map, old_scope)
            else None
        | _, _ => None
        end
    | Sinvalid (Eid var) =>
        match lhs_type_of_ref (Eid var) old_scope with
        | Some _ =>
            Some (old_comp_ss, CEP.add var D_invalidated old_conn_map, old_scope)
        | _ => None
        end
    | Swhen cond ss_true ss_false =>
        match rhs_type_of_expr cond old_scope with
        | Some (exist (Fuint 1) _) =>
            match ExpandBranches_funs ss_true old_comp_ss old_conn_map old_scope with
            | Some (true_comp_ss, true_conn_map, _) =>
                match ExpandBranches_funs ss_false true_comp_ss old_conn_map old_scope with
                | Some (false_comp_ss, false_conn_map, _) =>
                    Some (false_comp_ss, combine_when_connections cond true_conn_map false_conn_map, old_scope)
                | _ => None
                end
            | _ => None
            end
        | _ => None
        end
    | _ => None
    end.

Fixpoint ExpandPorts_fun
    (* create a map of def_expr for the port sequence pp.
       Out ports need to be assigned value “undefined”;
       in ports do not need to be assigned any value.
       Because types have been lowered already, we can assume
       that all ports have ground types. *)
    (pp : seq HiFP.hfport) (* the sequence of ports of the module *)
:   option (CEP.t vertex_type * CEP.t def_expr)
:=  match pp with
    | [::] => Some (CEP.empty vertex_type, CEP.empty def_expr)
    | Finput p (Gtyp gt) :: pp' =>
        match ExpandPorts_fun pp' with
        | Some (vm_temp, ct_temp) =>
            Some (CEP.add p (InPort gt) vm_temp, ct_temp)
        | None => None
        end
    | Foutput p (Gtyp gt) :: pp' =>
        match ExpandPorts_fun pp' with
        | Some (vm_temp, ct_temp) =>
            Some (CEP.add p (OutPort gt) vm_temp, CEP.add p D_undefined ct_temp)
        | None => None
        end
    | _ => None
    end.

Definition convert_to_connect_stmts
    (* converts a map of connections to connect statements *)
    (conn_map : CEP.t def_expr) (* map that needs to be converted *)
:   HiFP.hfstmt_seq
:=  CEP.fold (fun (v : ProdVarOrder.t) (d : def_expr) (old_ss : HiFP.hfstmt_seq) =>
                      match d with
                      | D_undefined => old_ss
                      | D_invalidated => Qcons (Sinvalid (Eid v)) old_ss
                      | D_fexpr e => Qcons (Sfcnct (Eid v) e) old_ss
                      end)
             conn_map (Qnil ProdVarOrder.T).

Definition ExpandWhens_fun
    (* Expand When statements in a module *)
    (m : HiFP.hfmodule) (* module that needs to be handled *)
:   option HiFP.hfmodule (* result is either a semantically equivalent module without when statements,
                            or nothing if there was some error *)
:=  match m with
    | FInmod v pp ss =>
        match ExpandPorts_fun pp with
        | Some (vm_port, ct_port) =>
            match ExpandBranches_funs ss (Qnil ProdVarOrder.T) ct_port vm_port with
            | Some (def_ss, conn_map, _) =>
                Some (FInmod v pp (Qcat def_ss (convert_to_connect_stmts conn_map)))
            | None => None
            end
        | None => None
        end
    | FExmod _ _ _ => None
    end.



(*****************************************************************************)
(*                                                                           *)
(*                      C O R R E C T N E S S   P R O O F                    *)
(*                                                                           *)
(*****************************************************************************)

Lemma fully_inferred_does_not_change :
forall (gt : fgtyp) (v : CEP.key) (vm : CEP.t vertex_type),
   fully_inferred gt ->
      match code_type_find_vm_widths (Gtyp gt) v vm with
      | Some (Gtyp gt', _) => gt = gt'
      | Some _ => False
      | None => True
      end.
Proof.
intros.
unfold fully_inferred in H.
destruct gt ; try discriminate H ; simpl code_type_find_vm_widths.
* destruct (CEP.find v vm) as [[newgt|newgt|newgt _ _ _|newgt|newgt]|] ; try trivial ;
  destruct newgt ; try trivial ; destruct (n == n0) eqn :Hnn0 ; try trivial ;
  move /eqP : Hnn0 => Hnn0 ; rewrite -Hnn0 ; reflexivity.
* destruct (CEP.find v vm) as [[newgt|newgt|newgt _ _ _|newgt|newgt]|] ; try trivial ;
  destruct newgt ; try trivial ; destruct (n == n0) eqn :Hnn0 ; try trivial ;
  move /eqP : Hnn0 => Hnn0 ; rewrite -Hnn0 ; reflexivity.
* destruct (CEP.find v vm) as [[newgt|newgt|newgt _ _ _|newgt|newgt]|] ; try trivial ;
  destruct newgt ; trivial.
* destruct (CEP.find v vm) as [[newgt|newgt|newgt _ _ _|newgt|newgt]|] ; try trivial ;
  destruct newgt ; trivial.
Qed.

Lemma ExpandPorts_fun_submap :
    forall (ports : seq HiFP.hfport) (vm_old vm_new vm_port vm_old_port : CEP.t vertex_type)
           (ct_old ct_new ct_port : CEP.t def_expr) (tmap port_tmap : CEP.t (ftype * HiF.forient)),
    ports_have_fully_inferred_ground_types ports ->
    ports_tmap ports vm_old_port = Some port_tmap ->
    CEP.submap port_tmap tmap ->
    ExpandPorts_fun ports = Some (vm_port, ct_port) ->
        Sem_frag_ports vm_old ct_old ports vm_new ct_new tmap ->
            CEP.submap vm_port vm_new.
Proof.
induction ports as [|port ports'] ; simpl ; intros.
* injection H2 ; clear H2 ; intros ; subst vm_port ct_port.
  intro.
  by rewrite CEP.Lemmas.F.empty_o //.
* intro.
  (*generalize (ports_tmap_uniq vm_old_port (port :: ports')) ; intro.
  simpl in H4.
  rewrite H0 in H4.*)
  destruct port as [port_name [port_fgtyp| |]|port_name [port_fgtyp| |]] ;
        try by discriminate H2.
  1-2: destruct (ExpandPorts_fun ports') as [[vm_temp ct_temp]|] ;
        last by discriminate H2.
  1-2: injection H2 ; clear H2 ; intros ; subst vm_port ct_port.
  1-2: destruct H3 as [vm' [ct' H3]].
  1-2: move /andP : H => H.
  1-2: specialize (IHports' vm_old vm' vm_temp vm_old_port ct_old ct' ct_temp tmap)
                  with (1 := proj2 H) (4 := Logic.eq_refl).
  1-2: generalize (fully_inferred_does_not_change port_fgtyp port_name vm_old_port (proj1 H)) ; intro.
  1-2: destruct (code_type_find_vm_widths (Gtyp port_fgtyp) port_name vm_old_port)
       as [[[port_fgtyp'| |] _]|] ;
             last (by discriminate H0) ;
             try (by contradiction H2) ;
             subst port_fgtyp'.
  1-2: destruct (ports_tmap ports' vm_old_port) as [temp_tmap|] ;
             last by discriminate H0.
  1-2: specialize (IHports' temp_tmap Logic.eq_refl) with (2 := proj1 H3).
  1-2: destruct H3 as [_ H3] ; simpl Sem_frag_port in H3.
  1-2: destruct (CEP.find port_name temp_tmap) eqn: H2 ; first by discriminate H0.
  1-2: injection H0 ; clear H0 ; intros ; subst port_tmap.
  1-2: rewrite (CEP.Lemmas.submap_add_find H1) in H3.
  1-2: specialize (IHports' (CEP.Lemmas.submap_add_find_none H1 H2)).
  1-2: destruct (k == port_name) eqn: Hport_name_k.
  - 1,3: rewrite CEP.Lemmas.find_add_eq // in H5.
    1-2: move /eqP : Hport_name_k => Hport_name_k ; subst k.
    1-2: injection H5 ; clear H5 ; intros ; subst v.
    1-2: destruct H3 as [H3 _] ; simpl connect_port in H3.
    1-2: move /and3P : H3 => [/andP [_ /eqP H3] _ _].
    1-2: exact H3.
  - 1-2: destruct H3 as [_ H3].
    1-2: specialize (H3 k.1 k.2).
    1-2: rewrite /size_of_ftype -surjective_pairing add1n in H3.
    1-2: assert (k.1 <> port_name.1 \/ k.2 < port_name.2 \/ port_name.2 < k.2).
          1,3: clear -Hport_name_k.
          1-2: destruct (k.1 != port_name.1) eqn: H1 ;
                     first (by left ; move /eqP : H1 => H1 ; exact H1).
          1-2: destruct (k.2 < port_name.2) eqn: H2small ;
                     first (by right ; left ; reflexivity).
          1-2: destruct (port_name.2 < k.2) eqn: H2large ;
                     first (by right ; right ; reflexivity).
          1-2: move /eqP : H1 => H1.
          1-2: apply injective_projections in H1 ;
                     first by rewrite H1 eq_refl // in Hport_name_k.
          1-2: assert (nat_of_bin k.2 == nat_of_bin port_name.2)
                     by rewrite eqn_leq leqNgt H2large leqNgt H2small //.
Admitted.

Lemma ports_tmap_and_ExpandPorts_fun :
    (* a lemma that relates ports_tmap and ExpandPorts_fun *)
    forall (ports : seq HiFP.hfport) (vm_port vm : CEP.t vertex_type) (ct_port : CEP.t def_expr) (pmap : CEP.t (ftype * HiF.forient)),
    ports_have_fully_inferred_ground_types ports ->
    ExpandPorts_fun ports = Some (vm_port, ct_port) ->
    ports_tmap ports vm = Some pmap ->
            (forall v : CEP.key,
                match CEP.find v pmap with
                | Some (Atyp _ _, _) | Some (Btyp _, _) => False
                | _ => True
                end)
        /\
            CEP.Equal vm_port (CEP.map (fun el : ftype * HiF.forient =>
                                               match el with
                                               | (Gtyp gt, HiF.Source) => InPort gt
                                               | (Gtyp gt, HiF.Sink) => OutPort gt
                                               | _ => Node Freset
                                               end)
                                       pmap)
        /\
            CEP.Equal ct_port (CEP.map2 (fun (el : option (ftype * HiF.forient)) (_ : option unit) =>
                                               match el with
                                               | Some (Gtyp gt, HiF.Sink) => Some D_invalidated
                                               | _ => None
                                               end)
                                       pmap (CEP.empty unit)).
Proof.
induction ports as [|port ports'] ; simpl ; intros.
* injection H0 ; clear H H0 ; intros ; subst vm_port ct_port.
  injection H1 ; clear H1 ; intros ; subst pmap.
  split.
  + intro.
    by rewrite CEP.Lemmas.F.empty_o //.
  split.
  + intro.
    rewrite CEP.Lemmas.F.empty_o.
    symmetry ; apply CEP.Lemmas.F.not_find_in_iff ; intro.
    apply CEP.map_2, CEP.Lemmas.empty_in_iff in H.
    exact H.
  + intro.
    by rewrite CEP.Lemmas.F.empty_o CEP.Lemmas.F.map2_1bis //.
* split.
  + intro.
    destruct port as [port_name [port_fgtyp| |]|port_name [port_fgtyp| |]] ;
          try by discriminate H0.
    1,2: destruct (v == port_name) eqn: Hport_name_v.
    - 1,3: move /eqP : Hport_name_v => Hport_name_v.
      1-2: subst v.
      1-2: simpl code_type_find_vm_widths in H1.
      1-2: destruct (CEP.find port_name vm) as [[newgt|newgt|newgt _ _ _|newgt|newgt]|] ; last (by discriminate H1).
        1-10: destruct (code_vm_type_equivalent port_fgtyp newgt) ; last (by discriminate H1).
        1-10: destruct (ports_tmap ports' vm) ; last by discriminate H1.
        1-10: destruct (CEP.find port_name t) ; first by discriminate H1.
        1-10: injection H1 ; clear H1 ; intros ; subst pmap.
        1-10: rewrite CEP.Lemmas.find_add_eq // /PVM.SE.eq //.
    - 1-2: destruct (code_type_find_vm_widths (Gtyp port_fgtyp) port_name vm) as [[newt _]|] ; last by discriminate H1.
      1-2: move /andP : H => [_ H].
      1-2: destruct (ExpandPorts_fun ports') as [[vm_temp ct_temp]|] ; last by discriminate H0.
      1-2: specialize (IHports' vm_temp vm ct_temp) with (1 := H) (2 := Logic.eq_refl).
      1-2: destruct (ports_tmap ports' vm) as [pmap'|] ; last by discriminate H1.
      1-2: specialize (IHports' pmap' Logic.eq_refl).
      1-2: destruct IHports' as [IHports' _].
      1-2: specialize (IHports' v).
      1-2: destruct (CEP.find port_name pmap') ; first by discriminate H1.
      1-2: injection H1 ; clear H1 ; intros ; subst pmap.
      1-2: by rewrite CEP.Lemmas.find_add_neq // /PVM.SE.eq Hport_name_v //.
  split.
  + intro.
    rewrite CEP.Lemmas.map_o.
    destruct port as [port_name [port_fgtyp| |]|port_name [port_fgtyp| |]] ;
          try by discriminate H0.
    1,2: destruct (y == port_name) eqn: Hport_name_y.
    - 1,3: move /eqP : Hport_name_y => Hport_name_y.
      1-2: subst y.
      1-2: generalize (ExpandPorts_fun_submap ports') ; intro.
      1-2: destruct (ExpandPorts_fun ports') as [[vm_temp ct_temp]|] ; last by discriminate H0.
      1-2: injection H0 ; clear H0 ; intros ; subst vm_port ct_port.
      1-2: rewrite CEP.Lemmas.find_add_eq // ; last by rewrite /PVM.SE.eq //.
      1-2: simpl code_type_find_vm_widths in H1.
      1-2: destruct (CEP.find port_name vm) as [[newgt|newgt|newgt _ _ _|newgt|newgt]|] ; last (by discriminate H1).
        1-10: destruct (code_vm_type_equivalent port_fgtyp newgt) ; last (by discriminate H1).
        1-10: destruct (ports_tmap ports' vm) ; last by discriminate H1.
        1-10: destruct (CEP.find port_name t) ; first by discriminate H1.
        1-10: injection H1 ; clear H1 ; intros ; subst pmap.
        1-10: rewrite CEP.Lemmas.find_add_eq // /option_map /PVM.SE.eq //.
    - 1-2: destruct (code_type_find_vm_widths (Gtyp port_fgtyp) port_name vm) as [[newt _]|] ; last by discriminate H1.
      1-2: move /andP : H => [_ H].
      1-2: destruct (ExpandPorts_fun ports') as [[vm_temp ct_temp]|] ; last by discriminate H0.
      1-2: specialize (IHports' vm_temp vm ct_temp) with (1 := H) (2 := Logic.eq_refl).
      1-2: destruct (ports_tmap ports' vm) as [pmap'|] ; last by discriminate H1.
      1-2: specialize (IHports' pmap' Logic.eq_refl).
      1-2: destruct IHports' as [IHports' _].
      1-2: specialize (IHports' v).
      1-2: destruct (CEP.find port_name pmap') ; first by discriminate H1.
      1-2: injection H1 ; clear H1 ; intros ; subst pmap.
      1-2: by rewrite CEP.Lemmas.find_add_neq // /PVM.SE.eq Hport_name_v //.
    admit.
  + admit.
Admitted.

Theorem ExpandWhens_correct :
(* if ExpandWhens creates a new module and it has a certain semantic,
   then the previous module also has the same semantic. *)
    forall (m m' : HiFP.hfmodule)
           (vm : CEP.t vertex_type) (ct : CEP.t def_expr),
        ExpandWhens_fun m = Some m' ->
        Sem m' vm ct ->
            Sem m vm ct.
Proof.
intros.
unfold ExpandWhens_fun in H.
unfold Sem, ports_stmts_tmap in H0.
unfold Sem, ports_stmts_tmap.
destruct m as [m_name m_ports m_stmts|]; try by discriminate H.
destruct (ExpandPorts_fun) as [[vm_port ct_port]|] eqn: HExpandPorts ; try by discriminate H.
destruct (ExpandBranches_funs m_stmts (Qnil ProdVarOrder.T) ct_port vm_port)
         as [[[def_ss conn_map] final_scope]|] eqn: HexpandBranches ; try by discriminate H.
injection H ; clear H ; intros ; subst m'.
destruct (ports_tmap m_ports vm) as [pmap|] ; try by contradiction H0.
generalize (stmts_tmap_components vm m_stmts pmap pmap pmap
            (CEP.Lemmas.submap_refl pmap) (CEP.Lemmas.submap_refl pmap) (CEP.Lemmas.submap_refl pmap)) ; intro.
(* use a lemma to ensure that 
stmts_tmap (pmap, pmap) (Qcat def_ss ...) vm =
stmts_tmap (pmap, pmap) m_stmts           vm.
*)
























ExpandPorts_fun m_ports = Some (vm_port, ct_port) ->
    ports_tmap m_ports vm = Some pmap ->
            (forall v : CEP.key,
                match CEP.find v pmap with
                | Some (Atyp _ _, _) | Some (Btyp _, _) => False
                | _ => True
                end)
        /\
            CEP.Equal vm_port (CEP.map (fun el : ftype * HiF.forient =>
                                               match el with
                                               | (Gtyp gt, HiF.Source) => InPort gt
                                               | (Gtyp gt, HiF.Sink) => OutPort gt
                                               | _ => Node Freset)
                                       pmap)
        /\
            CEP.Equal ct_port (CEP.map2 (fun el _ : option (ftype * HiF.forient) =>
                                               match el with
                                               | Some (Gtyp gt, HiF.Sink) => Some D_invalidated
                                               | _ => None)
                                       pmap)

    (forall v1 v2 : N,
     match CEP.find (v1, v2) tmap with
     | Some (Atyp _ _, _) | Some (Btyp _, _) =>
         forall v2' : N, v2' <> v2 -> CEP.find (v1, v2') tmap = None
     | _ => True
     end) /\


