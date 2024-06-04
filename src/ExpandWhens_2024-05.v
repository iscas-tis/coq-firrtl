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

Definition fully_inferred
    (* checks the precondition of ExpandWhens on a type *)
    (gt : fgtyp) (* ground type to be checked *)
:   bool (* result is true iff the type has no implicit width or uninferred reset *)
:=  match gt with
    | Fuint_implicit _
    | Fsint_implicit _
    | Freset => false
    | _ => true
    end.

Fixpoint ports_have_fully_inferred_ground_types
    (* checks the precondition of ExpandWhens on a sequence of ports *)
    (pp : seq HiFP.hfport) (* sequence of ports to be checked *)
:   bool (* result is true iff the sequence of ports contains
             no aggregate types, no implicit widths, or uninferred resets *)
:=  match pp with
    | [::] => true
    | Finput  _ (Gtyp gt) :: pp'
    | Foutput _ (Gtyp gt) :: pp' => fully_inferred gt && ports_have_fully_inferred_ground_types pp'
    | _ => false
    end.

Definition tmap_has_fully_inferred_ground_types
    (* checks the precondition of ExpandWhens on a type map *)
    (tmap : CEP.t (ftype * HiF.forient)) (* type map to be checked *)
:   Prop (* result is True iff the type map contains
            no aggregate types, no implicit widths, or uninferred resets *)
:=  forall (v : ProdVarOrder.T),
        match CEP.find v tmap return Prop with
        | Some (Gtyp gt, _) => fully_inferred gt
        | Some _ => False
        | None => True
        end.

Fixpoint expr_has_fully_inferred_ground_types
    (* checks the precondition of ExpandWhens on an expression.
       It does not check the type of references. *)
    (expr : HiFP.hfexpr) (* expression to be checked *)
:   bool (* result is true iff the expression contains
            no uninferred resets in constants.
            (Constants never have an implicit width that cannot be made explicit trivially.) *)
:=  match expr with
    | Econst Freset _ => false
    | Econst _ _ => true
    | Ecast _ expr' => expr_has_fully_inferred_ground_types expr'
    | Eprim_unop _ expr' => expr_has_fully_inferred_ground_types expr'
    | Eprim_binop _ expr1 expr2 =>
            expr_has_fully_inferred_ground_types expr1
        &&
            expr_has_fully_inferred_ground_types expr2
    | Emux cond expr1 expr2 =>
            expr_has_fully_inferred_ground_types cond
        &&
            expr_has_fully_inferred_ground_types expr1
        &&
            expr_has_fully_inferred_ground_types expr2
    | Evalidif cond expr' =>
            expr_has_fully_inferred_ground_types cond
        &&
            expr_has_fully_inferred_ground_types expr'
    | Eref ref => ref_has_fully_inferred_ground_types ref
    end
with ref_has_fully_inferred_ground_types
    (* checks the precondition of ExpandWhens on a reference *)
    (ref : HiFP.href) (* reference to be checked *)
:   bool (* result is true if the expressions within the reference contain
            no uninferred resets in constants.
            (Constants never have an implicit width that cannot be made explicit trivially.) *)
:=  match ref with
    | Eid _ => true
    | Esubfield ref' _ => ref_has_fully_inferred_ground_types ref'
    | Esubindex _ _ (* Esubindex requires an array, which is not allowed after lowering types *)
    | Esubaccess _ _ => false (* Esubaccess is not allowed in the ExpandWhens phase *)
    end.

Definition ct_has_fully_inferred_ground_types
    (* checks the precondition of ExpandWhens on the edges of a module graph *)
    (ct : CEP.t def_expr) (* expression set / edge set to be checked *)
:   Prop (* result is True iff the expression set contains
            no aggregate types, no implicit widths, or uninferred resets *)
:=  forall k : CEP.key,
        if CEP.find k ct is Some (D_fexpr e)
        then expr_has_fully_inferred_ground_types e
        else true.

Fixpoint stmt_has_fully_inferred_ground_types
    (* checks the preconditin of ExpandWhens on a statement *)
    (s : HiFP.hfstmt) (* statement to be checked *)
:   bool (* result is true if the statements do not contain
            aggregate types, implicit widths or uninferred resets. *)
:=  match s with
    | Sskip => true
    | Swire _ (Gtyp gt) => fully_inferred gt
    | Swire _ _ => false
    | Sreg _ r =>
        match type r, reset r with
        | Gtyp gt, NRst =>
                expr_has_fully_inferred_ground_types (clock r)
            &&
                fully_inferred gt
        | Gtyp gt, Rst rst_sig rst_val =>
                expr_has_fully_inferred_ground_types rst_sig
            &&
                expr_has_fully_inferred_ground_types rst_val
            &&
                expr_has_fully_inferred_ground_types (clock r)
            &&
                fully_inferred gt
        | _, _ => false
        end
    | Smem _ m => if data_type m is Gtyp gt then fully_inferred gt else false
    | Sinvalid r => ref_has_fully_inferred_ground_types r
    | Sinst _ _ => false (* instances are not supported currently *)
    | Snode _ e => expr_has_fully_inferred_ground_types e
    | Sfcnct r e => ref_has_fully_inferred_ground_types r && expr_has_fully_inferred_ground_types e
    | Swhen cond ss_true ss_false =>
            expr_has_fully_inferred_ground_types cond
        &&
            stmts_have_fully_inferred_ground_types ss_true
        &&
            stmts_have_fully_inferred_ground_types ss_false
    end
with stmts_have_fully_inferred_ground_types
    (* checks the precondition of ExpandWhens on a statement sequence *)
    (ss : HiFP.hfstmt_seq) (* statement sequence to be checked *)
:   bool (* result is true iff the statement sequence does not contain
            aggregate types, implicit widths or uninferred resets *)
:=  match ss with
    | Qnil => true
    | Qcons s ss' =>
            stmt_has_fully_inferred_ground_types s
        &&
            stmts_have_fully_inferred_ground_types ss'
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
    (* create a module graph for the port sequence pp.
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

Definition convert_to_connect_stmt
    (* convert one entry in a map of connections to a connect statement,
       helper function for CEP.fold *)
    (v : CEP.key) (* key of the connection *)
    (d : def_expr) (* value of the connection *)
    (old_ss : HiFP.hfstmt_seq) (* old sequence of connect statements *)
:   HiFP.hfstmt_seq (* returns old_ss, extended with assigning d to v *)
:=  match d with
    | D_undefined => old_ss
    | D_invalidated => Qcons (Sinvalid (Eid v)) old_ss
    | D_fexpr e => Qcons (Sfcnct (Eid v) e) old_ss
    end.

Definition convert_to_connect_stmts
    (* converts a map of connections to connect statements *)
    (conn_map : CEP.t def_expr) (* map that needs to be converted *)
:   HiFP.hfstmt_seq
:=  CEP.fold convert_to_connect_stmt conn_map (Qnil ProdVarOrder.T).

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

(*---------------------------------------------------------------------------*)
(* Properties of fully-inferred types                                        *)

Lemma fully_inferred_does_not_change
    (* The lemma states that code_type_find_vm_widths cannot change
       an explicit type *)
:   forall (gt : fgtyp) (v : CEP.key) (vm : CEP.t vertex_type),
            fully_inferred gt
        ->
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

Lemma ports_tmap_preserves_fully_inferred
    (* This lemma states that fully inferred ports lead to a fully inferred type map. *)
:   forall (vm : CEP.t vertex_type) (pp : seq HiFP.hfport),
            ports_have_fully_inferred_ground_types pp
        ->
            match ports_tmap pp vm with
            | Some pmap => tmap_has_fully_inferred_ground_types pmap
            | None => True
            end.
Proof.
induction pp.
* simpl ; intro ; intro.
  rewrite CEP.Lemmas.empty_o //.
* simpl ; intro.
  destruct a, f ; try done.
  1,2: move /andP : H => [H H0].
  1,2: specialize (IHpp H0).
  1,2: generalize (fully_inferred_does_not_change f s vm H);
          intro.
  1,2: destruct (code_type_find_vm_widths (Gtyp f) s vm) as [[[newgt| |] _]|] ; try done.
  1,2: subst newgt.
  1,2: destruct (ports_tmap pp vm) ; last by trivial.
  1,2: destruct (CEP.find s t) ; first by trivial.
  1,2: intro.
  1,2: destruct (v == s) eqn: Hvs.
  1,3: rewrite CEP.Lemmas.find_add_eq ; first (by apply H) ;
       last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
  1,2: rewrite CEP.Lemmas.find_add_neq ; first (by apply IHpp) ;
       last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
Qed.

Lemma expr_preserves_fully_inferred :
forall scope : CEP.t (ftype * HiF.forient),
   tmap_has_fully_inferred_ground_types scope ->
      forall expr : HiFP.hfexpr,
         expr_has_fully_inferred_ground_types expr ->
            match type_of_expr expr scope return Prop with
            | Some (exist (Gtyp ft) _) => fully_inferred ft
            | Some _ => False
            | None => True
            end
with ref_preserves_fully_inferred :
forall scope : CEP.t (ftype * HiF.forient),
   tmap_has_fully_inferred_ground_types scope ->
      forall ref : HiFP.href,
         ref_has_fully_inferred_ground_types ref ->
            match type_of_ref ref scope return Prop with
            | Some (Gtyp ft, _) => fully_inferred ft
            | Some _ => False
            | None => True
            end.
Proof.
* clear expr_preserves_fully_inferred.
  induction expr ; simpl type_of_expr ; simpl expr_has_fully_inferred_ground_types ; intro.
  + destruct f ; done.
  + specialize (IHexpr H0) ; clear H0.
    destruct (type_of_expr expr scope) as [[[gt| |] _]|]; try done ;
    destruct u ; try done ;
    destruct gt ; done.
  + specialize (IHexpr H0) ; clear H0.
    destruct (type_of_expr expr scope) as [[[gt| |] _]|] ; try done ;
    destruct e ; try done ; destruct gt ; try done.
    - 1,2: destruct (n0 <= n < n1) ; by done.
    - 1,2,3,4: destruct (n <= n0) ; by done.
  + move /andP : H0 => [H0 H1].
    specialize (IHexpr1 H0) ; clear H0.
    specialize (IHexpr2 H1) ; clear H1.
    destruct (type_of_expr expr1 scope) as [[[gt1| |] _]|] ; try done ;
    destruct (type_of_expr expr2 scope) as [[[gt2| |] _]|] ; try done ;
    destruct e ; try done ;
    destruct gt1 ; try done ; destruct gt2 ; by done.
  + move /andP : H0 => [/andP [H0 H1] H2].
    specialize (IHexpr1 H0) ; clear H0.
    specialize (IHexpr2 H1) ; clear H1.
    specialize (IHexpr3 H2) ; clear H2.
    destruct (type_of_expr expr1 scope) as [[[[[|[|]]| | | | | |]| |] _]|] ; try done.
    destruct (type_of_expr expr2 scope) as [[[gt2| |] p2]|] ; try done ;
    destruct (type_of_expr expr3 scope) as [[[gt3| |] p3]|] ; try done ;
    unfold ftype_mux ; simpl ftype_mux'.
    destruct gt2, gt3 ; by done.
  + move /andP : H0 => [H0 H1].
    specialize (IHexpr1 H0) ; clear H0.
    specialize (IHexpr2 H1) ; clear H1.
    destruct (type_of_expr expr1 scope) as [[[[[|[|]]| | | | | |]| |] _]|] ; by done.
  + specialize (ref_preserves_fully_inferred scope H h H0).
    destruct (type_of_ref h scope) as [[[gt| |] ori]|]; try done.
    destruct ori, gt ; by done.
* clear ref_preserves_fully_inferred.
  induction ref ; simpl type_of_ref ; simpl ref_has_fully_inferred_ground_types ; intro.
  + by apply H.
  + specialize (IHref H0).
    destruct (type_of_ref ref scope) as [[[| |] ori]|] ; by done.
  + by discriminate H0.
  + by discriminate H0.
Qed.

Lemma stmt_tmap_preserves_fully_inferred :
forall (vm : CEP.t vertex_type) (tmap scope : CEP.t (ftype * HiF.forient)) (s : HiFP.hfstmt),
   stmt_has_fully_inferred_ground_types s ->
   tmap_has_fully_inferred_ground_types tmap ->
   CEP.submap scope tmap ->
      match stmt_tmap (tmap, scope) s vm with
      | Some (tmap', _) => tmap_has_fully_inferred_ground_types tmap'
      | _ => True
      end
with stmts_tmap_preserves_fully_inferred :
forall (vm : CEP.t vertex_type) (ss : HiFP.hfstmt_seq) (tmap scope : CEP.t (ftype * HiF.forient)),
   stmts_have_fully_inferred_ground_types ss ->
   tmap_has_fully_inferred_ground_types tmap ->
   CEP.submap scope tmap ->
      match stmts_tmap (tmap, scope) ss vm with
      | Some (tmap', _) => tmap_has_fully_inferred_ground_types tmap'
      | _ => True
      end.
Proof.
* clear stmt_tmap_preserves_fully_inferred.
  destruct s ; intros ; try done.
  + (* Swire *)
    simpl stmt_tmap.
    destruct (CEP.find s tmap) ; first by trivial.
    unfold stmt_has_fully_inferred_ground_types in H.
    destruct f as [gt| |]; try done.
    generalize (fully_inferred_does_not_change gt s vm H) ;
          intro.
    destruct (code_type_find_vm_widths (Gtyp gt) s vm) as [[[newgt| |] _]|] ;
        try by done.
    rewrite -H2 ; clear H2 newgt.
    intro.
    destruct (v == s) eqn: Hvs ; first by rewrite CEP.Lemmas.find_add_eq //.
    rewrite CEP.Lemmas.find_add_neq // ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
    by apply H0.
  + (* Sreg *)
    simpl stmt_tmap.
    destruct (CEP.find s tmap) ; first by trivial.
    destruct (type_of_expr (clock h) scope) ; last by trivial.
    unfold stmt_has_fully_inferred_ground_types in H.
    destruct (type h) as [gt| |]; try done.
    generalize (fully_inferred_does_not_change gt s vm) ;
          intro.
    destruct (code_type_find_vm_widths (Gtyp gt) s vm) as [[[newgt| |] _]|] ;
        destruct (reset h) ;
        move /andP : H => [H H'] ;
        specialize (H2 H') ;
        try by done.
    1,2: rewrite -H2 ; clear H2 newgt.
    2: destruct (type_of_expr h0 scope) as [[[[[|[]]| | | | | |]| |] _]|] ; try by trivial.
    2: destruct (type_of_expr h1 (CEP.add s (Gtyp gt, HiF.Duplex) scope)) ; last by trivial.
    3: destruct (type_of_expr h1 scope) ; last by trivial.
    1-3: intro.
    1-3: destruct (v == s) eqn: Hvs ; first by rewrite CEP.Lemmas.find_add_eq //.
    1-3: rewrite CEP.Lemmas.find_add_neq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
    1-3: by apply H0.
  + (* Snode *)
    simpl stmt_tmap.
    destruct (CEP.find s tmap) ; first by trivial.
    assert (tmap_has_fully_inferred_ground_types scope).
          intro.
          specialize (H1 v).
          destruct (CEP.find v scope) as [p|] ; try done.
          specialize (H0 v).
          rewrite (H1 p Logic.eq_refl) in H0.
          by exact H0.
    simpl stmt_has_fully_inferred_ground_types in H.
    generalize (expr_preserves_fully_inferred scope H2 h H) ; intro.
    destruct (type_of_expr h scope) as [[newt _]|] ; last by trivial.
    intro.
    destruct (v == s) eqn: Hvs ; first by rewrite CEP.Lemmas.find_add_eq //.
    rewrite CEP.Lemmas.find_add_neq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
    by apply H0.
  + (* Sfcnct *)
    simpl stmt_tmap.
    simpl stmt_has_fully_inferred_ground_types in H.
    destruct (type_of_ref h scope) ; last by done.
    destruct (type_of_expr h0 scope) ; last by done.
    by exact H0.
  + (* Sinvalid *)
    simpl stmt_tmap.
    destruct (type_of_ref h scope) ; last by done.
    by exact H0.
  + (* Swhen *)
    rename h into cond ; rename h0 into ss_true ; rename h1 into ss_false.
    simpl stmt_tmap.
    destruct (type_of_expr cond scope) ; last by done.
    simpl stmt_has_fully_inferred_ground_types in H.
    move /andP : H => [/andP [_ Ht] Hf].
    generalize (stmts_tmap_preserves_fully_inferred vm ss_true tmap scope Ht H0 H1) ;
          intro.
    generalize (stmts_submap vm ss_true tmap scope H1) ;
          intro.
    destruct (stmts_tmap (tmap, scope) ss_true vm) as [[tmap_true scope_true]|] ; try done.
    specialize (stmts_tmap_preserves_fully_inferred vm ss_false tmap_true scope Hf H).
    destruct (stmts_tmap (tmap_true, scope) ss_false vm) as [[tmap_false _]|] ; try done.
    apply stmts_tmap_preserves_fully_inferred.
    by apply (CEP.Lemmas.submap_trans H1), H2.
* clear stmts_tmap_preserves_fully_inferred.
  induction ss ; intros ; try done.
  simpl stmts_tmap.
  simpl in H ; move /andP : H => [H H'].
  specialize (stmt_tmap_preserves_fully_inferred vm tmap scope h H H0 H1).
  generalize (stmt_submap vm h tmap scope H1) ;
      intro.
  destruct (stmt_tmap (tmap, scope) h vm) as [[tmap' scope']|] ; try done.
  specialize (IHss tmap' scope' H' stmt_tmap_preserves_fully_inferred (proj1 H2)).
  destruct (stmts_tmap (tmap', scope') ss vm) as [[tmap'' _]|] ; by done.
Qed.

(*---------------------------------------------------------------------------*)
(* Relating different properties of ports                                    *)

Definition vm_and_tmap_compatible
    (* checks whether a vertex set vm and a type map tmap are compatible,
       i.e. whether the type map could have been created from vm or a superset of vm. *)
    (vm : CEP.t vertex_type) (* vertex set *)
    (tmap : CEP.t (ftype * HiF.forient)) (* tmap *)
:   Prop
:=  CEP.submap (CEP.map (fun v : vertex_type
                         => match v with
                            | OutPort gt => (Gtyp gt, HiF.Sink)
                            | InPort gt
                            | Node gt => (Gtyp gt, HiF.Source)
                            | Register gt _ _ _
                            | Wire gt => (Gtyp gt, HiF.Duplex)
                            end)
                         vm) tmap.

Lemma ExpandPorts_fun_submap :
    forall (ports : seq HiFP.hfport) (vm_old vm_new vm_port vm_old_port : CEP.t vertex_type)
           (ct_old ct_new ct_port : CEP.t def_expr) (tmap port_tmap : CEP.t (ftype * HiF.forient)),
    ports_have_fully_inferred_ground_types ports ->
    ports_tmap ports vm_old_port = Some port_tmap ->
    CEP.submap port_tmap tmap (* we need this submap to get the induction, but one would normally set port_tmap = tmap. *) ->
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
          1-2: move /eqP : H => H.
          1-2: rewrite -(nat_of_binK k.2) H nat_of_binK //.
    1-2: rewrite -(proj1 (H3 H0)).
    1-2: apply IHports'.
    1-2: move /negP : Hport_name_k => Hport_name_k.
    1-2: rewrite CEP.Lemmas.find_add_neq // in H5.
Qed.

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
(*
            CEP.Equal vm_port (CEP.map (fun el : ftype * HiF.forient =>
                                               match el with
                                               | (Gtyp gt, HiF.Source) => InPort gt
                                               | (Gtyp gt, HiF.Sink) => OutPort gt
                                               | _ => Node Freset
                                               end)
                                       pmap)
*)
            (* The following is slightly stronger than (vm_and_tmap_compatible vm_port pmap). *)
            CEP.Equal (CEP.map (fun v : vertex_type
                               => match v with
                                  | OutPort gt => (Gtyp gt, HiF.Sink)
                                  | InPort gt
                                  | Node gt => (Gtyp gt, HiF.Source)
                                  | Register gt _ _ _
                                  | Wire gt => (Gtyp gt, HiF.Duplex)
                                  end)
                               vm_port) pmap
        /\
            (* The following is slightly stronger than (vm_and_ct_compatible vm_port ct_port). *)
            CEP.Equal ct_port (CEP.map2 (fun (el : option (ftype * HiF.forient)) (_ : option unit) =>
                                               match el with
                                               | Some (Gtyp gt, HiF.Sink) => Some D_undefined
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
    apply CEP.Lemmas.F.not_find_in_iff ; intro.
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
      1-2: destruct (ExpandPorts_fun ports') as [[vm_temp ct_temp]|] ; last by discriminate H0.
      1-2: injection H0 ; clear H0 ; intros ; subst vm_port ct_port.
      1-2: rewrite CEP.Lemmas.find_add_eq // ; last by rewrite /PVM.SE.eq //.
      1-2: move /andP : H => [H _].
      1-2: generalize (fully_inferred_does_not_change port_fgtyp port_name vm H) ; intro.
      1-2: destruct (code_type_find_vm_widths (Gtyp port_fgtyp) port_name vm) as [[[port_fgtyp'| |] _]|] ;
                 last (by discriminate H1) ;
                 try (by contradiction H0) ;
                 subst port_fgtyp'.
      1-2: destruct (ports_tmap ports' vm) ; last by discriminate H1.
      1-2: destruct (CEP.find port_name t) ; first by discriminate H1.
      1-2: injection H1 ; clear H1 ; intros ; subst pmap.
      1-2: by rewrite CEP.Lemmas.find_add_eq // /option_map /PVM.SE.eq //.
    - 1-2: destruct (code_type_find_vm_widths (Gtyp port_fgtyp) port_name vm) as [[newt _]|] ; last by discriminate H1.
      1-2: move /andP : H => [_ H].
      1-2: destruct (ExpandPorts_fun ports') as [[vm_temp ct_temp]|] ; last by discriminate H0.
      1-2: specialize (IHports' vm_temp vm ct_temp) with (1 := H) (2 := Logic.eq_refl).
      1-2: destruct (ports_tmap ports' vm) as [pmap'|] ; last by discriminate H1.
      1-2: injection H0 ; clear H0 ; intros ; subst vm_port ct_port.
      1-2: move /negP : Hport_name_y => Hport_name_y.
      1-2: rewrite CEP.Lemmas.find_add_neq //.
      1-2: destruct (CEP.find port_name pmap') ; first by discriminate H1.
      1-2: injection H1 ; clear H1 ; intros ; subst pmap.
      1-2: rewrite CEP.Lemmas.find_add_neq //.
      1-2: specialize (IHports' pmap' Logic.eq_refl).
      1-2: destruct IHports' as [_ [IHports' _]].
      1-2: specialize (IHports' y).
      1-2: by rewrite CEP.Lemmas.map_o // in IHports'.
  + intro.
    rewrite CEP.Lemmas.map2_1bis //.
    destruct port as [port_name [port_fgtyp| |]|port_name [port_fgtyp| |]] ;
          try by discriminate H0.
    1,2: destruct (y == port_name) eqn: Hport_name_y.
    - 1,2,4: destruct (code_type_find_vm_widths (Gtyp port_fgtyp) port_name vm) as [[newt _]|] ; last by discriminate H1.
      1-3: move /andP : H => [_ H].
      1-3: destruct (ExpandPorts_fun ports') as [[vm_temp ct_temp]|] ; last by discriminate H0.
      1-3: specialize (IHports' vm_temp vm ct_temp) with (1 := H) (2 := Logic.eq_refl).
      1-3: destruct (ports_tmap ports' vm) as [pmap'|] ; last by discriminate H1.
      1-3: injection H0 ; clear H0 ; intros ; subst vm_port ct_port.
        2-3: move /negP : Hport_name_y => Hport_name_y.
          3: rewrite CEP.Lemmas.find_add_neq //.
      1-3: destruct (CEP.find port_name pmap') eqn: Hpm ; first by discriminate H1.
      1-3: injection H1 ; clear H1 ; intros ; subst pmap.
        1: rewrite CEP.Lemmas.find_add_eq //.
        2-3: rewrite CEP.Lemmas.find_add_neq //.
      1-3: specialize (IHports' pmap' Logic.eq_refl).
      1-3: destruct IHports' as [_ [_ IHports']].
      1-3: specialize (IHports' y).
      1-3: rewrite CEP.Lemmas.map2_1bis // in IHports'.
      move /eqP : Hport_name_y => Hport_name_y ; subst y.
      rewrite Hpm in IHports'.
      destruct newt ; exact IHports'.
    - move /eqP : Hport_name_y => Hport_name_y.
      subst y.
      destruct (ExpandPorts_fun ports') as [[vm_temp ct_temp]|] ; last by discriminate H0.
      injection H0 ; clear H0 ; intros ; subst vm_port ct_port.
      rewrite CEP.Lemmas.find_add_eq // ; last by rewrite /PVM.SE.eq //.
      move /andP : H => [H _].
      generalize (fully_inferred_does_not_change port_fgtyp port_name vm H) ; intro.
      destruct (code_type_find_vm_widths (Gtyp port_fgtyp) port_name vm) as [[[port_fgtyp'| |] _]|] ;
            last (by discriminate H1) ;
            try (by contradiction H0) ;
            subst port_fgtyp'.
      destruct (ports_tmap ports' vm) ; last by discriminate H1.
      destruct (CEP.find port_name t) ; first by discriminate H1.
      injection H1 ; clear H1 ; intros ; subst pmap.
      by rewrite CEP.Lemmas.find_add_eq // /option_map /PVM.SE.eq //.
Qed.

(*---------------------------------------------------------------------------*)
(* Relation between expression translations                                  *)

Lemma type_of_expr_and_rhs_type_of_expr :
forall (e : HiFP.hfexpr) (vm : CEP.t vertex_type) (tmap: CEP.t (ftype * HiF.forient)),
        expr_has_fully_inferred_ground_types e
    ->
        tmap_has_fully_inferred_ground_types tmap
    ->
        vm_and_tmap_compatible vm tmap
    ->
        match rhs_type_of_expr e vm with
        | Some (exist gt p) =>
                fully_inferred gt
            /\
                type_of_expr e tmap = Some (exist ftype_not_implicit_width (Gtyp gt) p)
        | None => True
        end
with type_of_ref_and_rhs_type_of_ref :
forall (r : HiFP.href) (vm : CEP.t vertex_type) (tmap: CEP.t (ftype * HiF.forient)),
        ref_has_fully_inferred_ground_types r
    ->
        tmap_has_fully_inferred_ground_types tmap
    ->
        vm_and_tmap_compatible vm tmap
    ->
        match rhs_type_of_ref r vm with
        | Some gt =>
                fully_inferred gt
            /\
                (   type_of_ref r tmap = Some (Gtyp gt, HiF.Source)
                \/
                    type_of_ref r tmap = Some (Gtyp gt, HiF.Duplex))
        | None => True
        end.
Proof.
* clear type_of_expr_and_rhs_type_of_expr.
  intros.
  induction e ; simpl.
  + (* Econst *)
    destruct f ; by done.
  + (* Ecast *)
    specialize (IHe H).
    destruct u, (rhs_type_of_expr e vm) as [[[| | | | | |] p]|] ;
          try (unfold Fuint_exp) ;
          try (unfold Fsint_exp) ;
          try done ;
          by (split ; first (by done) ;
              rewrite (proj2 IHe) //).
  + (* Eprim_unop *)
    specialize (IHe H).
    destruct e, (rhs_type_of_expr e0 vm) as [[[| | | | | |] p]|] ;
          try (unfold Fuint_exp) ;
          try (unfold Fsint_exp) ;
          try done ;
          rewrite (proj2 IHe) // ;
          try (destruct (n0 <= n < n1) ; by done) ;
          (destruct (n <= n0) ; by done).
  + (* Eprim_binop *)
    simpl in H.
    move /andP : H => H.
    specialize (IHe1 (proj1 H)).
    specialize (IHe2 (proj2 H)).
    destruct e1, (rhs_type_of_expr e2 vm) as [[[| | | | | |] p1]|],
                 (rhs_type_of_expr e3 vm) as [[[| | | | | |] p2]|] ;
          try (unfold Fuint_exp) ;
          try (unfold Fsint_exp) ;
          try done ;
          rewrite (proj2 IHe1) (proj2 IHe2) //.
  + (* Emux *)
    simpl in H.
    move /andP : H => [/andP H H'].
    specialize (IHe1 (proj1 H)).
    specialize (IHe2 (proj2 H)).
    specialize (IHe3 H').
    destruct (rhs_type_of_expr e1 vm) as [[[[|[|]]| | | | | |] p1]|],
             (rhs_type_of_expr e2 vm) as [[[| | | | | |] p2]|],
             (rhs_type_of_expr e3 vm) as [[[| | | | | |] p3]|] ;
          try done ;
          rewrite (proj2 IHe1) (proj2 IHe2) (proj2 IHe3) /fgtyp_mux //.
  + (* Evalidif *)
    simpl in H.
    move /andP : H => H.
    specialize (IHe1 (proj1 H)).
    specialize (IHe2 (proj2 H)).
    destruct (rhs_type_of_expr e1 vm) as [[[[|[|]]| | | | | |] p1]|],
             (rhs_type_of_expr e2 vm) as [[[| | | | | |] p2]|] ;
          try done ;
          rewrite (proj2 IHe1) (proj2 IHe2) /fgtyp_mux //.
    by discriminate (proj1 IHe2).
  + (* Eref *)
    simpl in H.
    specialize (type_of_ref_and_rhs_type_of_ref h vm tmap H H0 H1).
    destruct (rhs_type_of_ref h vm) as [[| | | | | |]|] ;
          try (by discriminate (proj1 type_of_ref_and_rhs_type_of_ref)) ;
          split ; try done ;
          destruct type_of_ref_and_rhs_type_of_ref as [_ [Hsd|Hsd]] ;
          by rewrite Hsd //.
* (* reference *)
  clear type_of_ref_and_rhs_type_of_ref.
  intros.
  induction r.
  + (* Eid *)
    simpl.
    specialize (H0 s).
    specialize (H1 s).
    rewrite CEP.Lemmas.F.map_o /option_map in H1.
    destruct (CEP.find s vm) as [[| | | |]|] ;
          try (by done) ;
          specialize (H1 _ Logic.eq_refl) ;
          rewrite H1 in H0 ;
          (split ; first by exact H0) ;
          try (left ; done) ;
          right ; done.
  + (* Esubfield *)
    (* TBD for memory and instances *)
    simpl ; done.
  + (* Esubindex *)
    by discriminate H.
  + (* Esubaccess *)
    by discriminate H.
Qed.

Lemma type_of_ref_and_lhs_type_of_ref :
forall (r : HiFP.href) (vm : CEP.t vertex_type) (tmap: CEP.t (ftype * HiF.forient)),
        ref_has_fully_inferred_ground_types r
    ->
        tmap_has_fully_inferred_ground_types tmap
    ->
        vm_and_tmap_compatible vm tmap
    ->
        match lhs_type_of_ref r vm with
        | Some gt =>
                fully_inferred gt
            /\
                (   type_of_ref r tmap = Some (Gtyp gt, HiF.Sink)
                \/
                    type_of_ref r tmap = Some (Gtyp gt, HiF.Duplex))
        | None => True
        end.
Proof.
induction r ; simpl ; intros ; try by trivial.
specialize (H0 s).
specialize (H1 s).
rewrite CEP.Lemmas.map_o /option_map in H1.
destruct (PVM.find s vm) as [[gt|gt|gt|gt|gt]|] ; try by trivial.
1-3: specialize H1 with (1 := Logic.eq_refl).
1-3: split ;
           first by (rewrite H1 in H0 ; exact H0).
1-3: rewrite H1.
- left ; reflexivity.
- 1,2: right ; reflexivity.
Qed.

(*---------------------------------------------------------------------------*)
(* Properties of connection maps                                             *)

Definition extend_defined_map_with
    (* Returns map m, except that undefined elements are copied from dflt.
       “undefined” here includes expressions that are assigned an undefined value *)
    (m (* main map whose values are all used *)
     dflt : CEP.t def_expr) (* default: values are used where m does not define an expression *)
:   CEP.t def_expr
:=  CEP.map2 (fun (elm eld : option def_expr)
              => match elm with
                 | Some D_undefined | None => eld
                 | _ => elm
                 end)
             m dflt.

Lemma convert_to_connect_stmts_Sem :
(* a lemma that states that helper_connect and Sem_frag_stmts are sort of inverses *)
forall (conn_map : CEP.t def_expr) (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap: CEP.t (ftype * HiF.forient)),
    tmap_has_fully_inferred_ground_types tmap ->
    ct_has_fully_inferred_ground_types conn_map ->
            (Sem_frag_stmts vm_old ct_old (convert_to_connect_stmts conn_map) vm_new ct_new tmap ->
                    CEP.Equal vm_old vm_new
                /\
                    CEP.Equal ct_new (extend_defined_map_with conn_map ct_old))
        (*/\
            (vm_and_ct_compatible vm_old ct_old ->
            CEP.submap conn_map ct_old ->
            CEP.Equal vm_old vm_new ->
            CEP.Equal ct_new (extend_defined_map_with conn_map ct_old) ->
            "type correctness according to tmap" ->
            (* or perhaps write something like a weak semantics, i.e.
               "if there is no error, then ..." *)
                Sem_frag_stmts vm_old ct_old (CEP.fold helper_connect conn_map (Qnil ProdVarOrder.T)) vm_new ct_new tmap)*).
Proof.
intros until 2.
(*split.*)
* rewrite /convert_to_connect_stmts CEP.Lemmas.P.fold_spec_right.
  assert (SetoidList.equivlistA (@CEP.Lemmas.O.eqke def_expr)
                                (List.rev (CEP.elements conn_map))
                                (CEP.elements conn_map))
        by (intro ;
            apply (SetoidList.InA_rev (@CEP.Lemmas.O.eqke def_expr))).
  revert H1.
  generalize (CEP.elements_3w conn_map) ; intro.
(*  assert (Heqv_key : RelationClasses.Equivalence (CEP.eq_key (elt:=def_expr))).
        clear.
        assert (forall x : CEP.key * def_expr, CEP.eq_key x x)
              by (intro ; rewrite /CEP.eq_key /CEP.SE.eq eq_refl //).
        assert (forall x y : CEP.key * def_expr, CEP.eq_key x y -> CEP.eq_key y x)
              by (intros ; rewrite /CEP.eq_key /CEP.SE.eq eq_sym H0 //).
        assert (forall x y z : CEP.key * def_expr, CEP.eq_key x y -> CEP.eq_key y z -> CEP.eq_key x z)
              by (intros ; rewrite H1 H2 /CEP.eq_key /CEP.SE.eq //).
        exact (RelationClasses.Build_Equivalence (CEP.eq_key (elt:=def_expr)) H H0 H1).
  assert (Heqv_key_elt : RelationClasses.Equivalence (CEP.eq_key_elt (elt:=def_expr))).
        clear.
        assert (forall x : CEP.key * def_expr, CEP.eq_key_elt x x)
              by (destruct x ; split ; first (by rewrite /CEP.SE.eq eq_refl //) ; last (by reflexivity)).
        assert (forall x y : CEP.key * def_expr, CEP.eq_key_elt x y -> CEP.eq_key_elt y x)
              by (destruct x, y ; split ; first (by rewrite /CEP.SE.eq eq_sym (proj1 H0) //) ; last (by symmetry ; apply H0)).
        assert (forall x y z : CEP.key * def_expr, CEP.eq_key_elt x y -> CEP.eq_key_elt y z -> CEP.eq_key_elt x z)
              by (destruct x, y, z ; split ; first (by rewrite (proj1 H1) (proj1 H2) /CEP.SE.eq //) ;
                  last (by apply (eq_trans (proj2 H1) (proj2 H2)))).
        exact (RelationClasses.Build_Equivalence (CEP.eq_key_elt (elt:=def_expr)) H H0 H1).*)
  assert (Heqv_key0 : RelationClasses.Equivalence (fun x y : ProdVarOrder.T => x == y)).
        clear.
        assert (forall x y : ProdVarOrder.T, x == y -> y == x)
              by (intros ; rewrite eq_sym //).
        assert (forall x y z : ProdVarOrder.T, x == y -> y == z -> x == z)
              by (intros ; move /eqP : H0 => H0 ; rewrite H0 //).
        exact (RelationClasses.Build_Equivalence (fun x y : ProdVarOrder.T => x == y) (eq_refl (T := ProdVarOrder.T)) H H0).
  apply SetoidList.NoDupA_rev in H1 ; last by apply (CEP.Lemmas.O.eqk_equiv def_expr).
  revert H0 H1.
  generalize (List.rev (CEP.elements conn_map)) as conn_map_list.
  intro ; revert conn_map_list vm_old ct_old conn_map.
  induction conn_map_list.
  + unfold List.fold_right.
    intros.
    split ; first by apply H3.
    intro.
    apply RelationClasses.Equivalence_Symmetric, SetoidList.equivlistA_nil_eq in H2 ;
          last by exact (CEP.Lemmas.O.eqke_equiv def_expr).
    apply CEP.Lemmas.P.elements_Empty in H2.
    apply CEP.Lemmas.Empty_find with (x := y) in H2.
    simpl Sem_frag_stmts in H3.
    unfold extend_map_with.
    rewrite CEP.Lemmas.map2_1bis // H2.
    symmetry ; apply H3.
  + destruct a as [k v].
    simpl List.fold_right.
    intros until 3.
    (*destruct (List.fold_right (CEP.Lemmas.P.uncurry helper_connect)
                              (Qnil ProdVarOrder.T) conn_map_list) eqn: Hfold ;
          rewrite Hfold // /CEP.Lemmas.P.uncurry /helper_connect /fst /snd.
    rewrite Hfold in IHconn_map_list.*)
    inversion H1 ; clear H3 H4 x l.
    assert (forall k : CEP.key,
                match CEP.find k (CEP.Lemmas.P.of_list conn_map_list) with
                | Some (D_fexpr e) => expr_has_fully_inferred_ground_types e
                | _ => true
                end).
          intro.
          generalize (CEP.find_2 (m := CEP.Lemmas.P.of_list conn_map_list) (x := k0)) ; intro.
          destruct (CEP.find k0 (CEP.Lemmas.P.of_list conn_map_list)) as [[]|] ; try done.
          specialize (H3 (D_fexpr h) Logic.eq_refl).
          apply (CEP.Lemmas.P.of_list_1 k0 (D_fexpr h) H6), (SetoidList.InA_cons_tl (k, v)),
                H2, CEP.Lemmas.elements_mapsto_iff, CEP.find_1 in H3.
          specialize (H0 k0) ; rewrite H3 // in H0.
    destruct v.
    - (* D_undefined *)
      unfold CEP.Lemmas.P.uncurry ; simpl Sem_frag_stmts.
      intro.
      specialize (IHconn_map_list vm_old ct_old (CEP.Lemmas.P.of_list conn_map_list)
                                  H3 H6 (CEP.Lemmas.P.of_list_2 H6) H4).
      split ; first by apply IHconn_map_list.
      apply (CEP.Lemmas.Equal_trans (proj2 IHconn_map_list)).
      intro.
      unfold extend_map_with.
      rewrite CEP.Lemmas.map2_1bis // (*CEP.Lemmas.P.of_list_1b //. *)
              CEP.Lemmas.map2_1bis //.
      (*
      specialize (H k).
      destruct (CEP.find k tmap) as [[gt| |]|] ; try by contradiction.
      rewrite /size_of_ftype /mkseq in H3 ; simpl in H3.
      rewrite N.add_0_r -surjective_pairing in H3. *)
      destruct (y == k) eqn: Hyk.
      + move /eqP : Hyk => Hyk.
        rewrite Hyk.
        destruct (PVM.find k (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
        - contradict H5.
          apply (SetoidList.InA_eqA (CEP.Lemmas.O.eqk_equiv def_expr) (x := (k, d))) ;
                first by rewrite /CEP.Lemmas.O.eqk /fst /CEP.SE.eq //.
          apply SetoidList.In_InA ; first by exact (CEP.Lemmas.O.eqk_equiv def_expr).
          rewrite CEP.Lemmas.P.of_list_1b // in Hfind_list.
          apply SetoidList.findA_NoDupA in Hfind_list ;
                last (by exact H6) ;
                last (by exact Heqv_key0).
          apply SetoidList.InA_alt in Hfind_list.
          destruct Hfind_list as [[k' d'] [[Hk Hd] Hfind_list]].
          move /eqP : Hk => Hk.
          simpl in Hk, Hd.
          subst k' d'.
          exact Hfind_list.
        - (* use H2 to show that PVM.find k conn_map = D_undefined *)
          rewrite (CEP.Lemmas.elements_o conn_map k).
          generalize (SetoidList.findA_NoDupA Heqv_key0 HiFP.PVSLemmas.P.FM.eq_dec
                      (l := CEP.elements conn_map) k D_undefined (CEP.elements_3w conn_map)) ; intro.
          rewrite (proj1 H7) //.
          apply H2, SetoidList.InA_cons_hd.
          rewrite /CEP.Lemmas.O.eqke /PVM.SE.eq eq_refl /snd ; split ; by done.
      + destruct (PVM.find y (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
        - specialize (H2 (y, d)).
          destruct H2 as [H2 _].
          rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by apply H6.
          apply SetoidList.findA_NoDupA in Hfind_list ;
                last (by apply H6) ; last by apply Heqv_key0.
          apply SetoidList.InA_cons_tl with (y := (k, D_undefined)) in Hfind_list.
          apply H2, CEP.elements_2, CEP.find_1 in Hfind_list.
          rewrite Hfind_list //.
        - destruct (PVM.find y conn_map) eqn: Hfind_map.
          * apply CEP.find_2, CEP.elements_1, H2, SetoidList.InA_cons in Hfind_map.
            destruct Hfind_map as [Hfind_map|Hfind_map] ;
                  first (by rewrite /CEP.Lemmas.O.eqke /PVM.SE.eq /fst Hyk in Hfind_map ;
                            destruct Hfind_map as [Hfind_map _] ; done).
            rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by exact H6.
            apply (SetoidList.findA_NoDupA Heqv_key0 ProdVarOrder.eq_dec y d H6) in Hfind_map.
            rewrite Hfind_map // in Hfind_list.
          * by reflexivity.
    - (* D_invalidated *)
      simpl Sem_frag_stmts.
      intro.
      destruct H4 as [vm' [ct' [[H4 H7] H8]]].
      specialize (IHconn_map_list vm' ct' (CEP.Lemmas.P.of_list conn_map_list)
                                  H3 H6 (CEP.Lemmas.P.of_list_2 H6) H8).
      split ; first by apply (CEP.Lemmas.Equal_trans H4), IHconn_map_list.
      apply (CEP.Lemmas.Equal_trans (proj2 IHconn_map_list)).
      intro.
      unfold extend_map_with.
      rewrite CEP.Lemmas.map2_1bis // (*CEP.Lemmas.P.of_list_1b //. *)
              CEP.Lemmas.map2_1bis //.
      specialize (H k).
      destruct (CEP.find k tmap) as [[[gt| |] ori]|] ; try by contradiction.
      rewrite /size_of_ftype /mkseq in H7 ; simpl in H7.
      rewrite N.add_0_r -surjective_pairing in H7.
      destruct (y == k) eqn: Hyk.
      + move /eqP : Hyk => Hyk.
        rewrite Hyk.
        destruct (PVM.find k (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
        - contradict H5.
          apply (SetoidList.InA_eqA (CEP.Lemmas.O.eqk_equiv def_expr) (x := (k, d))) ;
                first by rewrite /CEP.Lemmas.O.eqk /fst /CEP.SE.eq //.
          apply SetoidList.In_InA ; first by exact (CEP.Lemmas.O.eqk_equiv def_expr).
          rewrite CEP.Lemmas.P.of_list_1b // in Hfind_list.
          apply SetoidList.findA_NoDupA in Hfind_list ;
                last (by exact H6) ;
                last (by exact Heqv_key0).
          apply SetoidList.InA_alt in Hfind_list.
          destruct Hfind_list as [[k' d'] [[Hk Hd] Hfind_list]].
          move /eqP : Hk => Hk.
          simpl in Hk, Hd.
          subst k' d'.
          exact Hfind_list.
        - (* use H2 to show that PVM.find k conn_map = D_invalidated *)
          rewrite (CEP.Lemmas.elements_o conn_map k).
          generalize (SetoidList.findA_NoDupA (B := def_expr) Heqv_key0) ; intro.
          specialize H9 with (eqA_dec := HiFP.PVSLemmas.P.FM.eq_dec) (l := CEP.elements conn_map) (a := k) (b := D_invalidated) (1 := CEP.elements_3w conn_map).
          rewrite (proj1 H9).
          * destruct ori ; try by contradiction H7.
            1,2: destruct H7 as [H7 _] ; specialize (H7 0) ; simpl in H7.
            1,2: by apply H7.
          * apply H2, SetoidList.InA_cons_hd.
            rewrite /CEP.Lemmas.O.eqke /PVM.SE.eq eq_refl /snd ; split ; by done.
      + destruct ori ; try by contradiction H7.
        1,2: destruct H7 as [_ H7].
        1,2: specialize (H7 y).
        1,2: rewrite mem_seq1 Hyk in H7.
        1,2: rewrite -H7.
        1,2: destruct (PVM.find y (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
        - 1,3: specialize (H2 (y, d)).
          1,2: rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by apply H6.
          1,2: apply SetoidList.findA_NoDupA in Hfind_list ;
                last (by apply H6) ; last by apply Heqv_key0.
          1,2: apply SetoidList.InA_cons_tl with (y := (k, D_invalidated)) in Hfind_list.
          1,2: apply H2, CEP.elements_2, CEP.find_1 in Hfind_list.
          1,2: rewrite Hfind_list //.
        - 1,2: destruct (PVM.find y conn_map) eqn: Hfind_map ;
                last by reflexivity.
          1,2: apply CEP.find_2, CEP.elements_1 in Hfind_map.
          1,2: apply H2, SetoidList.InA_cons in Hfind_map.
          1,2: destruct Hfind_map as [Hfind_map|Hfind_map] ;
                  first (by rewrite /CEP.Lemmas.O.eqke /PVM.SE.eq /fst Hyk in Hfind_map ;
                            destruct Hfind_map as [Hfind_map _] ; done).
          1,2: rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by exact H6.
          1,2: apply (SetoidList.findA_NoDupA Heqv_key0 ProdVarOrder.eq_dec y d H6) in Hfind_map.
          1,2: rewrite Hfind_map // in Hfind_list.
    - (* Expressions should not be very difficult... *)
      simpl Sem_frag_stmts.
      intro.
      destruct H4 as [vm' [ct' H4]].
      specialize (H0 k).
      assert (CEP.Lemmas.O.eqke (k, D_fexpr h) (k, D_fexpr h))
            by (split ; first (by rewrite /CEP.SE.eq //) ; last by reflexivity).
      apply (SetoidList.InA_cons_hd conn_map_list), H2, CEP.Lemmas.elements_mapsto_iff, CEP.find_1 in H7.
      rewrite H7 in H0 ; clear H7.
      destruct h.
      1-6: destruct H4 as [[H4 H7] H8].
      1-6: specialize (IHconn_map_list vm' ct' (CEP.Lemmas.P.of_list conn_map_list)
                                  H3 H6 (CEP.Lemmas.P.of_list_2 H6) H8).
      1-6: split ; first by apply (CEP.Lemmas.Equal_trans H4), IHconn_map_list.
      1-6: apply (CEP.Lemmas.Equal_trans (proj2 IHconn_map_list)).
      1-6: intro.
      1-6: unfold extend_map_with.
      1-6: rewrite CEP.Lemmas.map2_1bis // (*CEP.Lemmas.P.of_list_1b //. *)
              CEP.Lemmas.map2_1bis //.
      1-6: generalize (H k) ; intro.
      1-6: destruct (CEP.find k tmap) as [[[gt| |] ori]|] ; try by contradiction.
      1-6: rewrite /size_of_ftype /mkseq in H7 ; simpl in H7.
      1-6: rewrite N.add_0_r -surjective_pairing in H7.
      1-6: destruct (y == k) eqn: Hyk.
      + 1,3,5,7,9,11: move /eqP : Hyk => Hyk.
        1-6: rewrite Hyk.
        1-6: destruct (PVM.find k (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
        - 1,3,5,7,9,11: contradict H5.
          1-6: apply (SetoidList.InA_eqA (CEP.Lemmas.O.eqk_equiv def_expr) (x := (k, d))) ;
                first by rewrite /CEP.Lemmas.O.eqk /fst /CEP.SE.eq //.
          1-6: apply SetoidList.In_InA ; first by exact (CEP.Lemmas.O.eqk_equiv def_expr).
          1-6: rewrite CEP.Lemmas.P.of_list_1b // in Hfind_list.
          1-6: apply SetoidList.findA_NoDupA in Hfind_list ;
                last (by exact H6) ;
                last (by exact Heqv_key0).
          1-6: apply SetoidList.InA_alt in Hfind_list.
          1-6: destruct Hfind_list as [[k' d'] [[Hk Hd] Hfind_list]].
          1-6: move /eqP : Hk => Hk.
          1-6: simpl in Hk, Hd.
          1-6: subst k' d'.
          1-6: exact Hfind_list.
        - (* use H1 to show that PVM.find k conn_map = D_invalidated *)
          1-6: rewrite (CEP.Lemmas.elements_o conn_map k).
          1-6: generalize (SetoidList.findA_NoDupA (B := def_expr) Heqv_key0) ; intro.
          1-6: specialize H10 with (eqA_dec := HiFP.PVSLemmas.P.FM.eq_dec) (l := CEP.elements conn_map) (a := k) (1 := CEP.elements_3w conn_map).
          1: specialize (H10 (D_fexpr (Econst ProdVarOrder.T f b))).
          2: specialize (H10 (D_fexpr (Ecast u h))).
          3: specialize (H10 (D_fexpr (Eprim_unop e h))).
          4: specialize (H10 (D_fexpr (Eprim_binop e h1 h2))).
          5: specialize (H10 (D_fexpr (Emux h1 h2 h3))).
          6: specialize (H10 (D_fexpr (Evalidif h1 h2))).
          1-6: rewrite (proj1 H10) ;
                  last by (apply H2, SetoidList.InA_cons_hd ;
                           rewrite /CEP.Lemmas.O.eqke /PVM.SE.eq eq_refl ; split ; done).
          1-6: destruct ori ; try (by contradiction H7).
          1,2: by destruct f, gt ; try (by destruct H7 as [H7 _] ; done) ;
                  destruct H7 as [_ [H7 _]] ; specialize (H7 0) ; simpl in H7 ; apply H7.
          1,2: by destruct u, (type_of_expr h tmap) as [[[[| | | | | |]| |] _]|] ; try (by contradiction H7) ;
                  destruct gt ; try (by destruct H7 as [H7 _] ; done) ;
                  destruct H7 as [_ [H7 _]] ; specialize (H7 0) ; simpl in H7 ; apply H7.
          1,2: destruct e, (type_of_expr h tmap) as [[[[| | | | | |]| |] _]|] ; try done ;
               destruct gt ; try (by destruct H7 as [H7 _] ; done) ;
               try (destruct (n0 <= n < n1)) ;
               try (destruct (n <= n0)) ; try (by contradiction H7) ;
               by destruct H7 as [_ [H7 _]] ; specialize (H7 0) ; simpl in H7 ; apply H7.
          1,2: by destruct e, (type_of_expr h1 tmap) as [[[[| | | | | |]| |] _]|],
                              (type_of_expr h2 tmap) as [[[[| | | | | |]| |] _]|] ; try done ;
                  destruct gt ; try (by destruct H7 as [H7 _] ; done) ;
                  destruct H7 as [_ [H7 _]] ; specialize (H7 0) ; simpl in H7 ; apply H7.
          1,2: simpl in H0 ; move /andP : H0 => [_ H0] ;
               generalize (expr_preserves_fully_inferred tmap H h3 H0) ; intro.
          1,2: by destruct (type_of_expr h1 tmap) as [[[[[|[|]]| | | | | |]| |] _]|],
                           (type_of_expr h2 tmap) as [[[[| | | | | |]| |] p2]|],
                           (type_of_expr h3 tmap) as [[[[| | | | | |]| |] p3]|] ; try done ;
                  simpl in H7 ;
                  destruct gt ; try (by destruct H7 as [H7 _] ; done) ;
                  destruct H7 as [_ [H7 _]] ; specialize (H7 0) ; simpl in H7 ; apply H7.
          1,2: simpl in H0 ; move /andP : H0 => [_ H0] ;
               generalize (expr_preserves_fully_inferred tmap H h2 H0) ; intro.
          1,2: by destruct (type_of_expr h1 tmap) as [[[[[|[|]]| | | | | |]| |] _]|],
                           (type_of_expr h2 tmap) as [[[[| | | | | |]| |] _]|] ; try done ;
                  simpl in H7 ;
                  destruct gt ; try (by destruct H7 as [H7 _] ; done) ;
                  destruct H7 as [_ [H7 _]] ; specialize (H7 0) ; simpl in H7 ; apply H7.
      + 1-6: simpl in H0.
        1-6: destruct ori ; try (by contradiction H7).
        11,12: move /andP : H0 => [_ H0] ;
           generalize (expr_preserves_fully_inferred tmap H h2 H0) ; intro ;
           destruct (type_of_expr h1 tmap) as [[[[[|[|]]| | | | | |]| |] _]|],
                    (type_of_expr h2 tmap) as [[[[| | | | | |]| |] _]|] ; try done ;
           destruct gt ; try (by destruct H7 as [H7 _] ; done).
        9,10: move /andP : H0 => [_ H0] ;
           generalize (expr_preserves_fully_inferred tmap H h3 H0) ; intro ;
           destruct (type_of_expr h1 tmap) as [[[[[|[|]]| | | | | |]| |] _]|],
                    (type_of_expr h2 tmap) as [[[[| | | | | |]| |] p2]|],
                    (type_of_expr h3 tmap) as [[[[| | | | | |]| |] p3]|] ; try done ;
           simpl in H7 ; destruct gt ; try (by destruct H7 as [H7 _] ; done).
        7,8: destruct e, (type_of_expr h1 tmap) as [[[[| | | | | |]| |] _]|],
                         (type_of_expr h2 tmap) as [[[[| | | | | |]| |] _]|] ; try done ;
                destruct gt ; try (by destruct H7 as [H7 _] ; done).
        5,6: destruct e, (type_of_expr h tmap) as [[[[| | | | | |]| |] _]|] ; try done ;
           destruct gt ; try (by destruct H7 as [H7 _] ; done) ;
           try (destruct (n0 <= n < n1)) ;
           try (destruct (n <= n0)) ; try (by contradiction H7).
        3,4: destruct u, (type_of_expr h tmap) as [[[[| | | | | |]| |] _]|] ; try (by contradiction H7) ;
           destruct gt ; try (by destruct H7 as [H7 _] ; done).
        1,2: destruct f, gt ; try (by destruct H7 as [H7 _] ; done).
           1-364: destruct H7 as [_ [_ H7]].
           1-364: specialize (H7 y).
           1-364: rewrite mem_seq1 Hyk in H7.
           1-364: rewrite -H7.
           1-364: destruct (PVM.find y (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list ;
                 try (by specialize (H2 (y, d)) ;
                         rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last (by apply H6) ;
                         apply SetoidList.findA_NoDupA in Hfind_list ;
                               last (by apply H6) ; last (by apply Heqv_key0) ;
                         destruct H2 as [H2 _] ;
                         apply CEP.elements_2 in H2 ;
                               last (by apply SetoidList.InA_cons_tl, Hfind_list) ;
                         rewrite (CEP.find_1 H2) //).
           1-364: destruct (PVM.find y conn_map) eqn: Hfind_map ;
                 try (by reflexivity).
           1-364: apply CEP.find_2, CEP.elements_1 in Hfind_map.
           1-364: apply H2, SetoidList.InA_cons in Hfind_map.
           1-364: destruct Hfind_map as [Hfind_map|Hfind_map] ;
                  first (by rewrite /CEP.Lemmas.O.eqke /PVM.SE.eq /fst Hyk in Hfind_map ;
                          destruct Hfind_map as [Hfind_map _] ; done).
           1-364: rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; try (by exact H6).
           1-364: apply (SetoidList.findA_NoDupA Heqv_key0 ProdVarOrder.eq_dec y d H6) in Hfind_map.
           1-364: by rewrite Hfind_map // in Hfind_list.
      (* what remains is a link with a reference, which is translated to a different Sfcnct case. *)
      destruct H4 as [[H4 H7] H8].
      specialize (IHconn_map_list vm' ct' (CEP.Lemmas.P.of_list conn_map_list)
                                  H3 H6 (CEP.Lemmas.P.of_list_2 H6) H8).
      split ; first by apply (CEP.Lemmas.Equal_trans H4), IHconn_map_list.
      apply (CEP.Lemmas.Equal_trans (proj2 IHconn_map_list)).
      intro.
      unfold extend_map_with.
      rewrite CEP.Lemmas.map2_1bis // (*CEP.Lemmas.P.of_list_1b //. *)
              CEP.Lemmas.map2_1bis //.
      generalize (H k) ; intro.
      destruct (CEP.find k tmap) as [[[gt| |] [| | | |]]|] ; try by contradiction.
      1,2: unfold mkseq in H7 ; simpl map in H7 ; simpl foldr in H7.
      1,2: rewrite N.add_0_r -surjective_pairing in H7.
      1,2: generalize (list_lhs_ref_p_type tmap h) ; intro.
      1,2: destruct (list_lhs_ref_p h tmap) as [[[|ic [|]] [[gt_src| |] [| | | |]]]|] ; try (by contradiction H7) ;
            destruct H7 as [_ H7] ; simpl in H7 ; try (by destruct H7 as [H7 _] ; done).
      1-4: destruct (y == k) eqn: Hyk.
      + 1,3,5,7: move /eqP : Hyk => Hyk ; rewrite Hyk.
        1-4: destruct (PVM.find k (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
        - 1,3,5,7: contradict H5.
          1-4: apply (SetoidList.InA_eqA (CEP.Lemmas.O.eqk_equiv def_expr) (x := (k, d))) ;
                first by rewrite /CEP.Lemmas.O.eqk /fst /CEP.SE.eq //.
          1-4: apply SetoidList.In_InA ; first by exact (CEP.Lemmas.O.eqk_equiv def_expr).
          1-4: rewrite CEP.Lemmas.P.of_list_1b // in Hfind_list.
          1-4: apply SetoidList.findA_NoDupA in Hfind_list ;
                last (by exact H6) ;
                last (by exact Heqv_key0).
          1-4: apply SetoidList.InA_alt in Hfind_list.
          1-4: destruct Hfind_list as [[k' d'] [[Hk Hd] Hfind_list]].
          1-4: move /eqP : Hk => Hk.
          1-4: simpl in Hk, Hd.
          1-4: subst k' d'.
          1-4: exact Hfind_list.
        - (* use H2 to show that PVM.find k conn_map = D_invalidated *)
          1-4: rewrite (CEP.Lemmas.elements_o conn_map k).
          1-4: generalize (SetoidList.findA_NoDupA (B := def_expr) Heqv_key0) ; intro.
          1-4: specialize H11 with (eqA_dec := HiFP.PVSLemmas.P.FM.eq_dec) (l := CEP.elements conn_map) (a := k) (b := D_fexpr (Eref h)) (1 := CEP.elements_3w conn_map).
          1-4: rewrite (proj1 H11).
          * 1,3,5,7: destruct H7 as [H7 _] ; move /andP : H7 => [/andP [_ /eqP H7] _].
            1-4: by apply H7.
          * 1-4: apply H2, SetoidList.InA_cons_hd.
            1-4: rewrite /CEP.Lemmas.O.eqke /PVM.SE.eq eq_refl ; split ; by done.
      + 1-4: destruct (y == ic) eqn: Hyic.
        - 1,3,5,7: move /eqP : Hyic => Hyic ; subst y.
          1-4: move : H7 => [/andP [_ H7] _] ; rewrite (eq_sym k) Hyk orFb in H7.
          1-4: move /eqP : H7 => H7 ; rewrite H7.
          1-4: destruct (PVM.find ic (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
          * 1,3,5,7: specialize (H2 (ic, d)).
            1-4: rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by apply H6.
            1-4: apply SetoidList.findA_NoDupA in Hfind_list ;
                  last (by apply H6) ; last by apply Heqv_key0.
            1-4: apply SetoidList.InA_cons_tl with (y := (k, D_fexpr (Eref h))) in Hfind_list.
            1-4: apply H2, CEP.elements_2, CEP.find_1 in Hfind_list.
            1-4: by rewrite Hfind_list //.
          * 1-4: destruct (PVM.find ic conn_map) eqn: Hfind_map ;
                  last by reflexivity.
            1-4: apply CEP.find_2, CEP.elements_1 in Hfind_map.
            1-4: apply H2, SetoidList.InA_cons in Hfind_map.
            1-4: destruct Hfind_map as [Hfind_map|Hfind_map] ;
                    first (by rewrite /CEP.Lemmas.O.eqke /PVM.SE.eq /fst Hyk in Hfind_map ;
                              destruct Hfind_map as [Hfind_map _] ; done).
            1-4: rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by exact H6.
            1-4: apply (SetoidList.findA_NoDupA Heqv_key0 ProdVarOrder.eq_dec ic d H6) in Hfind_map.
            1-4: by rewrite Hfind_map // in Hfind_list.
        - 1-4: destruct H7 as [_ H7].
          1-4: specialize (H7 y).
          1-4: rewrite mem_seq1 Hyk orFb mem_seq1 Hyic in H7.
          1-4: rewrite -H7.
          1-4: destruct (PVM.find y (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
          * 1,3,5,7: specialize (H2 (y, d)).
            1-4: rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by apply H6.
            1-4: apply SetoidList.findA_NoDupA in Hfind_list ;
                  last (by apply H6) ; last by apply Heqv_key0.
            1-4: apply SetoidList.InA_cons_tl with (y := (k, D_fexpr (Eref h))) in Hfind_list.
            1-4: apply H2, CEP.elements_2, CEP.find_1 in Hfind_list.
            1-4: by rewrite Hfind_list //.
          * 1-4: destruct (PVM.find y conn_map) eqn: Hfind_map ;
                  last by reflexivity.
            1-4: apply CEP.find_2, CEP.elements_1 in Hfind_map.
            1-4: apply H2, SetoidList.InA_cons in Hfind_map.
            1-4: destruct Hfind_map as [Hfind_map|Hfind_map] ;
                    first (by rewrite /CEP.Lemmas.O.eqke /PVM.SE.eq /fst Hyk in Hfind_map ;
                              destruct Hfind_map as [Hfind_map _] ; done).
            1-4: rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by exact H6.
            1-4: apply (SetoidList.findA_NoDupA Heqv_key0 ProdVarOrder.eq_dec y d H6) in Hfind_map.
            1-4: by rewrite Hfind_map // in Hfind_list.
Qed.

Lemma ExpandBranches_funs_preserves_fully_inferred :
forall (ss old_comp_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t vertex_type),
        stmts_have_fully_inferred_ground_types ss
    ->
        ct_has_fully_inferred_ground_types old_conn_map
    ->
        match ExpandBranches_funs ss old_comp_ss old_conn_map old_scope with
        | Some (comp_ss, conn_map, scope) =>
            ct_has_fully_inferred_ground_types conn_map
        | None => True
        end
with ExpandBranch_fun_preserves_fully_inferred :
forall (s : HiFP.hfstmt) (old_comp_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t vertex_type),
        stmt_has_fully_inferred_ground_types s
    ->
        ct_has_fully_inferred_ground_types old_conn_map
    ->
        match ExpandBranch_fun s old_comp_ss old_conn_map old_scope with
        | Some (comp_ss, conn_map, scope) =>
            ct_has_fully_inferred_ground_types conn_map
        | None => True
        end.
Proof.
* clear ExpandBranches_funs_preserves_fully_inferred.
  induction ss ; simpl.
  + done.
  + intros.
    move /andP : H => H.
    specialize (ExpandBranch_fun_preserves_fully_inferred h old_comp_ss old_conn_map old_scope
                (proj1 H) H0).
    destruct (ExpandBranch_fun h old_comp_ss old_conn_map old_scope) as [[[temp_comp_ss temp_conn_map] temp_scope]|];
          last by trivial.
    specialize (IHss temp_comp_ss temp_conn_map temp_scope
                (proj2 H) ExpandBranch_fun_preserves_fully_inferred).
    destruct (ExpandBranches_funs ss temp_comp_ss temp_conn_map temp_scope) as [[[_ conn_map] _]|] ;
          last by trivial.
    exact IHss.
* clear ExpandBranch_fun_preserves_fully_inferred.
  induction s ; simpl ; try done.
  + (* Swire *)
    intros.
    destruct f as [| |] ; by done.
  + (* Sreg *)
    intros.
    destruct (type h) as [| |] ; try by done.
    destruct (rhs_type_of_expr (clock h) old_scope) ; last by done.
    destruct (reset h) ; first by done.
    destruct (rhs_type_of_expr h0 old_scope) as [[[[|[|]]| | | | | |] _]|] ; try by done.
    1,2: destruct (rhs_type_of_expr h1 old_scope) ; by done.
  + (* Snode *)
    intros.
    destruct (rhs_type_of_expr h old_scope) as [[]|]; by done.
  + (* Sfcnct *)
    intros.
    destruct h as [var| | |] ; try by done.
    destruct (CEP.find var old_scope) as [[[]|[]|[]|[]|[]]|] ; try (by done) ;
    destruct (rhs_type_of_expr h0 old_scope) as [[[] _]|] ; try (by done) ;
    try (destruct (n0 <= n) ; last (by done)) ;
    intro ;
    destruct (k == var) eqn: Hkvar ;
    try (by rewrite (CEP.Lemmas.find_add_eq Hkvar) //) ;
    by rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))) //.
  + (* Sinvalid *)
    intros.
    destruct h as [var| | |] ; try by done.
    destruct (CEP.find var old_scope) as [[[]|[]|[]|[]|[]]|] ; try (by done) ;
    intro ;
    destruct (k == var) eqn: Hkvar ;
    try (by rewrite (CEP.Lemmas.find_add_eq Hkvar) //) ;
    by rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))) //.
  + (* Swhen *)
    rename h into cond ; rename h0 into ss_true ; rename h1 into ss_false.
    intros.
    destruct (rhs_type_of_expr cond old_scope) as [[[[|[|]]| | | | | |] _]|] ; try by done.
    move /andP : H => [/andP [Hcond Ht] Hf].
    generalize (ExpandBranches_funs_preserves_fully_inferred ss_true old_comp_ss old_conn_map old_scope
                Ht H0) ; intro.
    destruct (ExpandBranches_funs ss_true old_comp_ss old_conn_map old_scope) as [[[true_comp_ss true_conn_map] _]|] ; last by done.
    specialize (ExpandBranches_funs_preserves_fully_inferred ss_false true_comp_ss old_conn_map old_scope
                Hf H0).
    destruct (ExpandBranches_funs ss_false true_comp_ss old_conn_map old_scope) as [[[false_comp_ss false_conn_map] _]|] ; last by done.
    intro.
    specialize (H k) ; specialize (ExpandBranches_funs_preserves_fully_inferred k).
    rewrite /combine_when_connections CEP.Lemmas.map2_1bis //.
    destruct (CEP.find k true_conn_map) as [[]|], (CEP.find k false_conn_map) as [[]|] ; try by done.
    destruct (h == h0) ; first by exact H.
    simpl.
    rewrite Hcond H ExpandBranches_funs_preserves_fully_inferred //.
Qed.

Lemma stmts_tmap_submap_vm :
forall (vm_small vm_large : CEP.t vertex_type) (ss : HiFP.hfstmt_seq) (tmap scope : CEP.t (ftype * HiF.forient)),
      CEP.submap scope tmap ->
      CEP.submap vm_small vm_large ->
      subdomain scope vm_small ->
      stmts_tmap (tmap, scope) ss vm_small = stmts_tmap (tmap, scope) ss vm_large
with stmt_tmap_submap_vm :
forall (vm_small vm_large : CEP.t vertex_type) (s : HiFP.hfstmt) (tmap scope : CEP.t (ftype * HiF.forient)),
      CEP.submap scope tmap ->
      CEP.submap vm_small vm_large ->
      subdomain scope vm_small ->
      stmt_tmap (tmap, scope) s vm_small = stmt_tmap (tmap, scope) s vm_large.
Proof.
Admitted.

Lemma ExpandBranch_components :
   forall (ss def_ss : HiFP.hfstmt_seq) (conn_map : CEP.t def_expr) (scope : CEP.t vertex_type)
          (def_ss' : HiFP.hfstmt_seq) (conn_map' : CEP.t def_expr) (scope' : CEP.t vertex_type),
      ExpandBranches_funs ss def_ss conn_map scope =
          Some (def_ss', conn_map', scope') ->
              def_ss' = Qcat def_ss (component_stmts_of ss)
          /\
              ((forall k : CEP.key, CEP.find k conn_map  <> Some D_undefined) ->
               (forall k : CEP.key, CEP.find k conn_map' <> Some D_undefined))
with ExpandBranch_component :
   forall (def_ss' : HiFP.hfstmt_seq) (conn_map' : CEP.t def_expr) (scope : CEP.t vertex_type)
          (s : HiFP.hfstmt) (def_ss : HiFP.hfstmt_seq) (conn_map : CEP.t def_expr) (scope' : CEP.t vertex_type),
      ExpandBranch_fun s def_ss conn_map scope =
          Some (def_ss', conn_map', scope') ->
              def_ss' = Qcat def_ss (component_stmt_of s)
          /\
              ((forall k : CEP.key, CEP.find k conn_map  <> Some D_undefined) ->
               (forall k : CEP.key, CEP.find k conn_map' <> Some D_undefined)).
Proof.
* clear ExpandBranch_components.
  induction ss ; intros ; simpl ExpandBranches_funs in H ; simpl component_stmts_of.
  + injection H ; clear H ; intros ; subst def_ss' conn_map' scope'.
    split ; first by rewrite Qcats0 //.
    done.
  + specialize ExpandBranch_component with (s := h) (def_ss := def_ss) (conn_map := conn_map) (scope := scope).
    destruct (ExpandBranch_fun h def_ss conn_map scope) as [[[def_ss0 conn_map0] scope0]|] ; last by discriminate H.
    specialize ExpandBranch_component with (1 := Logic.eq_refl).
    apply IHss in H.
    split.
    - rewrite (proj1 ExpandBranch_component) Qcat_assoc in H.
      by apply H.
    - intro.
      by apply H, ExpandBranch_component, H0.
* clear ExpandBranch_component.
  destruct s.
  + (* Sskip *)
    unfold ExpandBranch_fun, component_stmt_of.
    intros.
    injection H ; clear H ; intros ; subst def_ss' conn_map' scope'.
    split; first by rewrite Qcats0 //.
    done.
  + (* Swire *)
    unfold ExpandBranch_fun, component_stmt_of.
    intros.
    destruct f as [gt| |] ; try by discriminate H.
    injection H ; clear H ; intros ; subst def_ss' conn_map' scope'.
    split ; first by rewrite -Qcat_rcons Qcats0 //.
    done.
  + (* Sreg *)
    unfold ExpandBranch_fun, component_stmt_of.
    intros.
    destruct (type h) as [gt| |] ; try by discriminate H.
    destruct (rhs_type_of_expr (clock h) scope) as [|] ; last by discriminate H.
    destruct (reset h).
    2: destruct (rhs_type_of_expr h0 scope) as [[[[|[|]]| | | | | |] _]|] ; try by discriminate H.
    2,3: destruct (rhs_type_of_expr h1 scope) ; last by discriminate H.
    1-3: injection H ; clear H ; intros ; subst def_ss' conn_map' scope'.
    1-3: split ; first by rewrite -Qcat_rcons Qcats0 //.
    1-3: done.
  + (* Smem *)
    unfold ExpandBranch_fun.
    discriminate.
  + (* Sinst *)
    unfold ExpandBranch_fun.
    discriminate.
  + (* Snode *)
    unfold ExpandBranch_fun, component_stmt_of.
    intros.
    destruct (rhs_type_of_expr h scope) as [[gt_expr _]|] ; last by discriminate H.
    injection H ; clear H ; intros ; subst def_ss' conn_map' scope'.
    split ; first by rewrite -Qcat_rcons Qcats0 //.
    done.
  + (* Sfcnct *)
    unfold ExpandBranch_fun, component_stmt_of.
    intros.
    destruct h ; try by discriminate H.
    destruct (lhs_type_of_ref (Eid (var:=ProdVarOrder.T) s) scope) as [gt_tgt|] ; last by discriminate H.
    destruct (rhs_type_of_expr h0 scope) as [[gt_src _]|] ; last by discriminate H.
    destruct (connect_type_compatible false (Gtyp gt_tgt) (Gtyp gt_src) false) ;
          last by discriminate H.
    injection H ; clear H ; intros ; subst def_ss' conn_map' scope'.
    split ; first by rewrite Qcats0 //.
    intro ; intro ; specialize (H k).
    destruct (k == s) eqn: Hks.
    - by rewrite (CEP.Lemmas.find_add_eq Hks) //.
    - by rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hks))) //.
  + (* Sinvalid *)
    unfold ExpandBranch_fun, component_stmt_of.
    intros.
    destruct h ; try by discriminate H.
    destruct (lhs_type_of_ref (Eid (var:=ProdVarOrder.T) s) scope) as [gt_tgt|] ; last by discriminate H.
    injection H ; clear H ; intros ; subst def_ss' conn_map' scope'.
    split ; first by rewrite Qcats0 //.
    intro ; intro ; specialize (H k).
    destruct (k == s) eqn: Hks.
    - by rewrite (CEP.Lemmas.find_add_eq Hks) //.
    - by rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hks))) //.
  + (* Swhen *)
    simpl ExpandBranch_fun ; simpl component_stmt_of.
    rename h into cond ; rename h0 into ss_true ; rename h1 into ss_false.
    intros.
    generalize (ExpandBranch_components ss_true def_ss conn_map scope) ;
          intro.
    destruct (rhs_type_of_expr cond scope) as [[[[|[|]]| | | | | |] _]|] ; try by discriminate H.
    destruct (ExpandBranches_funs ss_true def_ss conn_map scope) as [[[true_comp_ss true_conn_map] true_scope]|] ; last by discriminate H.
    specialize (H0 _ _ _ Logic.eq_refl).
    generalize (ExpandBranch_components ss_false true_comp_ss conn_map scope) ;
          intro.
    destruct (ExpandBranches_funs ss_false true_comp_ss conn_map scope) as [[[false_comp_ss false_conn_map] false_scope]|] ; last by discriminate H.
    specialize (H1 _ _ _ Logic.eq_refl).
    injection H ; clear H ; intros ; subst def_ss' conn_map' scope'.
    split ; first by rewrite -Qcat_assoc -(proj1 H0) -(proj1 H1) //.
    destruct H0 as [_ H0] ; destruct H1 as [_ H1].
    intro ; intro ; specialize (H0 H k) ; specialize (H1 H k).
    rewrite /combine_when_connections CEP.Lemmas.map2_1bis //.
    destruct (CEP.find k  true_conn_map) as [[]|] ; try (by contradiction H0) ;
    destruct (CEP.find k false_conn_map) as [[]|] ; try (by contradiction H1) ;
    try discriminate.
    destruct (h == h0) ; discriminate.
Qed.

Definition map_can_connect
    (tmap : CEP.t (ftype * HiF.forient))
    (conn_map : CEP.t def_expr)
:   Prop
:=  forall k : CEP.key,
        match CEP.find k conn_map with
        | Some D_undefined => false
        | Some (D_fexpr e) =>
            match CEP.find k tmap, type_of_expr e tmap with
            | Some (Gtyp gt_tgt, HiF.Sink)  , Some (exist (Gtyp gt_src) _)
            | Some (Gtyp gt_tgt, HiF.Duplex), Some (exist (Gtyp gt_src) _) =>
                connect_type_compatible false (Gtyp gt_tgt) (Gtyp gt_src) false
            | _, _ => false
            end
        | Some D_invalidated =>
            match CEP.find k tmap with
            | Some (Gtyp gt_tgt, HiF.Sink)
            | Some (Gtyp gt_tgt, HiF.Duplex) => true
            | _ => false
            end
        | _ => true
        end.

Fixpoint stmts_can_connect
    (tmap : CEP.t (ftype * HiF.forient))
    (conn_stmts : HiFP.hfstmt_seq)
:   bool
:=  match conn_stmts with
    | Qnil => true
    | Qcons (Sfcnct (Eid k) e) ss' =>
        match CEP.find k tmap, type_of_expr e tmap with
        | Some (Gtyp gt_tgt, HiF.Sink)  , Some (exist (Gtyp gt_src) _)
        | Some (Gtyp gt_tgt, HiF.Duplex), Some (exist (Gtyp gt_src) _) =>
                connect_type_compatible false (Gtyp gt_tgt) (Gtyp gt_src) false
            &&
                stmts_can_connect tmap ss'
        | _, _ => false
        end
    | Qcons (Sinvalid (Eid k)) ss' =>
        match CEP.find k tmap with
        | Some (Gtyp gt_tgt, HiF.Sink)
        | Some (Gtyp gt_tgt, HiF.Duplex) => stmts_can_connect tmap ss'
        | _ => false
        end
    | _ => false
    end.

Lemma convert_to_connect_stmts_preserves_can_connect :
    forall (tmap : CEP.t (ftype * HiF.forient)) (conn_map : CEP.t def_expr),
            map_can_connect tmap conn_map
        ->
            stmts_can_connect tmap (convert_to_connect_stmts conn_map).
Proof.
intros.
rewrite /convert_to_connect_stmts CEP.fold_1.
assert (SetoidList.inclA (@CEP.Lemmas.O.eqke def_expr) (CEP.elements conn_map) (CEP.elements conn_map)) by done.
revert H0.
assert (stmts_can_connect tmap (Qnil ProdVarOrder.T)) by rewrite /stmts_can_connect //.
revert H0.
generalize (Qnil ProdVarOrder.T) as old_conn_map_list.
generalize (CEP.elements conn_map) at 1 3 as conn_map_list.
induction conn_map_list.
* intros ; simpl ; done.
* intros ; simpl.
  apply IHconn_map_list.
  + rewrite /convert_to_connect_stmt.
    specialize (H1 a (SetoidList.InA_cons_hd conn_map_list (conj (eqxx a.1) (erefl a.2)))).
    destruct a as [k el] ; simpl.
    apply CEP.elements_2, CEP.find_1 in H1.
    specialize (H k).
    rewrite H1 in H.
    destruct el ; try done ; simpl.
    - destruct (CEP.find k tmap) as [[[| |] [| | | |]]|] ; done.
    - destruct (CEP.find k tmap) as [[[gt_tgt| |] [| | | |]]|] ; try done ;
      destruct (type_of_expr h tmap) as [[[gt_src| |] _]|] ; try done ;
      simpl in H ; rewrite H andTb //.
  + intro ; specialize (H1 x).
    intro ; apply H1, SetoidList.InA_cons_tl, H2.
Qed.

Lemma Sem_frag_stmts_connect :
forall (vm : CEP.t vertex_type) (ct_old conn_map : CEP.t def_expr)
       (tmap : CEP.t (ftype * HiF.forient)),
        map_can_connect tmap conn_map
    ->
        tmap_has_fully_inferred_ground_types tmap
    ->
        vm_and_tmap_compatible vm tmap
    ->
        subdomain conn_map ct_old
    ->
        Sem_frag_stmts vm ct_old (convert_to_connect_stmts conn_map) vm (extend_map_with conn_map ct_old) tmap.
Proof.
(*
  assert (Heqv_key_elt : RelationClasses.Equivalence (CEP.eq_key_elt (elt:=def_expr))).
        clear.
        assert (forall x : CEP.key * def_expr, CEP.eq_key_elt x x)
              by (destruct x ; split ; first (by rewrite /CEP.SE.eq eq_refl //) ; last (by reflexivity)).
        assert (forall x y : CEP.key * def_expr, CEP.eq_key_elt x y -> CEP.eq_key_elt y x)
              by (destruct x, y ; split ; first (by rewrite /CEP.SE.eq eq_sym (proj1 H0) //) ; last (by symmetry ; apply H0)).
        assert (forall x y z : CEP.key * def_expr, CEP.eq_key_elt x y -> CEP.eq_key_elt y z -> CEP.eq_key_elt x z)
              by (destruct x, y, z ; split ; first (by rewrite (proj1 H1) (proj1 H2) /CEP.SE.eq //) ;
                  last (by apply (eq_trans (proj2 H1) (proj2 H2)))).
        exact (RelationClasses.Build_Equivalence (CEP.eq_key_elt (elt:=def_expr)) H H0 H1).
  assert (Heqv_key : RelationClasses.Equivalence (CEP.eq_key (elt:=def_expr))).
        clear.
        assert (forall x : CEP.key * def_expr, CEP.eq_key x x)
              by (intro ; rewrite /CEP.eq_key /CEP.SE.eq eq_refl //).
        assert (forall x y : CEP.key * def_expr, CEP.eq_key x y -> CEP.eq_key y x)
              by (intros ; rewrite /CEP.eq_key /CEP.SE.eq eq_sym H0 //).
        assert (forall x y z : CEP.key * def_expr, CEP.eq_key x y -> CEP.eq_key y z -> CEP.eq_key x z)
              by (intros ; rewrite H1 H2 /CEP.eq_key /CEP.SE.eq //).
        exact (RelationClasses.Build_Equivalence (CEP.eq_key (elt:=def_expr)) H H0 H1). *)
intros.
unfold convert_to_connect_stmts.
rewrite (CEP.Lemmas.P.fold_spec_right).
assert (forall (x : PVM.key) (e : def_expr),
       PVM.MapsTo x e conn_map <->
       SetoidList.InA (@CEP.Lemmas.O.eqke def_expr) (x, e) (List.rev (PVM.elements conn_map))).
      intros ; split ; intro.
      * apply SetoidList.InA_rev, CEP.elements_1, H3.
      * apply CEP.elements_2, SetoidList.InA_rev, H3.
revert H3.
generalize (SetoidList.NoDupA_rev (CEP.Lemmas.O.eqk_equiv def_expr) (CEP.elements_3w conn_map)).
(*assert (stmts_can_connect tmap (Qnil ProdVarOrder.T)) by rewrite /stmts_can_connect //.
revert H3.
generalize (Qnil ProdVarOrder.T) as old_conn_stmts.*)
replace (@List.rev (prod PVM.SE.t def_expr)
            (@CEP.elements def_expr conn_map)) with (@List.rev (prod PVM.key def_expr)
            (@CEP.elements def_expr conn_map)) by reflexivity.
generalize (List.rev (CEP.elements conn_map)) as conn_map_list ; intro.
revert conn_map ct_old H H2.
induction conn_map_list.
* simpl ; intros.
  split ; first by apply CEP.Lemmas.F.Equal_refl.
  (* use H4 to show that conn_map is empty.
     Additionally need to do something about old_conn_stmts *)
  intro ; specialize (H4 y).
  rewrite /extend_map_with CEP.Lemmas.map2_1bis //.
  generalize (CEP.find_2 (m := conn_map) (x := y)) ; intro.
  destruct (CEP.find y conn_map) as [e|] ; last by reflexivity.
  specialize (H5 _ Logic.eq_refl).
  apply H4 in H5.
  by inversion H5.
* simpl ; intros.
  destruct a as [k el].
  generalize (H k) ; intro.
  specialize (proj2 (H4 k el) (SetoidList.InA_cons_hd conn_map_list (conj (eqxx (k, el).1) (erefl (k, el).2)))) ;
        intro.
  apply CEP.find_1 in H6.
  rewrite H6 in H5.
  assert (CEP.Equal (extend_map_with (CEP.remove k conn_map) (CEP.add k el ct_old)) (extend_map_with conn_map ct_old)).
        intro.
        rewrite /extend_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis //.
        destruct (y == k) eqn: Hyk.
        - rewrite (CEP.Lemmas.remove_eq_o conn_map) ; last by rewrite /PVM.SE.eq eq_sym Hyk.
          by rewrite (CEP.Lemmas.find_add_eq Hyk) (elimT eqP Hyk) H6 //.
        - rewrite (CEP.Lemmas.remove_neq_o conn_map) ; last by rewrite /PVM.SE.eq eq_sym ; apply (elimT negP (negbT Hyk)).
          by rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hyk))) //.
  rewrite {1}/CEP.Lemmas.P.uncurry /fst /snd {1}/convert_to_connect_stmt.
  destruct el ; try by done.
  + (* Sinvalid *)
    simpl Sem_frag_stmts.
    exists vm, (CEP.add k D_invalidated ct_old).
    split.
    - split ; first by apply CEP.Lemmas.F.Equal_refl.
      destruct (CEP.find k tmap) as [[[gt| |] [| | | |]]|] ; try (by discriminate H5) ;
            rewrite /size_of_ftype /mkseq ; simpl map ; rewrite N.add_0_r -surjective_pairing.
      1,2: split ;
            last by (intro ; rewrite mem_seq1 ;
                     destruct (v0 == k) eqn: Hvk ; first (by trivial) ;
                     rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hvk))) //).
      1,2: intro ; destruct n ; simpl ;
            last by (assert ((@List.length CEP.key [::] <= n)%coq_nat) by apply Nat.le_0_l ;
                     apply List.nth_error_None in H8 ;
                     rewrite H8 //).
      1,2: split ;
            last by rewrite (CEP.Lemmas.find_add_eq (eq_refl k)) //.
      1,2: specialize (H2 k) ; rewrite H6 in H2.
      1,2: by destruct (CEP.find k ct_old) ; done.
    - apply (Sem_frag_stmts_Equal _ vm _ (CEP.add k D_invalidated ct_old) _
                                    vm _ (extend_map_with (CEP.remove k conn_map) (CEP.add k D_invalidated ct_old)) _ tmap) ;
            try (by apply CEP.Lemmas.Equal_refl) ;
            first (by apply H7).
      apply IHconn_map_list.
      * intro ; specialize (H k0).
        destruct (k == k0) eqn: Hkk0.
        + by rewrite CEP.Lemmas.remove_eq_o //.
        + rewrite CEP.Lemmas.remove_neq_o // /PVM.SE.eq.
          apply (elimT negP (negbT Hkk0)).
      * trivial.
      * intro ; specialize (H2 k0).
        destruct (k0 == k) eqn: Hkk0.
        + by rewrite CEP.Lemmas.find_add_eq //.
        + move /negP : Hkk0 => Hkk0.
          rewrite (CEP.Lemmas.find_add_neq Hkk0).
          rewrite eq_sym in Hkk0.
          by rewrite (CEP.Lemmas.remove_neq_o _ Hkk0) //.
      * inversion H3 ; by assumption.
      * intros ; specialize (H4 x e).
        split ; intro.
        + apply CEP.Lemmas.remove_mapsto_iff in H8.
          rewrite /PVM.SE.eq eq_sym in H8.
          destruct H4 as [H4 _].
          specialize (H4 (proj2 H8)).
          inversion H4 ; subst l y ; last by assumption.
          rewrite /CEP.Lemmas.O.eqke /PVM.SE.eq /fst in H10.
          destruct H8 as [H8 _].
          rewrite (proj1 H10) // in H8.
        + destruct (k == x) eqn: Hkx.
          - move /eqP : Hkx => Hkx ; subst x.
            inversion H3 ; subst x l.
            contradict H11.
            apply CEP.Lemmas.O.InA_eqke_eqk, (SetoidList.InA_eqA (@CEP.Lemmas.O.eqk_equiv def_expr)) with (y := (k, D_invalidated)) in H8 ;
                  try by exact H8.
            rewrite /CEP.Lemmas.O.eqk /PVM.SE.eq eq_refl //.
          - move /negP : Hkx => Hkx.
            by apply (CEP.remove_2 Hkx), H4, SetoidList.InA_cons_tl, H8.
  + (* Sfcnct *)
    simpl Sem_frag_stmts.
    exists vm, (CEP.add k (D_fexpr h) ct_old).
    split.
    - destruct h ; split ; try by apply CEP.Lemmas.F.Equal_refl.
      1-6: destruct (CEP.find k tmap) as [[[gt_tgt| |] [| | | |]]|] ; try (by discriminate H5) ;
                 rewrite /size_of_ftype /mkseq ; simpl map ; rewrite N.add_0_r -surjective_pairing.
      1-12: simpl foldr.
      1-2: destruct (type_of_expr (Econst ProdVarOrder.T f b) tmap) as [[[gt_src| |] _]|] ; try (by discriminate H5).
      3-4: destruct (type_of_expr (Ecast u h) tmap) as [[[gt_src| |] _]|] ; try (by discriminate H5).
      5-6: destruct (type_of_expr (Eprim_unop e h) tmap) as [[[gt_src| |] _]|] ; try (by discriminate H5).
      7-8: destruct (type_of_expr (Eprim_binop e h1 h2) tmap) as [[[gt_src| |] _]|] ; try (by discriminate H5).
      9-10: destruct (type_of_expr (Emux h1 h2 h3) tmap) as [[[gt_src| |] _]|] ; try (by discriminate H5).
      11-12: destruct (type_of_expr (Evalidif h1 h2) tmap) as [[[gt_src| |] _]|] ; try (by discriminate H5).
      1-12: split ; first by exact H5.
      1-12: simpl ; split ;
            last by (intro ; rewrite mem_seq1 ;
                     destruct (v0 == k) eqn: Hvk ; first (by trivial) ;
                     rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hvk))) //).
      1-12: intro ; destruct n ; simpl ;
            last by (assert ((@List.length CEP.key [::] <= n)%coq_nat) by apply Nat.le_0_l ;
                     apply List.nth_error_None in H8 ;
                     rewrite H8 //).
      1-12: split ;
            last by rewrite (CEP.Lemmas.find_add_eq (eq_refl k)) //.
      1-12: specialize (H2 k) ; rewrite H6 in H2.
      1-12: by destruct (CEP.find k ct_old) ; done.
      (* What remains is a reference *)
      destruct (CEP.find k tmap) as [[[gt_tgt| |] [| | | |]]|] ;
                 try (by discriminate H5) ;
                 rewrite /size_of_ftype /mkseq ; simpl map.
      1,2: rewrite N.add_0_r -surjective_pairing.
      1,2: simpl foldr ; simpl type_of_expr in H5.
      1,2: generalize (list_lhs_ref_p_type tmap h) ; intro.
      1,2: generalize (list_lhs_ref_p_size tmap h) ; intro.
      1-2: destruct (type_of_ref h tmap) as [[type_ft [| | | |]]|] ;
                try by discriminate H5.
      1-4: destruct (list_lhs_ref_p h tmap) as [[lst_src [ft_src ori_src]]|] eqn: Hlist ;
                last by contradiction H8.
      1-4: injection H8 ; clear H8 ; intros ; subst type_ft ori_src.
      1-4: destruct ft_src as [[| | | | | |]| |] ; 
          simpl in H5 ;
          try (by discriminate H5) ;
          try (by destruct (make_ftype_explicit ft_src) ;
                  discriminate H5) ;
          try (by destruct (make_ffield_explicit f) ;
                  discriminate H5).
      1-28: simpl ; split ;
             first by (exact H5).
      1-28: destruct lst_src as [|ic [|]] ; try by discriminate H9.
      1-28: split ;
             last by (intro v0 ; rewrite mem_seq1 mem_seq1 ;
                      destruct ((v0 == k) || (v0 == ic)) eqn: Hv0k ; first (by trivial) ;
                      apply negbT in Hv0k ;
                      rewrite negb_or in Hv0k ;
                      move /andP : Hv0k => [/negP Hv0k _] ;
                      rewrite (CEP.Lemmas.find_add_neq Hv0k) //).
      1-28: specialize (H2 k) ; destruct (CEP.find k ct_old) ;
                  last by rewrite H6 // in H2.
      1-28: rewrite (CEP.Lemmas.find_add_eq (eq_refl k)) eq_refl andbT.
      1-28: destruct (k == ic) eqn: Hkic ; first by done.
      1-28: rewrite eq_sym in Hkic ;
            rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkic))) eq_refl //.
    - apply (Sem_frag_stmts_Equal _ vm _ (CEP.add k (D_fexpr h) ct_old) _
                                    vm _ (extend_map_with (CEP.remove k conn_map) (CEP.add k (D_fexpr h) ct_old)) _ tmap) ;
            try (by apply CEP.Lemmas.Equal_refl) ;
            first (by apply H7).
      apply IHconn_map_list.
      * intro ; specialize (H k0).
        destruct (k == k0) eqn: Hkk0.
        + by rewrite CEP.Lemmas.remove_eq_o //.
        + rewrite CEP.Lemmas.remove_neq_o // /PVM.SE.eq.
          apply (elimT negP (negbT Hkk0)).
      * trivial.
      * intro ; specialize (H2 k0).
        destruct (k0 == k) eqn: Hkk0.
        + by rewrite CEP.Lemmas.find_add_eq //.
        + move /negP : Hkk0 => Hkk0.
          rewrite (CEP.Lemmas.find_add_neq Hkk0).
          rewrite eq_sym in Hkk0.
          by rewrite (CEP.Lemmas.remove_neq_o _ Hkk0) //.
      * inversion H3 ; by assumption.
      * intros ; specialize (H4 x e).
        split ; intro.
        + apply CEP.Lemmas.remove_mapsto_iff in H8.
          rewrite /PVM.SE.eq eq_sym in H8.
          destruct H4 as [H4 _].
          specialize (H4 (proj2 H8)).
          inversion H4 ; subst l y ; last by assumption.
          rewrite /CEP.Lemmas.O.eqke /PVM.SE.eq /fst in H10.
          destruct H8 as [H8 _].
          rewrite (proj1 H10) // in H8.
        + destruct (k == x) eqn: Hkx.
          - move /eqP : Hkx => Hkx ; subst x.
            inversion H3 ; subst x l.
            contradict H11.
            apply CEP.Lemmas.O.InA_eqke_eqk, (SetoidList.InA_eqA (@CEP.Lemmas.O.eqk_equiv def_expr)) with (y := (k, D_fexpr h)) in H8 ;
                  try by exact H8.
            rewrite /CEP.Lemmas.O.eqk /PVM.SE.eq eq_refl //.
          - move /negP : Hkx => Hkx.
            by apply (CEP.remove_2 Hkx), H4, SetoidList.InA_cons_tl, H8.
Qed.

Lemma ExpandBranch_stmt_tmap :
(* When comparing stmt_tmap and ExpandBranch_fun:
   if the first function gets a larger scope as input,
   it will produce a larger scope as output.

   This lemma is used by the next theorem (ExpandBranch_funs_checks_scopes). *)
forall (vm : CEP.t vertex_type) (s : HiFP.hfstmt)
       (old_vmscope2 new_vmscope2 : CEP.t vertex_type)
       (old_tmap new_tmap old_scope1 new_scope1 : CEP.t (ftype * HiF.forient))
       (old_def_ss new_def_ss : HiFP.hfstmt_seq) (old_conn_map new_conn_map : CEP.t def_expr),
   stmt_tmap (old_tmap, old_scope1) s vm = Some (new_tmap, new_scope1) ->
   ExpandBranch_fun s old_def_ss old_conn_map old_vmscope2 = Some (new_def_ss, new_conn_map, new_vmscope2) ->
   vm_and_tmap_compatible old_vmscope2 old_scope1 ->
   stmt_has_fully_inferred_ground_types s ->
      vm_and_tmap_compatible new_vmscope2 new_scope1
with ExpandBranch_stmts_tmap :
forall (vm : CEP.t vertex_type) (ss : HiFP.hfstmt_seq)
       (old_vmscope2 new_vmscope2 : CEP.t vertex_type)
       (old_tmap new_tmap old_scope1 new_scope1 : CEP.t (ftype * HiF.forient))
       (old_def_ss new_def_ss : HiFP.hfstmt_seq) (old_conn_map new_conn_map : CEP.t def_expr),
   stmts_tmap (old_tmap, old_scope1) ss vm = Some (new_tmap, new_scope1) ->
   ExpandBranches_funs ss old_def_ss old_conn_map old_vmscope2 = Some (new_def_ss, new_conn_map, new_vmscope2) ->
   vm_and_tmap_compatible old_vmscope2 old_scope1 ->
   stmts_have_fully_inferred_ground_types ss ->
      vm_and_tmap_compatible new_vmscope2 new_scope1.
Proof.
(* proven in the older version of the file *)
Admitted.

Lemma ExpandBranches_funs_preserves_compatibility :
    forall (ss : HiFP.hfstmt_seq)
           (old_tmap old_scope new_tmap new_scope : CEP.t (ftype * HiF.forient))
           (vm_tmap : CEP.t vertex_type)
           (old_comp_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr)
           (old_vmscope : CEP.t vertex_type)
           (new_vmscope : CEP.t vertex_type) (new_conn_map : CEP.t def_expr),
            stmts_have_fully_inferred_ground_types ss
        ->
            tmap_has_fully_inferred_ground_types old_tmap
        ->
            CEP.submap new_vmscope vm_tmap
        ->
            CEP.submap old_scope old_tmap
        ->
            stmts_tmap (old_tmap, old_scope) ss vm_tmap = Some (new_tmap, new_scope)
        ->
            vm_and_tmap_compatible old_vmscope old_scope
        ->
            ExpandBranches_funs ss old_comp_ss old_conn_map old_vmscope =
            Some (Qcat old_comp_ss (component_stmts_of ss), new_conn_map, new_vmscope)
        ->
            vm_and_tmap_compatible new_vmscope new_scope
with ExpandBranch_fun_preserves_compatibility :
    forall (s : HiFP.hfstmt)
           (old_tmap old_scope new_tmap new_scope : CEP.t (ftype * HiF.forient))
           (vm_tmap : CEP.t vertex_type)
           (old_comp_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr)
           (old_vmscope : CEP.t vertex_type)
           (new_vmscope : CEP.t vertex_type) (new_conn_map : CEP.t def_expr),
            stmt_has_fully_inferred_ground_types s
        ->
            tmap_has_fully_inferred_ground_types old_tmap
        ->
            CEP.submap new_vmscope vm_tmap
        ->
            CEP.submap old_scope old_tmap
        ->
            stmt_tmap (old_tmap, old_scope) s vm_tmap = Some (new_tmap, new_scope)
        ->
            vm_and_tmap_compatible old_vmscope old_scope
        ->
            ExpandBranch_fun s old_comp_ss old_conn_map old_vmscope =
            Some (Qcat old_comp_ss (component_stmt_of s), new_conn_map, new_vmscope)
        ->
            vm_and_tmap_compatible new_vmscope new_scope.
Proof.
* clear ExpandBranches_funs_preserves_compatibility.
  induction ss ; simpl ; intros.
  + injection H3 ; clear H3 ; intros ; subst new_tmap new_scope.
    rewrite Qcats0 in H5 ; injection H5 ; clear H5 ; intros ; subst new_conn_map new_vmscope.
    by exact H4.
  + specialize (ExpandBranch_fun_preserves_compatibility h old_tmap old_scope)
                with (vm_tmap := vm_tmap) (old_comp_ss := old_comp_ss)
                     (old_conn_map := old_conn_map) (old_vmscope := old_vmscope).
    generalize (stmt_submap vm_tmap h old_tmap old_scope H2) ; intro.
    specialize (ExpandBranch_stmt_tmap vm_tmap h old_vmscope)
          with (old_tmap := old_tmap) (old_scope1 := old_scope) (old_def_ss := old_comp_ss) (old_conn_map := old_conn_map) ; intro.
    move /andP : H => H.
    generalize (stmt_tmap_preserves_fully_inferred vm_tmap old_tmap old_scope h
                (proj1 H) H0 H2) ; intro.
    destruct (stmt_tmap (old_tmap, old_scope) h vm_tmap) as [[temp_tmap temp_scope]|] ; try by discriminate H3.
    specialize H7 with (1 := Logic.eq_refl).
    specialize (ExpandBranch_fun_preserves_compatibility) with (1 := proj1 H) (2 := H0) (4 := H2) (5 := Logic.eq_refl).
    specialize (ExpandBranch_component) with (s := h) (def_ss := old_comp_ss) (conn_map := old_conn_map) (scope := old_vmscope) ; intro.
    destruct (ExpandBranch_fun h old_comp_ss old_conn_map old_vmscope) as [[[temp_comp_ss temp_conn_map] temp_vmscope]|] ;
          try by discriminate H5.
    specialize H7 with (1 := Logic.eq_refl) (2 := H4) (3 := proj1 H).
    specialize (H9 _ _ _ Logic.eq_refl) ; destruct H9 as [H10 H9] ; subst temp_comp_ss.
    specialize (ExpandBranch_fun_preserves_compatibility) with (3 := Logic.eq_refl).

    rewrite -Qcat_assoc in H5.
    generalize (stmts_submap vm_tmap ss temp_tmap temp_scope (proj1 H6)) ; intro.
    rewrite H3 in H10.

    specialize IHss with (1 := proj2 H) (2 := H8) (3 := H1) (4 := proj1 H6) (5 := H3) (7 := H5).
    apply IHss ; by assumption.
* clear ExpandBranch_fun_preserves_compatibility.
  induction s ; simpl ; intros.
  + (* Sskip *)
    injection H3 ; clear H3 ; intros ; subst new_tmap new_scope.
    rewrite Qcats0 in H5 ; injection H5 ; clear H5 ; intros ; subst new_conn_map new_vmscope.
    by exact H4.
  + (* Swire *)
    intro.
    rewrite CEP.Lemmas.map_o /option_map.
    destruct f as [gt| |] ; try by discriminate H5.
    injection H5 ; clear H5 ; intros ; subst new_conn_map new_vmscope.
    destruct (CEP.find s old_tmap) ; first by discriminate H3.
    generalize (fully_inferred_does_not_change gt s vm_tmap H) ; intro.
    destruct (code_type_find_vm_widths (Gtyp gt) s vm_tmap) as [[[gt'| |] _]|] ;
          last (by discriminate H3) ;
          try (by contradiction H5) ;
          subst gt'.
    injection H3 ; clear H3 ; intros ; subst new_tmap new_scope.
    destruct (k == s) eqn: Hks.
    - rewrite (CEP.Lemmas.find_add_eq Hks) in H8.
      by rewrite (CEP.Lemmas.find_add_eq Hks) //.
    - rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hks))) in H8.
      rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hks))).
      apply H4.
      by rewrite CEP.Lemmas.map_o /option_map //.
  + (* Sreg *)
    intro.
    rewrite CEP.Lemmas.map_o /option_map.
    destruct (type h) as [gt| |] ; try by discriminate H5.
    destruct (rhs_type_of_expr (clock h) old_vmscope) ; last by discriminate H5.
    destruct (reset h) as [|rst_sig rst_val].
    1,2: move /andP : H => [H6 H].
    2: move /andP : H6 => [/andP [H6 _] _].
    2: assert (tmap_has_fully_inferred_ground_types old_scope)
          by (intro ; specialize (H0 v) ; specialize (H2 v) ;
              destruct (CEP.find v old_scope) ; last (by trivial) ;
              specialize (H2 _ Logic.eq_refl) ; rewrite H2 // in H0).
    2: apply (type_of_expr_and_rhs_type_of_expr rst_sig old_vmscope old_scope) in H6 ;
             try (by assumption) ; clear H7.
    2: destruct (rhs_type_of_expr rst_sig old_vmscope) as [[[[|[|]]| | | | | |] Hrst_sig]|] ; try by discriminate H5.
    2,3: destruct (rhs_type_of_expr rst_val old_vmscope) ; last by discriminate H5.
    1-3: injection H5 ; clear H5 ; intros ; subst new_conn_map new_vmscope.
    1-3: destruct (CEP.find s old_tmap) ; first by discriminate H3.
    1-3: destruct (type_of_expr (clock h) old_scope) ; last by discriminate H3.
    1-3: generalize (fully_inferred_does_not_change gt s vm_tmap H) ; intro.
    1-3: destruct (code_type_find_vm_widths (Gtyp gt) s vm_tmap) as [[[gt'| |] _]|] ;
          last (by discriminate H3) ;
          try (by contradiction H5) ;
          subst gt'.
    2-3: rewrite (proj2 H6) in H3 ; clear H6.
    2: destruct (type_of_expr rst_val (CEP.add s (Gtyp gt, HiF.Duplex) old_scope)) ; last by discriminate H3.
    3: destruct (type_of_expr rst_val old_scope) ; last by discriminate H3.
    1-3: injection H3 ; clear H3 ; intros ; subst new_tmap new_scope.
    1-3: destruct (k == s) eqn: Hks.
    - 1,3,5: rewrite (CEP.Lemmas.find_add_eq Hks) in H9.
      1-3: by rewrite (CEP.Lemmas.find_add_eq Hks) //.
    - 1-3: rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hks))) in H9.
      1-3: rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hks))) //.
      1-3: apply H4.
      1-3: by rewrite CEP.Lemmas.map_o /option_map //.
  + (* Smem *)
    by discriminate H5.
  + (* Sinst *)
    by discriminate H5.
  + (* Snode *)
    intro.
    rewrite CEP.Lemmas.map_o /option_map.
    assert (tmap_has_fully_inferred_ground_types old_scope)
          by (intro ; specialize (H0 v) ; specialize (H2 v) ;
              destruct (CEP.find v old_scope) ; last (by trivial) ;
              specialize (H2 _ Logic.eq_refl) ; rewrite H2 // in H0).
    apply (type_of_expr_and_rhs_type_of_expr h old_vmscope old_scope H) in H6 ;
             last (by assumption).
    destruct (rhs_type_of_expr h old_vmscope) as [[]|] ; last by discriminate H5.
    injection H5 ; clear H5 ; intros ; subst new_conn_map new_vmscope.
    destruct (CEP.find s old_tmap) ; first by discriminate H3.
    rewrite (proj2 H6) in H3.
    injection H3 ; clear H3 ; intros ; subst new_tmap new_scope.
    destruct (k == s) eqn: Hks.
    - rewrite (CEP.Lemmas.find_add_eq Hks) in H9.
      by rewrite (CEP.Lemmas.find_add_eq Hks) //.
    - rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hks))) in H9.
      rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hks))).
      apply H4.
      by rewrite CEP.Lemmas.map_o /option_map //.
  + (* Sfcnct *)
    intro.
    rewrite CEP.Lemmas.map_o /option_map.
    destruct h ; try by discriminate H5.
    destruct (CEP.find s old_vmscope) as [[gt_tgt|gt_tgt|gt_tgt|gt_tgt|gt_tgt]|] ; try by discriminate H5.
    1-3: destruct (rhs_type_of_expr h0 old_vmscope) as [[gt_src _]|] ; last by discriminate H5.
    1-3: destruct (match gt_tgt with
                   | Fuint _ => match gt_src with | Fuint _ | Fuint_implicit _ => true | _ => false end
                   | Fsint _ => match gt_src with | Fsint _ | Fsint_implicit _ => true | _ => false end
                   | Fuint_implicit w_tgt => match gt_src with | Fuint w_src | Fuint_implicit w_src => w_src <= w_tgt | _ => false end
                   | Fsint_implicit w_tgt => match gt_src with | Fsint w_src | Fsint_implicit w_src => w_src <= w_tgt | _ => false end
                   | Fclock => match gt_src with | Fclock => true | _ => false end
                   | Freset => false
                   | Fasyncreset => match gt_src with | Fasyncreset => true | _ => false end
       end) ; last by discriminate H5.
    1-3: injection H5 ; clear H5 ; intros ; subst new_conn_map new_vmscope.
    1-3: simpl type_of_ref in H3.
    1-3: destruct (CEP.find s old_scope) ; last by discriminate H3.
    1-3: destruct (type_of_expr h0 old_scope) ; last by discriminate H3.
    1-3: injection H3 ; clear H3 ; intros ; subst new_tmap new_scope.
    1-3: apply H4.
    1-3: by rewrite CEP.Lemmas.map_o /option_map //.
  + (* Sinvalid *)
    intro.
    rewrite CEP.Lemmas.map_o /option_map.
    destruct h ; try by discriminate H5.
    destruct (CEP.find s old_vmscope) as [[gt_tgt|gt_tgt|gt_tgt|gt_tgt|gt_tgt]|] ; try by discriminate H5.
    1-3: injection H5 ; clear H5 ; intros ; subst new_conn_map new_vmscope.
    1-3: simpl type_of_ref in H3.
    1-3: destruct (CEP.find s old_scope) ; last by discriminate H3.
    1-3: injection H3 ; clear H3 ; intros ; subst new_tmap new_scope.
    1-3: apply H4.
    1-3: by rewrite CEP.Lemmas.map_o /option_map //.
  + (* Swhen *)
Admitted.

(*
Lemma extend_convert_to_connect_stmts :
forall (vm_old : CEP.t vertex_type) (ct_old conn_map1 conn_map2 : CEP.t def_expr)
       (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t (ftype * HiF.forient)),
        Sem_frag_stmts vm_old ct_old (convert_to_connect_stmts (extend_map_with conn_map1 conn_map2)) vm_new ct_new tmap
    ->
        (exists ct_temp : CEP.t def_expr,
                Sem_frag_stmts vm_old ct_old (convert_to_connect_stmts conn_map2) vm_old ct_temp tmap
            /\
                Sem_frag_stmts vm_old ct_temp (convert_to_connect_stmts conn_map1) vm_new ct_new tmap).
Proof.
intros.
exists (extend_map_with conn_map2 ct_old). *)

(*---------------------------------------------------------------------------*)
(* Inductive core statement of the correctness proof                         *)

Definition Ps (s : HiFP.hfstmt) : Prop :=
forall (vm_old sf_vm old_vmscope eb_vmscope : CEP.t vertex_type)
       (ct_old sf_ct eb_conn_map : CEP.t def_expr)
       (old_tmap old_scope tm_tmap tm_scope tmap : CEP.t (ftype * HiF.forient))
       (old_comp : HiFP.hfstmt_seq),
    tmap_has_fully_inferred_ground_types tmap ->
    vm_and_tmap_compatible sf_vm tmap ->
    vm_and_ct_compatible vm_old ct_old ->
    stmt_has_fully_inferred_ground_types s ->
    CEP.submap old_scope old_tmap ->
    stmt_tmap (old_tmap, old_scope) s sf_vm = Some (tm_tmap, tm_scope) ->
    CEP.submap tm_tmap tmap ->
    ExpandBranch_fun s old_comp (CEP.empty def_expr) old_vmscope = Some (Qcat old_comp (component_stmt_of s), eb_conn_map, eb_vmscope) ->
    CEP.submap old_vmscope vm_old ->
    Sem_frag_stmts vm_old ct_old (Qcat (component_stmt_of s)
                                       (convert_to_connect_stmts eb_conn_map))
                   sf_vm sf_ct tmap ->
    Sem_frag_stmt vm_old ct_old s sf_vm sf_ct tmap.

Definition Pss (ss : HiFP.hfstmt_seq) : Prop :=
forall (vm_old sf_vm old_vmscope eb_vmscope : CEP.t vertex_type)
       (ct_old sf_ct eb_conn_map : CEP.t def_expr)
       (old_tmap old_scope tm_tmap tm_scope tmap : CEP.t (ftype * HiF.forient))
       (old_comp : HiFP.hfstmt_seq),
    tmap_has_fully_inferred_ground_types tmap ->
    vm_and_tmap_compatible sf_vm tmap ->
    vm_and_ct_compatible vm_old ct_old ->
    stmts_have_fully_inferred_ground_types ss ->
    CEP.submap old_scope old_tmap ->
    stmts_tmap (old_tmap, old_scope) ss sf_vm = Some (tm_tmap, tm_scope) ->
    CEP.submap tm_tmap tmap ->
    ExpandBranches_funs ss old_comp (CEP.empty def_expr) old_vmscope = Some (Qcat old_comp (component_stmts_of ss), eb_conn_map, eb_vmscope) ->
    CEP.submap old_vmscope vm_old ->
    Sem_frag_stmts vm_old ct_old (Qcat (component_stmts_of ss)
                                       (convert_to_connect_stmts eb_conn_map))
                   sf_vm sf_ct tmap ->
    Sem_frag_stmts vm_old ct_old ss sf_vm sf_ct tmap.

Lemma ExpandBranches_funs_cat :
forall (ss1 ss2 : HiFP.hfstmt_seq) (old_comp : HiFP.hfstmt_seq)
       (old_conn_map : CEP.t def_expr) (old_vmscope : CEP.t vertex_type),
    ExpandBranches_funs (Qcat ss1 ss2) old_comp old_conn_map old_vmscope =
    match ExpandBranches_funs ss1 old_comp old_conn_map old_vmscope with
    | Some (temp_comp_ss, temp_conn_map, temp_vmscope) =>
        ExpandBranches_funs ss2 temp_comp_ss temp_conn_map temp_vmscope
    | None => None
    end.
Proof.
Admitted.

Lemma stmts_have_fully_inferred_ground_types_cat :
forall (ss1 ss2 : HiFP.hfstmt_seq),
        stmts_have_fully_inferred_ground_types (Qcat ss1 ss2)
    <->
            stmts_have_fully_inferred_ground_types ss1
        /\
            stmts_have_fully_inferred_ground_types ss2.
Proof.
intros ; split.
Admitted.

Lemma component_stmts_of_cat :
forall (ss1 ss2 : HiFP.hfstmt_seq),
    component_stmts_of (Qcat ss1 ss2) =
    Qcat (component_stmts_of ss1) (component_stmts_of ss2).
Proof.
Admitted.

Lemma ExpandBranches_Sem_ct :
(* This theorem relates the connection maps generated by Sem_frag_stmts and ExpandBranch_funs. *)
forall (ss old_def_ss : HiFP.hfstmt_seq) (vm_old vm_new vm_tmap old_vmscope : CEP.t vertex_type)
       (ct_old ct_new old_conn_map : CEP.t def_expr) (tmap : CEP.t (ftype * HiF.forient))
       (old_tmap_scope new_tmap_scope : CEP.t (ftype * HiF.forient) * CEP.t (ftype * HiF.forient)),
    stmts_have_fully_inferred_ground_types ss ->
    tmap_has_fully_inferred_ground_types old_tmap_scope.1 ->
    vm_and_tmap_compatible old_vmscope old_tmap_scope.2 ->
    CEP.submap old_tmap_scope.2 old_tmap_scope.1 ->
    stmts_tmap old_tmap_scope ss vm_tmap = Some new_tmap_scope ->
    CEP.submap new_tmap_scope.1 tmap ->
    CEP.submap old_vmscope vm_old ->
    vm_and_ct_compatible vm_old ct_old ->
    Sem_frag_stmts vm_old ct_old ss vm_new ct_new tmap ->
    CEP.submap old_conn_map ct_old ->
        match ExpandBranches_funs ss old_def_ss old_conn_map old_vmscope with
        | Some (def_ss, new_conn_map, new_scope) =>
                (* def_ss = Qcat old_def_ss (component_stmts_of ss) *)
                CEP.submap new_scope vm_new
            /\
                CEP.submap new_conn_map ct_new
        | None => True
        end
with ExpandBranch_Sem_ct :
forall (s : HiFP.hfstmt) (old_def_ss : HiFP.hfstmt_seq) (vm_old vm_new vm_tmap old_vmscope : CEP.t vertex_type)
       (ct_old ct_new old_conn_map : CEP.t def_expr) (tmap : CEP.t (ftype * HiF.forient))
       (old_tmap_scope new_tmap_scope : CEP.t (ftype * HiF.forient) * CEP.t (ftype * HiF.forient)),
    stmt_has_fully_inferred_ground_types s ->
    tmap_has_fully_inferred_ground_types old_tmap_scope.1 ->
    vm_and_tmap_compatible old_vmscope old_tmap_scope.2 ->
    CEP.submap old_tmap_scope.2 old_tmap_scope.1 ->
    stmt_tmap old_tmap_scope s vm_tmap = Some new_tmap_scope ->
    CEP.submap new_tmap_scope.1 tmap ->
    CEP.submap old_vmscope vm_old ->
    vm_and_ct_compatible vm_old ct_old ->
    Sem_frag_stmt vm_old ct_old s vm_new ct_new tmap ->
    CEP.submap old_conn_map ct_old ->
        match ExpandBranch_fun s old_def_ss old_conn_map old_vmscope with
        | Some (def_ss, new_conn_map, new_scope) =>
               (* def_ss = Qcat old_def_ss (component_stmt_of s) *)
                CEP.submap new_scope vm_new
            /\
                CEP.submap new_conn_map ct_new
        | None => True
        end.
Proof.
(* This proof is copied from the older version,
let's see if it still works without much changes. *)
* clear ExpandBranches_Sem_ct.
  induction ss ; simpl ; intros ;
        first by split ;
                 first (by apply (CEP.Lemmas.submap_trans H5),
                                 (CEP.Lemmas.Equal_submap (proj1 H7))) ;
                 last  (by apply (CEP.Lemmas.submap_trans H8),
                                 (CEP.Lemmas.Equal_submap (proj2 H7))).
  move /andP : H => [H H9].
  destruct H7 as [vm' [ct' [H7 H10]]].
  specialize (ExpandBranch_Sem_ct h old_def_ss vm_old vm' vm_tmap old_vmscope ct_old ct' old_conn_map tmap old_tmap_scope).
  generalize (stmt_submap vm_tmap h old_tmap_scope.1 old_tmap_scope.2 H2) ; intro.
  rewrite -surjective_pairing in H11.
  specialize (ExpandBranch_stmt_tmap vm_tmap h old_vmscope)
        with (old_tmap := old_tmap_scope.1) (old_scope1 := old_tmap_scope.2) (old_def_ss := old_def_ss) (old_conn_map := old_conn_map) ; intro.
  rewrite -surjective_pairing in H12.
  destruct (stmt_tmap old_tmap_scope h vm_tmap) as [[tmap' scope']|] eqn: Htmap_scope' ; last by discriminate H3.
  destruct new_tmap_scope as [new_tmap new_scope] ; simpl fst in H4.
  specialize H12 with (1 := Logic.eq_refl).
  generalize (stmts_submap vm_tmap ss tmap' scope' (proj1 H11)) ; intro.
  rewrite H3 in H13.
  specialize (ExpandBranch_Sem_ct (tmap', scope')
              H H0 H1 H2 Logic.eq_refl
              (CEP.Lemmas.submap_trans (proj1 (proj2 H13)) H4)
              H5 H6 H7 H8) ;
        simpl fst in ExpandBranch_Sem_ct.
  destruct (ExpandBranch_fun h old_def_ss old_conn_map old_vmscope) as [[[temp_def_ss temp_conn_map] temp_vmscope]|] ;
        last by done.
  specialize (H12 temp_vmscope temp_def_ss temp_conn_map Logic.eq_refl H1 H).
  specialize (stmt_tmap_preserves_fully_inferred vm_tmap old_tmap_scope.1 old_tmap_scope.2 h H H0 H2) ; intro.
  rewrite -surjective_pairing Htmap_scope' in H14.
  apply (IHss temp_def_ss vm' vm_new vm_tmap temp_vmscope ct' ct_new temp_conn_map tmap (tmap', scope') (new_tmap, new_scope)) ;
          try by assumption.
  + by apply H11.
  + by apply ExpandBranch_Sem_ct.
  + by apply Sem_frag_stmt_compatible with (1 := H7), H6.
  + by apply ExpandBranch_Sem_ct.
* clear ExpandBranch_Sem_ct.
  destruct s ; simpl ; try done ; intros.
  all: assert (H10: tmap_has_fully_inferred_ground_types old_tmap_scope.2)
        by (intro ; specialize (H2 v) ; specialize (H0 v) ;
            destruct (CEP.find v old_tmap_scope.2) as [[ft ori]|] ; last (by trivial) ;
            rewrite (H2 _ Logic.eq_refl) // in H0).
  + (* Sskip *)
    split.
    - by apply (CEP.Lemmas.submap_trans H5),
               (CEP.Lemmas.Equal_submap (proj1 H7)).
    - by apply (CEP.Lemmas.submap_trans H8),
               (CEP.Lemmas.Equal_submap (proj2 H7)).
  + (* Swire *)
    destruct f as [gt| |] ; try by done.
    destruct (CEP.find s old_tmap_scope.1) ; first by discriminate H3.
    generalize (fully_inferred_does_not_change gt s vm_tmap H) ; intro.
    destruct (code_type_find_vm_widths (Gtyp gt) s vm_tmap) as [[[gt'| |] _]|] ; try by done.
    subst gt'.
    destruct new_tmap_scope as [new_tmap new_scope] ; simpl fst in H4.
    injection H3 ; clear H3 ; intros ; subst new_tmap new_scope.
    specialize (H4 s).
    rewrite (CEP.Lemmas.find_add_eq (eq_refl s)) in H4 ;
          specialize H4 with (1 := Logic.eq_refl).
    rewrite H4 // /size_of_ftype add1n in H7.
    split.
    - intro.
      destruct (k == s) eqn: Hks.
      * move /eqP : Hks => Hks ; subst k.
        rewrite (CEP.Lemmas.find_add_eq (eq_refl s)) ; intros.
        injection H3 ; clear H3 ; intros ; subst v.
        destruct H7 as [H7 _].
        specialize (H7 N0) ; simpl in H7.
        rewrite add0n nat_of_binK -surjective_pairing // in H7.
        by apply H7.
      * rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hks))).
        destruct H7 as [_ [H7 _]].
        specialize (H7 k.1 k.2).
        rewrite -surjective_pairing in H7.
        move /eqP : Hks => Hks.
        destruct (k.1 == s.1) eqn: Hks1 ; move /eqP : Hks1 => Hks1 ;
              last by rewrite -(H7 (or_introl Hks1)) // ; apply H5.
        destruct (Nat.compare_spec k.2 s.2).
        * specialize (injective_projections k s Hks1) ; intro.
          rewrite -(nat_of_binK k.2) -(nat_of_binK s.2) H3 in H9.
          rewrite H9 // in Hks.
        * rewrite -H7 ; first (by apply H5).
          right ; left ; move /ltP : H3 => H3 ; exact H3.
        * rewrite -H7 ; first (by apply H5).
          right ; right ; move /ltP : H3 => H3 ; exact H3.
    - intro.
      destruct (k == s) eqn: Hks.
      * move /eqP : Hks => Hks ; subst k.
        destruct H7 as [H7 _] (* sic! *).
        specialize (H7 N0) ; simpl in H7.
        rewrite add0n nat_of_binK -surjective_pairing // in H7.
        intros.
        apply H8 in H3.
        specialize (H6 s).
        by rewrite (proj1 H7) H3 // in H6.
      * destruct H7 as [_ [_ [H7 _]]].
        specialize (H7 k.1 k.2).
        rewrite -surjective_pairing in H7.
        move /eqP : Hks => Hks.
        destruct (k.1 == s.1) eqn: Hks1 ; move /eqP : Hks1 => Hks1 ;
              last by rewrite -(H7 (or_introl Hks1)) // ; apply H8.
        destruct (Nat.compare_spec k.2 s.2).
        * specialize (injective_projections k s Hks1) ; intro.
          rewrite -(nat_of_binK k.2) -(nat_of_binK s.2) H3 in H9.
          rewrite H9 // in Hks.
        * rewrite -H7 ; first (by apply H8).
          right ; left ; move /ltP : H3 => H3 ; exact H3.
        * rewrite -H7 ; first (by apply H8).
          right ; right ; move /ltP : H3 => H3 ; exact H3.
  + (* Sreg *)
    destruct (type h) as [gt| |] ; try by done.
    destruct (rhs_type_of_expr (clock h) old_vmscope) ; last by trivial.
    destruct (reset h) as [|rst_sig rst_val].
    1,2: move /andP : H => [H9 H].
    2: move /andP : H9 => [/andP [H9 _] _] ;
       apply (type_of_expr_and_rhs_type_of_expr rst_sig old_vmscope old_tmap_scope.2) with (2 := H10) (3 := H1) in H9.
    2: destruct (rhs_type_of_expr rst_sig old_vmscope) as [[[[|[|]]| | | | | |] p]|] ;
               try (by trivial) ;
               destruct H9 as [_ H9].
    2-3: destruct (rhs_type_of_expr rst_val old_vmscope) ; last by trivial.

    1-3: destruct (CEP.find s old_tmap_scope.1) eqn: Hfind_old ; first by discriminate H3.
    1-3: destruct (type_of_expr (clock h) old_tmap_scope.2) ; last by discriminate H3.
    1-3: generalize (fully_inferred_does_not_change gt s vm_tmap H) ; intro.
    1-3: destruct (code_type_find_vm_widths (Gtyp gt) s vm_tmap) as [[[gt'| |] _]|] ; try by done.
    1-3: subst gt'.
    2-3: rewrite H9 in H3.
    2: destruct (type_of_expr rst_val (CEP.add s (Gtyp gt, HiF.Duplex) old_tmap_scope.2)) ;
                last by discriminate H3.
    3: destruct (type_of_expr rst_val old_tmap_scope.2) ;
                last by discriminate H3.
    1-3: destruct new_tmap_scope as [new_tmap new_scope] ; simpl fst in H4.
    1-3: injection H3 ; clear H3 ; intros ; subst new_tmap new_scope.
    2-3: generalize (type_of_expr_submap rst_sig old_tmap_scope.2 tmap
                     (CEP.Lemmas.submap_trans H2
                      (CEP.Lemmas.submap_add_find_none H4 Hfind_old))) ;
               rewrite H9 ; clear H9 ; intro H9.
    1-3: specialize (H4 s).
    1-3: rewrite (CEP.Lemmas.find_add_eq (eq_refl s)) in H4 ;
          specialize H4 with (1 := Logic.eq_refl).
    1-3: rewrite H4 // /size_of_ftype add1n in H7.
    1-3: destruct H7 as [_ H7].
    1-3: split.
    - 1,3,5: intro.
      1-3: destruct (k == s) eqn: Hks.
      * 1,3,5: move /eqP : Hks => Hks ; subst k.
        1-3: rewrite (CEP.Lemmas.find_add_eq (eq_refl s)) ; intros.
        1-3: injection H3 ; clear H3 ; intros ; subst v.
        1-3: destruct H7 as [H7 _].
        1-3: specialize (H7 N0) ; simpl in H7.
        1-3: rewrite add0n nat_of_binK -surjective_pairing // in H7.
        2-3: rewrite H9 in H7.
        1-3: by apply H7.
      * 1-3: rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hks))).
        1-3: destruct H7 as [_ [_ [_ [H7 _]]]].
        1-3: specialize (H7 k.1 k.2).
        1-3: rewrite -surjective_pairing in H7.
        1-3: move /eqP : Hks => Hks.
        1-3: destruct (k.1 == s.1) eqn: Hks1 ; move /eqP : Hks1 => Hks1 ;
                   last by rewrite -(H7 (or_introl Hks1)) // ; apply H5.
        1-3: clear H9.
        1-3: destruct (Nat.compare_spec k.2 s.2).
        * 1,4,7: specialize (injective_projections k s Hks1) ; intro.
          1-3: rewrite -(nat_of_binK k.2) -(nat_of_binK s.2) H3 in H9.
          1-3: rewrite H9 // in Hks.
        * 1,3,5: rewrite -H7 ; first (by apply H5).
          1-3: right ; left ; move /ltP : H3 => H3 ; exact H3.
        * 1-3: rewrite -H7 ; first (by apply H5).
          1-3: right ; right ; move /ltP : H3 => H3 ; exact H3.
    - 1-3: intro.
      1-3: destruct (k == s) eqn: Hks.
      * 1,3,5: move /eqP : Hks => Hks ; subst k.
        1-3: destruct H7 as [H7 _] (* sic! *).
        1-3: specialize (H7 N0) ; simpl in H7.
        1-3: rewrite add0n nat_of_binK -surjective_pairing // in H7.
        1-3: intros.
        1-3: apply H8 in H3.
        1-3: specialize (H6 s).
        1-3: by rewrite (proj1 H7) H3 // in H6.
      * 1-3: destruct H7 as [_ [_ [_ [_ H7]]]].
        1-3: specialize (H7 k.1 k.2).
        1-3: rewrite -surjective_pairing in H7.
        1-3: move /eqP : Hks => Hks.
        1-3: destruct (k.1 == s.1) eqn: Hks1 ; move /eqP : Hks1 => Hks1 ;
              last by rewrite -(H7 (or_introl Hks1)) // ; apply H8.
        1-3: destruct (Nat.compare_spec k.2 s.2).
        * 1,4,7: specialize (injective_projections k s Hks1) ; intro.
          1-3: rewrite -(nat_of_binK k.2) -(nat_of_binK s.2) H3 in H11.
          1-3: rewrite H11 // in Hks.
        * 1,3,5: rewrite -H7 ; first (by apply H8).
          1-3: right ; left ; move /ltP : H3 => H3 ; exact H3.
        * 1-3: rewrite -H7 ; first (by apply H8).
          1-3: right ; right ; move /ltP : H3 => H3 ; exact H3.
  + (* Snode *)
    admit.
(*
    destruct (type_of_expr h old_scope) as [[_ _]|] ; last by done.
    generalize (@CEP.Lemmas.submap_add_find_none _ old_tmap_scope.1 tmap s) ; intro.
    destruct (CEP.find s old_tmap_scope.1) ; first by discriminate H3.
    generalize (expr_preserves_fully_inferred old_tmap_scope.1 H0 h H) ; intro.
    generalize (type_of_expr_submap h old_tmap_scope.2 old_tmap_scope.1 H2) ; intro.
    generalize (type_of_expr_submap h old_tmap_scope.1 tmap) ; intro.
    destruct (type_of_expr h old_tmap_scope.2) as [[newt p]|] ; last by discriminate H3.
    rewrite H9 in H8 H10 ; clear H9.
    destruct newt as [gt| |] ; try by contradiction H8.
    destruct new_tmap_scope as [new_tmap new_scope].
    injection H3 ; clear H3 ; intros _ H3.
    rewrite /fst -H3 in H4.
    specialize (H7 (Gtyp gt, HiF.Source) H4 Logic.eq_refl).
    rewrite (H10 H7) in H5 ; clear p H10 H7.
    destruct H5 as [_ [_ H5]].
    apply CEP.Lemmas.Equal_trans with (m' := ct_old) ; last by exact H6.
    apply CEP.Lemmas.Equal_sym, H5. *)
  + (* Sfcnct *)
    destruct h as [var| | |] ; try (by done).
    rewrite /ref_has_fully_inferred_ground_types andTb in H.
    simpl type_of_ref in H3.
    destruct h0 eqn: Hexpr.
    1-6: specialize (type_of_expr_and_rhs_type_of_expr) with (1 := H) (2 := H10) (3 := H1) ; intro.
    7: specialize (type_of_ref_and_rhs_type_of_ref) with (1 := H) (2 := H10) (3 := H1) ; intro.
    1-7: specialize (H1 var).
    1-7: rewrite CEP.Lemmas.map_o /option_map in H1.
    1-7: destruct (CEP.find var old_vmscope) as [[gt_tgt|gt_tgt|gt_tgt|gt_tgt|gt_tgt]|] ; try by trivial.
    1-21: specialize H1 with (1 := Logic.eq_refl).
    1-18: rewrite -{1}Hexpr ; rewrite -{1}Hexpr in H9 ;
          destruct (rhs_type_of_expr h0 old_vmscope) as [[gt_src p]|] ;
                try (by trivial).
    19-21: simpl rhs_type_of_expr ; simpl type_of_expr in H3 ;
           destruct (rhs_type_of_ref h old_vmscope) as [gt_src|] ; try (by trivial).
    1-21: destruct H9 as [H11 H9].
    19-21: destruct H9 as [H9|H9].
    1-24: rewrite H1 H9 in H3 ; injection H3 ; clear H3 ; intro ; subst new_tmap_scope.
    1-24: simpl list_lhs_ref_p in H7.
    1-24: apply H2, H4 in H1.
    1-24: rewrite H1 in H7.
    1-18: generalize (type_of_expr_submap h0 old_tmap_scope.2 tmap (CEP.Lemmas.submap_trans H2 H4)) ;
                rewrite Hexpr H9 ; intro ;
          rewrite H3 in H7.
    19-24: generalize (type_of_ref_submap h old_tmap_scope.2 tmap (CEP.Lemmas.submap_trans H2 H4)) ;
                rewrite H9 ; intro ;
           generalize (list_lhs_ref_p_type tmap h) ;
                rewrite H3 ; clear H3 ; intro ;
           destruct (list_lhs_ref_p h tmap) as [[list_src [ft_src ori_src]]|] ;
                 last (by contradiction H3) ;
           injection H3 ; clear H3 ; intros ; subst ft_src ori_src.
    1-24: rewrite /mkseq in H7 ; simpl in H7 ;
         rewrite N.add_0_r -surjective_pairing in H7.
    19-24: destruct gt_src ;
                 try (by discriminate H11) ;
           destruct list_src as [|ic [|]] ;
                 try (by discriminate (proj1 (proj2 (proj2 H7)))).
    1-42: rewrite (proj1 (proj2 H7)).
    1-42: split ;
                first by apply (CEP.Lemmas.submap_trans H5),
                               CEP.Lemmas.Equal_submap, H7.
    1-42: destruct H7 as [_ [_ H7]].
    1-42: intro.
    1-42: destruct (k == var) eqn: Hkvar ;
                first by (rewrite (CEP.Lemmas.find_add_eq Hkvar) ;
                          move /eqP : Hkvar => Hkvar ; subst k ;
                          destruct H7 as [H7 _] ;
                          try (specialize (H7 N0) ; simpl in H7 ; destruct H7 as [_ H7]) ;
                          try (move /andP : H7 => [/andP [_ /eqP H7] _]) ;
                          rewrite H7 //).
    1-42: rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
    1-18: destruct H7 as [_ H7] ;
          specialize (H7 k) ;
          rewrite mem_seq1 Hkvar in H7 ;
          rewrite -H7 // ;
          by apply H8.
    (* What remains is reference: *)
    1-24: destruct (k == ic) eqn: Hkic ;
                last by (destruct H7 as [_ H7] ;
                         specialize (H7 k) ;
                         rewrite mem_seq1 Hkvar mem_seq1 Hkic in H7 ;
                         rewrite -H7 // ;
                         apply H8).
    1-24: move /eqP : Hkic => Hkic ; subst ic.
    1-24: destruct H7 as [H7 _] ;
          rewrite (eq_sym var) Hkvar orFb in H7 ;
          move /andP : H7 => [_ /eqP H7].
    1-24: rewrite H7 ; by apply H8.
  + (* Sinvalid *)
    destruct h as [var| | |] ; try (by done).
    simpl type_of_ref in H3.
    specialize (H1 var).
    rewrite CEP.Lemmas.map_o /option_map in H1.
    destruct (CEP.find var old_vmscope) as [[gt_tgt|gt_tgt|gt_tgt|gt_tgt|gt_tgt]|] ; try by trivial.
    1-3: specialize H1 with (1 := Logic.eq_refl).
    1-3: rewrite H1 in H3 ; injection H3 ; clear H3 ; intro ; subst new_tmap_scope.
    1-3: simpl list_lhs_ref_p in H7.
    1-3: apply H2, H4 in H1.
    1-3: rewrite H1 in H7.
    1-3: rewrite /mkseq in H7 ; simpl in H7 ;
         rewrite N.add_0_r -surjective_pairing in H7.
    1-3: split ;
                first by apply (CEP.Lemmas.submap_trans H5),
                               CEP.Lemmas.Equal_submap, H7.
    1-3: destruct H7 as [_ H7].
    1-3: intro.
    1-3: destruct (k == var) eqn: Hkvar ;
                first by (rewrite (CEP.Lemmas.find_add_eq Hkvar) ;
                          move /eqP : Hkvar => Hkvar ; subst k ;
                          destruct H7 as [H7 _] ;
                          specialize (H7 N0) ; simpl in H7 ; destruct H7 as [_ H7] ;
                          rewrite H7 //).
    1-3: rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
    1-3: destruct H7 as [_ H7] ;
          specialize (H7 k) ;
          rewrite mem_seq1 Hkvar in H7 ;
          rewrite -H7 // ;
          by apply H8.
  + (* Swhen *)
    (*
    rename h into cond ; rename h0 into ss_true ; rename h1 into ss_false.
    destruct (type_of_expr cond old_tmap_scope.2) ; last by discriminate H3.
    generalize (stmts_submap vm_tmap ss_true old_tmap_scope.1 old_tmap_scope.2 H2) ; intro.
    rewrite -(surjective_pairing) in H7.
    assert (CEP.submap old_scope tmap).
          apply (CEP.Lemmas.submap_trans H1).
          apply (CEP.Lemmas.submap_trans H2).
          destruct (stmts_tmap old_tmap_scope ss_true vm_tmap) as [[tmap_true scope_true]|] ; last by discriminate H3.
          generalize (CEP.Lemmas.submap_trans (proj2 (proj2 H7)) (proj1 H7)) ; intro.
          generalize (stmts_submap vm_tmap ss_false tmap_true old_tmap_scope.2 H8) ; intro.
          destruct (stmts_tmap (tmap_true, old_tmap_scope.2) ss_false vm_tmap) as [[tmap_false scope_false]|] ; last by discriminate H3.
          apply (CEP.Lemmas.submap_trans (proj1 (proj2 H7))).
          apply (CEP.Lemmas.submap_trans (proj1 (proj2 H9))).
          destruct new_tmap_scope as [new_tmap new_scope].
          injection H3 ; clear H3 ; intros _ H3.
          rewrite H3 //.
    generalize (type_of_expr_submap cond old_scope tmap H8) ; intro.
    destruct (type_of_expr cond old_scope) as [[[[[|[]]| | | | | |]| |] p]|] ; try by done.
    generalize (ExpandBranches_Sem_ct ss_true old_def_ss vm_old) ; intro.
    specialize H10 with (vm_tmap := vm_tmap) (old_tmap_scope := old_tmap_scope).
    move /andP : H => [/andP [_ Htrue] Hfalse].
    generalize (stmts_tmap_preserves_fully_inferred vm_tmap ss_true old_tmap_scope.1 old_tmap_scope.2 Htrue H0 H2) ; intro.
    rewrite -surjective_pairing in H.
    destruct (stmts_tmap old_tmap_scope ss_true vm_tmap) as [[tmap_true scope_true]|] ; last by discriminate H3.
    rewrite H9 in H5.
    destruct H5 as [vm_true [ct_true [ct_false H5]]].
    specialize (H10 vm_true ct_old ct_true old_conn_map old_scope tmap (tmap_true, scope_true) Htrue H0 H1 H2 Logic.eq_refl)
          with (2 := proj1 H5) (3 := H6).
    destruct (ExpandBranch_funs ss_true old_def_ss old_conn_map old_scope) as [[[true_def_ss true_conn_map] _]|] ; last by done.
    assert (CEP.submap old_tmap_scope.2 tmap_true)
          by (apply (CEP.Lemmas.submap_trans (proj2 (proj2 H7)) (proj1 H7))).
    specialize (ExpandBranches_Sem_ct ss_false true_def_ss vm_true vm_new vm_tmap (extend_map_with ct_old ct_true) ct_false (extend_map_with old_conn_map true_conn_map) old_scope tmap (tmap_true, old_tmap_scope.2))
          with (1 := Hfalse) (2 := H) (3 := H1) (4 := H11) (7 := proj1 (proj2 H5)).
    generalize (stmts_submap vm_tmap ss_false tmap_true old_tmap_scope.2 H11) ; intro.
    destruct (stmts_tmap (tmap_true, old_tmap_scope.2) ss_false vm_tmap) as [[tmap_false scope_false]|] ; last by discriminate H3.
    destruct new_tmap_scope as [new_tmap new_scope].
    injection H3 ; clear H3 ; intros _ H3.
    rewrite -H3 /fst in H4.
    specialize (ExpandBranches_Sem_ct (tmap_false, scope_false) Logic.eq_refl H4).
    destruct (ExpandBranch_funs ss_false true_def_ss (extend_map_with old_conn_map true_conn_map) old_scope) as [[[false_def_ss false_conn_map] _]|] ; last by done.
    destruct H5 as [_ [_ H5]].
    intro.
    rewrite (H5 y) CEP.Lemmas.map2_1bis ; last by rewrite /helper_tf //.
    rewrite CEP.Lemmas.map2_1bis ; last by rewrite /Swhen_map2_helper //.
    assert (CEP.submap tmap_true tmap)
          by (apply (CEP.Lemmas.submap_trans (proj1 (proj2 H12)) H4)).
    specialize (H10 H13).
    assert (CEP.Equal (extend_map_with ct_old ct_true)
                      (extend_map_with old_conn_map true_conn_map))
          by (intro ; specialize (H6 y0) ; specialize (H10 y0) ;
              rewrite /extend_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // H6 H10 //).
    specialize (ExpandBranches_Sem_ct H14).
    rewrite (ExpandBranches_Sem_ct y).
    rewrite (H10 y) /Swhen_map2_helper /helper_tf.
    destruct (CEP.find y true_conn_map) as [[]|] ; destruct (CEP.find y false_conn_map) as [[]|] ; reflexivity.
Qed.*)
Admitted.

Lemma ExpandWhens_correct_inductive :
forall ss : HiFP.hfstmt_seq, Pss ss.
Proof.
apply (Qrcons_ind (Ps := Ps)) ; unfold Ps, Pss ; intros.
* (* Sskip *)
  injection H6 ; clear H6 ; intros H9 H6 _ ; subst eb_conn_map eb_vmscope.
  simpl in H8.
  exact H8.
* (* Swire v ft *)
  (* I need stmt_has_fully_inferred_ground_types s;
     it is not enough that tmap_has_fully_infered_ground_types tmap.
     (Perhaps it is enough to require
      tmap_has_fully_inferred_ground_types old_scope instead). *)
  rewrite /ExpandBranch_fun in H6.
  destruct ft as [gt| |] ; try by discriminate H6.
  rewrite /stmt_tmap /fst in H4.
  destruct (CEP.find v old_tmap) ; first by discriminate H4.
  generalize (fully_inferred_does_not_change gt v sf_vm H2) ;
        intro.
  destruct (code_type_find_vm_widths (Gtyp gt) v sf_vm) as [[[gt'| |] _]|] ;
        last (by discriminate H4) ;
        try (by contradiction H9) ;
        subst gt'.
  injection H4 ; clear H4 ; intros ; subst tm_tmap tm_scope.
  simpl in H6.
  injection H6 ; clear H6 ; intros H6 H9 _ ; subst eb_conn_map eb_vmscope.
  apply Sem_frag_stmts_cat in H8.
  simpl in H8.
  destruct H8 as [sf_vm_comps' [sf_ct_comps' [[sf_vm_comps [sf_ct_comps [H8 [H9 H10]]]] [H11 H12]]]].
  apply Sem_frag_stmt_Equal with (vm_old1 := vm_old) (ct_old1 := ct_old)
                                 (vm_new1 := sf_vm_comps') (ct_new1 := sf_ct_comps') (tmap1 := tmap) ;
        try (by assumption) ;
        try (by apply CEP.Lemmas.Equal_refl).
  apply Sem_frag_stmt_Equal with (vm_old1 := vm_old) (ct_old1 := ct_old)
                                 (vm_new1 := sf_vm_comps) (ct_new1 := sf_ct_comps) (tmap1 := tmap) ;
        try (by apply CEP.Lemmas.Equal_refl) ;
        (by assumption).
* (* Sreg v r *)
  simpl in H2.
  rewrite /stmt_tmap /fst /snd in H4.
  rewrite /ExpandBranch_fun in H6.
  destruct (type r) as [gt| |] ; try by discriminate H2.
  destruct (reset r) as [|rst_sig rst_val] ; last first.
  1-2: destruct (CEP.find v old_tmap) ; first by discriminate H4.
  1-2: destruct (type_of_expr (clock r) old_scope) as [_|] ; last by discriminate H4.
  1-2: destruct (rhs_type_of_expr (clock r) old_vmscope) as [_|] ; last by discriminate H6.
  1-2: move /andP : H2 => [H9 H2].
  1-2: generalize (fully_inferred_does_not_change gt v sf_vm H2) ;
        intro.
  1-2: destruct (code_type_find_vm_widths (Gtyp gt) v sf_vm) as [[[gt'| |] _]|] ;
        last (by discriminate H4) ;
        try (by contradiction H10) ;
        subst gt'.
  move /andP : H9 => [/andP [H9 _] _].
  apply (type_of_expr_and_rhs_type_of_expr rst_sig old_vmscope tmap)
         with (2 := H) in H9.
Check type_of_expr_and_rhs_type_of_expr.

Focus 11.
(* I think we should introduce a naming scheme for variables:
   stmts_tmap output variables begin with tm_
   ExpandBranches_funs output variables begin with eb_
   Sem_frag_stmts “output” variables begin with sf_.
   A variable that reflects the situation after ss ends with _ss.
   A variable that reflects the situation after ss and s ends with _ss_s.
   For ct there is also the variant _compss and _compss_comps, when only the component statements of these have been taken into account. *)
* (* Qrcons *)
  rename sf_vm into sf_vm_ss_s ;
  rename eb_vmscope into eb_vmscope_ss_s ;
  rename sf_ct into sf_ct_ss_s ;
  rename eb_conn_map into eb_conn_map_ss_s ;
  rename tm_tmap into tm_tmap_ss_s ;
  rename tm_scope into tm_scope_ss_s.

  (* First split up Qrcons wherever possible *)
  rewrite -(Qcats0 (Qrcons ss s)) Qcat_rcons stmts_have_fully_inferred_ground_types_cat in H4 ;
  simpl stmts_have_fully_inferred_ground_types in H4.
  rewrite -(Qcats0 (Qrcons ss s)) Qcat_rcons stmts_tmap_cat in H6 ;
  simpl stmts_tmap in H6.
  rewrite -(Qcats0 (Qrcons ss s)) Qcat_rcons ExpandBranches_funs_cat in H8 ;
  simpl ExpandBranches_funs in H8.
  apply Sem_frag_stmts_cat in H10.
  destruct H10 as [sf_vm_ss_s' [sf_ct_compss_comps [H10 H12]]].
  rewrite -(Qcats0 (Qrcons ss s)) Qcat_rcons component_stmts_of_cat Sem_frag_stmts_cat in H10.
  assert (H13: CEP.Equal sf_vm_ss_s' sf_vm_ss_s)
        by admit.
        (* This should be provable because H12 only has connect statements.
           See helper_connect_Sem in the older  file. *)
  destruct H10 as [sf_vm_ss [sf_ct_compss [H10 H11]]].
  simpl component_stmts_of in H11 ; rewrite Qcats0 in H11.
  apply Sem_frag_stmts_Equal
        with (vm_old2 := sf_vm_ss) (ct_old2 := sf_ct_compss)
        (vm_new2 := sf_vm_ss_s) (ct_new2 := sf_ct_compss_comps) (tmap2 := tmap) in H11 ;
        try (by apply CEP.Lemmas.F.Equal_refl) ;
        try (by apply H13).
  apply Sem_frag_stmts_Equal
        with (vm_old2 := sf_vm_ss_s) (ct_old2 := sf_ct_compss_comps)
        (vm_new2 := sf_vm_ss_s) (ct_new2 := sf_ct_ss_s) (tmap2 := tmap) in H12 ;
        try (by apply CEP.Lemmas.F.Equal_refl) ;
        try (by apply H13).
  clear H13 sf_vm_ss_s'.
  rewrite -(Qcats0 (Qrcons ss s)) Qcat_rcons Sem_frag_stmts_cat ;
  simpl Sem_frag_stmts.

  (* submap statements *)
  specialize Sem_frag_stmts_compatible with (1 := H10) ; intro.
  specialize Sem_frag_stmts_compatible with (1 := H11) ; intro.
  specialize Sem_frag_stmts_compatible with (1 := H12) ; intro.

  (* Now our goal is to get the conclusion of H.
     So let's work on its assumptions. *)
  specialize (H vm_old sf_vm_ss old_vmscope) with
             (ct_old := ct_old) (old_tmap := old_tmap)
             (old_scope := old_scope) (tmap := tmap) (old_comp := old_comp)
             (1 := H1) (3 := H3) (4 := proj1 H4) (5 := H5) (9 := H9).
  generalize (ExpandBranch_components ss old_comp (CEP.empty def_expr) old_vmscope) ; intro.
  specialize (ExpandBranch_stmts_tmap sf_vm_ss_s ss old_vmscope)
        with (old_tmap := old_tmap) (old_scope1 := old_scope)
             (old_def_ss := old_comp) (old_conn_map := CEP.empty def_expr)
             (4 := proj1 H4) ;
        intro. (* The preceding assumption is perhaps not needed. *)
(* We will get H : Sem_frag_stmts vm_old ct_old ss sf_vm_ss
      (extend_map_with eb_conn_map_ss sf_ct_compss) tmap later. *)
  specialize (ExpandBranches_Sem_ct ss old_comp vm_old sf_vm_ss sf_vm_ss_s old_vmscope ct_old)
        with (old_conn_map := CEP.empty def_expr) (tmap := tmap) (old_tmap_scope := (old_tmap, old_scope))
             (1 := proj1 H4) (4 := H5) (7 := H9) (8 := H3)
             (10 := (fun k v H => False_ind (PVM.find k ct_old = Some v)
                                            (CEP.empty_1 (CEP.find_2 H)))) ;
        intro.
  destruct (ExpandBranches_funs ss old_comp (CEP.empty def_expr) old_vmscope)
        as [[[eb_comp_ss eb_conn_map_ss] eb_vmscope_ss]|] ;
        last by discriminate H8.
  specialize H16 with (1 := Logic.eq_refl).
  destruct H16 as [H19 H16] ; subst eb_comp_ss.
  specialize (H16 (fun _ H => CEP.empty_1 (CEP.find_2 H))).
  specialize H17 with (2 := Logic.eq_refl).
  specialize H with (sf_ct := extend_map_with eb_conn_map_ss sf_ct_compss) (4 := Logic.eq_refl).

  assert (stmts_tmap (old_tmap, old_scope) ss sf_vm_ss = stmts_tmap (old_tmap, old_scope) ss sf_vm_ss_s) by admit.
  generalize (stmts_submap sf_vm_ss_s ss old_tmap old_scope H5) ; intro.
  destruct (stmts_tmap (old_tmap, old_scope) ss sf_vm_ss_s) as [[tm_tmap_ss tm_scope_ss]|] ;
         last by (discriminate H6).
  specialize H18 with (3 := Logic.eq_refl).
  rewrite H19 in H ; specialize H with (2 := Logic.eq_refl).
  specialize H17 with (1 := Logic.eq_refl).
  (* We will use the following in multiple places: *)
  assert (vm_and_tmap_compatible sf_vm_ss tmap).
        (* This holds because sf_vm_ss is a submap of sf_vm_ss_s. Where do we see this? *)
        intro ; intros ; specialize (H2 k).
        rewrite CEP.Lemmas.map_o /option_map in H2 ;
        rewrite CEP.Lemmas.map_o /option_map in H21.
        destruct H14 as [H14 _] ; specialize (H14 k).
        destruct (PVM.find k sf_vm_ss) ; last by discriminate H21.
        specialize H14 with (1 := Logic.eq_refl) ; rewrite H14 in H2.
        by apply H2, H21.
  (* We have handled most of the side conditions of H.
     Now let's work on the main assumption of H. *)
  assert (Sem_frag_stmts vm_old ct_old
      (Qcat (component_stmts_of ss)
         (convert_to_connect_stmts eb_conn_map_ss)) sf_vm_ss
      (extend_map_with eb_conn_map_ss sf_ct_compss) tmap).
        apply Sem_frag_stmts_cat.
        exists sf_vm_ss, sf_ct_compss.
        split ; first by exact H10.
        apply Sem_frag_stmts_connect.
        * (* map_can_connect tmap eb_conn_map_ss *)
          admit.
        * exact H1.
        * exact H21.
        * (* subdomain eb_conn_map_ss sf_ct_compss *)
          admit.
  specialize H with (1 := H21) (3 := H22).
  (* The remaining side condition can be proven from Lemma stmt_submap,
     after (destruct stmt_tmap s ...).

     So now let's work on the assumptions of H0. *)
  rewrite andbT in H4.
  specialize H0 with (old_comp := (Qcat old_comp (component_stmts_of ss)))
        (old_vmscope := eb_vmscope_ss) (old_tmap := tm_tmap_ss) (old_scope := tm_scope_ss) (sf_vm := sf_vm_ss_s)
        (tmap := tmap) (1 := H1) (2 := H2) (4 := proj2 H4) (5 := proj1 H20).

  assert (match ExpandBranch_fun s (Qcat old_comp (component_stmts_of ss)) (CEP.empty def_expr) eb_vmscope_ss with
          | Some (comp_new, conn_map_new, vmscope_new) =>
              ExpandBranch_fun s (Qcat old_comp (component_stmts_of ss)) eb_conn_map_ss eb_vmscope_ss =
              Some (comp_new, (extend_map_with conn_map_new eb_conn_map_ss), vmscope_new)
          | None =>
              ExpandBranch_fun s (Qcat old_comp (component_stmts_of ss)) eb_conn_map_ss eb_vmscope_ss =
              None
          end) by admit.
  destruct (ExpandBranch_fun s (Qcat old_comp (component_stmts_of ss))
          (CEP.empty def_expr) eb_vmscope_ss) as [[[eb_comp_ss_s eb_conn_map_s] eb_vmscope_ss_s']|] ;
        rewrite H23 // in H8 ; clear H22.
  injection H8 ; clear H8 ; intros ; subst eb_comp_ss_s eb_conn_map_ss_s eb_vmscope_ss_s'.
  rewrite component_stmts_of_cat Qcat_assoc in H0 ; simpl component_stmts_of in H0 ; rewrite Qcats0 in H0.
  specialize H0 with (4 := Logic.eq_refl).

  generalize (stmt_submap sf_vm_ss_s s tm_tmap_ss tm_scope_ss (proj1 H20)) ; intro.
  destruct (stmt_tmap (tm_tmap_ss, tm_scope_ss) s sf_vm_ss_s) as [[tm_tmap_ss_s' tm_scope_ss_s']|] ;
        last by discriminate H6.
  injection H6 ; clear H6 ; intros ; subst tm_tmap_ss_s' tm_scope_ss_s'.
  specialize H0 with (2 := Logic.eq_refl) (3 := H7).

  (* Now we can really use H: *)
  specialize (H (CEP.Lemmas.submap_trans (proj1 (proj2 H8)) H7)).
  exists sf_vm_ss, (extend_map_with eb_conn_map_ss sf_ct_compss).
  split ; first by exact H.
  exists sf_vm_ss_s, sf_ct_ss_s.
  split ; last by split ; apply CEP.Lemmas.Equal_refl.
  (* Now let us use H0: *)
  apply H0.
  - specialize H18 with (3 := (CEP.Lemmas.submap_trans (proj1 (proj2 H8)) H7))
                        (4 := H).
  - destruct H13 as [_ [_ H13]].
    intro.
    specialize (H13 H3 v).
    (* I think I now need a lemma like ExpandBranches_Sem_ct
       to finish this part of the proof. *)

    rewrite /extend_map_with CEP.Lemmas.map2_1bis //.

Focus 9.
* (* Swhen *)
  specialize (Sem_frag_stmts_compatible) with (1 := H10) ; intro.
  assert (vm_and_tmap_compatible old_vmscope tmap).
        intro ; intros ; apply H2.
        rewrite CEP.Lemmas.map_o /option_map in H12.
        specialize (H9 k).
        destruct (CEP.find k old_vmscope) ; last by discriminate H12.
        specialize (H9 _ Logic.eq_refl).
        specialize (proj1 H11 k _ H9) ; intro.
        by rewrite CEP.Lemmas.map_o /option_map H13 //.
  move /andP : H4 => [/andP [H4 H4t] H4f].
  apply (type_of_expr_and_rhs_type_of_expr cond old_vmscope tmap H4 H1)
        in H12.
  destruct (rhs_type_of_expr cond old_vmscope) as [[[[|[|]]| | | | | |] p]|] ;
        try by discriminate H8.
  destruct H12 as [_ H12] ; rewrite H12.
  destruct (type_of_expr cond old_scope) ; last by discriminate H6.
  apply Sem_frag_stmts_cat in H10.
  destruct H10 as [vm_false [ct_false_comp [H10 H13]]].
  apply Sem_frag_stmts_cat in H10.
  destruct H10 as [vm_true [ct_true_comp H10]].
  specialize (Sem_frag_stmts_compatible) with (1 := proj1 H10) ; intro.
  specialize (Sem_frag_stmts_compatible) with (1 := proj2 H10) ; intro.
  specialize (Sem_frag_stmts_compatible) with (1 := H13) ; intro.
  assert (subdomain old_scope vm_true) by admit.
         (* This should hold because proj1 H10 ensures
            that vm_true contains everything needed for sst.
            The subdomain relation is the other way round from
            (vm_and_tmap_compatible old_vmscope old_scope),
            so we cannot just assume that.
            A simple assumption could be (subdomain old_scope vm_old). *)
  apply (stmts_tmap_submap_vm vm_true vm_new sst old_tmap old_scope
              H5 (CEP.Lemmas.submap_trans (proj1 H15) (proj1 H16))) in H17.
  specialize H with (old_tmap := old_tmap) (old_scope := old_scope) (vm_new := vm_true).
  rewrite H17 in H ; clear H17.
  generalize (stmts_submap vm_new sst old_tmap old_scope H5) ; intro.
  specialize (ExpandBranches_funs_preserves_compatibility sst old_tmap old_scope)
        with (vm_tmap := vm_new) (old_comp_ss := old_comp_ss) (old_conn_map := CEP.empty def_expr) (old_vmscope := old_vmscope) (1 := H4t) ; intro.
  destruct (stmts_tmap (old_tmap, old_scope) sst vm_new) as [[tmap_true scope_true]|] ; last by discriminate H6.
  specialize H with (6 := Logic.eq_refl).
  specialize H18 with (4 := Logic.eq_refl).
  assert (subdomain old_scope vm_false) by admit.
  apply (stmts_tmap_submap_vm vm_false vm_new ssf tmap_true old_scope
              (CEP.Lemmas.submap_trans (proj2 (proj2 H17)) (proj1 H17)) (proj1 H16)) in H19.
  specialize H0 with (old_tmap := tmap_true) (old_scope := old_scope) (vm_new := vm_false).
  rewrite H19 in H0 ; clear H19.
  generalize (stmts_submap vm_new ssf tmap_true old_scope (CEP.Lemmas.submap_trans (proj2 (proj2 H17)) (proj1 H17))) ; intro.
  destruct (stmts_tmap (tmap_true, old_scope) ssf vm_new) as [[tmap_false scope_false]|] ; last by discriminate H6.
  specialize H0 with (6 := Logic.eq_refl).
  injection H6 ; clear H6 ; intros ; subst temp_tmap temp_scope.

  specialize H with (old_vmscope := old_vmscope) (old_comp_ss := old_comp_ss).
  generalize (ExpandBranch_components sst old_comp_ss (CEP.empty def_expr) old_vmscope) ; intro.
  destruct (ExpandBranches_funs sst old_comp_ss (CEP.empty def_expr) old_vmscope) as [[[true_comp_ss true_conn_map] true_vmscope]|];
        last by discriminate H8.
  specialize (H6 _ _ _ Logic.eq_refl).
  destruct H6 as [H6 _] ; subst true_comp_ss.
  specialize H with (7 := Logic.eq_refl).
  specialize H18 with (5 := Logic.eq_refl).
  specialize H0 with (old_vmscope := old_vmscope) (old_comp_ss := Qcat old_comp_ss (component_stmts_of sst)).
  generalize (ExpandBranch_components ssf (Qcat old_comp_ss (component_stmts_of sst)) (CEP.empty def_expr) old_vmscope) ; intro.
  destruct (ExpandBranches_funs ssf (Qcat old_comp_ss (component_stmts_of sst)) (CEP.empty def_expr) old_vmscope) as [[[false_comp_ss false_conn_map] false_vmscope]|] ;
        last by discriminate H8.
  specialize (H6 _ _ _ Logic.eq_refl).
  destruct H6 as [H6 _] ; subst false_comp_ss.
  specialize H0 with (7 := Logic.eq_refl).
  rewrite Qcat_assoc in H8.
  injection H8 ; clear H8 ; intros ; subst new_vmscope conn_map.
  assert (vm_and_tmap_compatible vm_true tmap).
        intro.
        specialize (H2 k).
        rewrite CEP.Lemmas.map_o /option_map ; rewrite CEP.Lemmas.map_o /option_map in H2.
        destruct H15 as [H15 _] ; specialize (H15 k).
        destruct H16 as [H16 _] ; specialize (H16 k).
        destruct (PVM.find k vm_true) ; last by done.
        specialize (H15 _ Logic.eq_refl) ; rewrite H15 in H16.
        specialize (H16 _ Logic.eq_refl) ; rewrite H16 // in H2.
  specialize (H vm_old ct_old (extend_map_with true_conn_map ct_true_comp) tmap
                H1 H6 H3 H4t H5
                (CEP.Lemmas.submap_trans (proj1 (proj2 H19)) H7)
                H9).
  assert (Sem_frag_stmts vm_old ct_old
              (Qcat (component_stmts_of sst) (convert_to_connect_stmts true_conn_map))
              vm_true (extend_map_with true_conn_map ct_true_comp) tmap).
        rewrite Sem_frag_stmts_cat.
        exists vm_true, ct_true_comp.
        split ; first by apply H10.
        apply Sem_frag_stmts_connect ; try by assumption.
        + (* use H17? *)



We may need something like:
a connection map generated by ExpandBranches_funs
is a submap of the tmap (or of vmscope, which can then be related to tmap).

ExpandBranches_funs ss ... vmscope = (... conn_map ...)
-> CEP.submap or CEP.subdomain conn_map vmscope

or more directly: (there may be already a similar lemma in the older version of the file)
stmts_tmap ss ... = Some (tmap, _)
-> vm_and_tmap_compatible old_vmscope tmap
-> ExpandBranches_funs ss ... old_vmscope = (... conn_map, new_vmscope)
   -> vm_and_tmap_compatible new_vmscope tmap

(We have as additional assumptions:
    vm_and_tmap_compatible vm_new tmap
    CEP.submap old_vmscope vm_old



(* An older version of the inductive statement, with partial proof. *)

Definition Ps (s : HiFP.hfstmt) : Prop :=
forall (*(pp : seq HiFP.hfport)*)
       (vm_old vm_new (*vm_port*) old_scope scope : CEP.t vertex_type)
       (ct_old ct_new (*port_conn_map*) conn_map : CEP.t def_expr)
       (temp_tmap tmap : CEP.t (ftype * HiF.forient)),
    (*ports_have_fully_inferred_ground_types pp ->*)
    stmt_has_fully_inferred_ground_types s ->
    tmap_has_fully_inferred_ground_types tmap ->
    vm_and_tmap_compatible vm_new tmap ->
    stmt_tmap s vm_new = Some temp_tmap ->
    CEP.submap temp_tmap tmap ->
    (*ports_stmt_tmap pp s vm_new = Some temp_tmap ->
    CEP.submap temp_tmap tmap ->
    ExpandPorts_fun pp = Some (old_scope, port_conn_map) ->*)
    ExpandBranch_fun s (Qnil ProdVarOrder.T) (CEP.empty def_expr) old_scope = Some (component_stmt_of s, conn_map, scope) ->
    vm_and_ct_compatible vm_old ct_old ->
    CEP.submap old_scope vm_old ->
    Sem_frag_stmts vm_old ct_old (Qcat (component_stmt_of s)
                                       (convert_to_connect_stmts conn_map))
                   vm_new ct_new tmap ->
    Sem_frag_stmt vm_old ct_old s vm_new ct_new tmap.

Definition Pss (ss : HiFP.hfstmt_seq) : Prop :=
forall (pp : seq HiFP.hfport)
       (vm_old vm_new vm_port old_scope scope : CEP.t vertex_type)
       (ct_old ct_new port_conn_map conn_map : CEP.t def_expr)
       (temp_tmap tmap : CEP.t (ftype * HiF.forient)),
    ports_have_fully_inferred_ground_types pp ->
    stmts_have_fully_inferred_ground_types ss ->
    tmap_has_fully_inferred_ground_types tmap ->
    ports_stmts_tmap pp ss vm_port = Some temp_tmap ->
    CEP.submap temp_tmap tmap ->
    ExpandPorts_fun pp = Some (old_scope, port_conn_map) ->
    ExpandBranches_funs ss (Qnil ProdVarOrder.T) (CEP.empty def_expr) old_scope = Some (component_stmts_of ss, conn_map, scope) ->
    vm_and_ct_compatible vm_old ct_old ->
    CEP.submap old_scope vm_old ->
    Sem_frag_stmts vm_old ct_old (Qcat (component_stmts_of ss)
                                       (convert_to_connect_stmts conn_map))
                   vm_new ct_new tmap ->
    Sem_frag_stmts vm_old ct_old ss vm_new ct_new tmap.

Lemma ExpandWhens_correct_inductive :
forall ss : HiFP.hfstmt_seq, Pss ss.
Proof.
apply (Qrcons_ind (Ps := Ps)) ; unfold Ps, Pss ; simpl ; intros.
* (* Sskip *)
  injection H5 ; clear H5 ; intros _ H5 ; subst conn_map.
  unfold convert_to_connect_stmts in H8.
  rewrite CEP.Lemmas.P.fold_Empty in H8 ;
        last by apply CEP.empty_1.
  simpl Sem_frag_stmts in H8.
  by exact H8.
* (* Swire *)
  destruct ft as [gt| |] ; try by discriminate H0.
  injection H5 ; clear H5 ; intros _ H5 ; subst conn_map.
  destruct H8 as [vm' [ct' [H8 H9]]].
  unfold convert_to_connect_stmts in H9.
  rewrite CEP.Lemmas.P.fold_Empty in H9 ;
        last by apply CEP.empty_1.
  simpl Sem_frag_stmts in H9.
  destruct H9 as [H9 H10].
  (* Now basically H6 is the same as the goal,
     just vm' is replaced by vm_new and ct' is replaced by ct_new.
     We have to destruct the expressions to bring them together. *)
  destruct (CEP.find v tmap) as [[newft _]|] ; last by contradiction H8.
  split.
  + destruct H8 as [H8 _].
    intro ; specialize (H8 n).
    destruct (List.nth_error (list_rhs_type_p newft) n) as [gt0|] ; last by trivial.
    rewrite H9 // in H8.
  destruct H8 as [_ H8] ; split.
  + destruct H8 as [H8 _].
    intros v0 n0 ; specialize (H8 v0 n0).
    rewrite H9 // in H8.
  destruct H8 as [_ H8] ; split.
  + destruct H8 as [H8 _].
    intros v0 n0 ; specialize (H8 v0 n0).
    rewrite H10 // in H8.
  + destruct H8 as [_ H8].
    intro n0 ; specialize (H8 n0).
    rewrite H10 // in H8.
* (* Sreg *)
  admit.
(*unfold ports_stmt_tmap in H1.
  (*specialize (ports_tmap_and_ExpandPorts_fun pp old_scope vm_port port_conn_map)
              with (1 := H) (2 := H3) ; intro H7.*)
  destruct (ports_tmap pp vm_port) as [pmap|] ; last by discriminate H1.
  (*specialize (H7 pmap Logic.eq_refl).*)
  simpl stmt_tmap in H1.
  destruct (CEP.find v pmap) ; first by discriminate H1.
  destruct (type_of_expr (clock r) pmap) ; last by discriminate H1.
  destruct (type r) as [gt| |] ; try by discriminate H0.
  destruct (rhs_type_of_expr (clock r) old_scope) ; last by discriminate H4.
  destruct (reset r) as [|rst_sig rst_val].
  1-2: move /andP : H0 => H0.
  1-2: generalize (fully_inferred_does_not_change gt v vm_port (proj2 H0)) ; intro.
  1-2: destruct (code_type_find_vm_widths (Gtyp gt) v vm_port) as [[[gt'| |] _]|] ;
             last (by discriminate H1) ;
             try (by contradiction H6) ;
             subst gt'.
  2:   destruct (rhs_type_of_expr rst_sig old_scope) as [[[[|[|]]| | | | | |] _]|] ; try by discriminate H4.
  2-3: destruct (rhs_type_of_expr rst_val old_scope) ; last by discriminate H4.
  1-3: injection H4 ; clear H4 ; intros _ H4 ; subst conn_map.
  1-3: destruct H5 as [vm' [ct' [H5 H6]]].
  1-3: unfold convert_to_connect_stmts in H6.
  1-3: rewrite CEP.Lemmas.P.fold_Empty in H6 ;
             last by apply CEP.empty_1.
  1-3: simpl Sem_frag_stmts in H6.
  1-3: destruct H6 as [H6 H7].
  1-3: destruct (CEP.find v tmap) as [[newft _]|] ; last by contradiction H5.
  (* same as with Swire: H5 is the pattern...
     However, if the register has a reset, there is an additional check. *)
  1-3: split.
Focus 3.

destruct (ports_tmap pp vm_port) as [pmap|] ; last by discriminate H1.
simpl stmt_tmap in H1.
destruct (CEP.find v pmap) 

  - 1: apply H5.*)
* (* Smem *)
  discriminate H5.
* (* Sinst *)
  discriminate H5.
* (* Snode *)
  admit.
* (* Sfcnct *)
  assert (ct_has_fully_inferred_ground_types (CEP.empty def_expr))
        by (intro ; rewrite CEP.Lemmas.F.empty_o //).
  apply (ExpandBranch_fun_preserves_fully_inferred (Sfcnct r e) (Qnil ProdVarOrder.T) (CEP.empty def_expr) old_scope
              H0) in H9.
  simpl ExpandBranch_fun in H9.
  rewrite H5 in H9.
  destruct r as [var| | |] ; try by discriminate H5.
  move /andP : H0 => [_ H0].
  unfold ports_stmt_tmap in H2 ; simpl stmt_tmap in H2.
  specialize (ports_tmap_and_ExpandPorts_fun pp old_scope vm_port port_conn_map)
             with (1 := H) (2 := H4) ; intro.
  generalize (ports_tmap_preserves_fully_inferred vm_port pp H) ; intro.
  destruct (ports_tmap pp vm_port) as [pmap|] ; last by discriminate H2.
  specialize (H10 pmap Logic.eq_refl).
  destruct H10 as [H10 [H12 H13]].
  specialize (convert_to_connect_stmts_Sem conn_map vm_old ct_old vm_new ct_new tmap
              H1 H9 H8) ; intro.
  assert (CEP.submap (CEP.map (fun v : vertex_type
                               => match v with
                                  | OutPort gt => (Gtyp gt, HiF.Sink)
                                  | Register gt _ _ _ | Wire gt => (Gtyp gt, HiF.Duplex)
                                  | InPort gt | Node gt => (Gtyp gt, HiF.Source)
                                  end) old_scope) pmap)
        by (intro ; intros ; rewrite -H12 ; destruct (var == k) eqn: Hkvar ;
            first (by rewrite CEP.Lemmas.map_o CEP.Lemmas.remove_eq_o // in H15) ;
            by rewrite -H15 CEP.Lemmas.map_o CEP.Lemmas.map_o CEP.Lemmas.remove_neq_o // /PVM.SE.eq Hkvar //).
  apply (type_of_expr_and_rhs_type_of_expr e old_scope pmap
              H0 H11) in H15.
  assert (CEP.submap (CEP.map (fun v : vertex_type
                               => match v with
                                  | OutPort gt => (Gtyp gt, HiF.Sink)
                                  | Register gt _ _ _ | Wire gt => (Gtyp gt, HiF.Duplex)
                                  | InPort gt | Node gt => (Gtyp gt, HiF.Source)
                                  end) old_scope) pmap)
        by (intro ; specialize (H12 k) ; destruct (var == k) eqn: Hvark ;
            first (by rewrite CEP.Lemmas.map_o CEP.Lemmas.remove_eq_o //) ;
            rewrite CEP.Lemmas.remove_neq_o ; last (by rewrite /PVM.SE.eq Hvark //) ;
            rewrite CEP.Lemmas.map_o CEP.Lemmas.remove_neq_o ; last (by rewrite /PVM.SE.eq Hvark //) ;
            rewrite -H12 CEP.Lemmas.map_o //).
  assert (tmap_has_fully_inferred_ground_types pmap)
        by (intro ; specialize (H11 v) ; destruct (var == v) eqn: Hvarv ;
            first (by rewrite CEP.Lemmas.remove_eq_o //) ;
            rewrite CEP.Lemmas.remove_neq_o // /PVM.SE.eq Hvarv //).
  apply (type_of_expr_and_rhs_type_of_expr e old_scope pmap
              H0 H17) in H16.
  specialize (H11 var).
  specialize (H12 var).
  rewrite CEP.Lemmas.map_o /option_map in H12.
  destruct (rhs_type_of_expr e old_scope) as [[gt_src psrc]|] ;
        last by destruct (CEP.find var old_scope) as [[]|] ; discriminate H5.
  rewrite (proj2 H15) in H2.
  specialize (H7 var).
  destruct (CEP.find var old_scope) as [[gt_tgt|gt_tgt|gt_tgt|gt_tgt|gt_tgt]|] ;
       try by discriminate H5.
  1-3: rewrite -H12 in H2, H11.
  1-3: injection H2 ; clear H2 ; intro ; subst temp_tmap.
  1-3: assert (CEP.submap pmap tmap)
             by (intro ; specialize (H3 k) ; destruct (var == k) eqn: Hvark ;
                 first (by rewrite CEP.Lemmas.remove_eq_o //) ;
                 rewrite CEP.Lemmas.remove_neq_o // ; last (by rewrite /PVM.SE.eq Hvark //) ;
                 rewrite CEP.Lemmas.remove_neq_o // /PVM.SE.eq Hvark //).
  (*1-3: assert (CEP.submap (CEP.remove var pmap) tmap)
          by (intro ; specialize (H3 k) ; destruct (var == k) eqn: Hvark ;
              first (by rewrite CEP.Lemmas.remove_eq_o //) ;
              by rewrite CEP.Lemmas.remove_neq_o // /PVM.SE.eq Hvark //).*)
  1-3: apply (type_of_expr_submap e pmap tmap) in H2.
  1-3: rewrite (proj2 H16) in H2.
  1-3: specialize (H3 var) ; rewrite -H12 in H3 ; specialize (H3 _ Logic.eq_refl).
  1-3: simpl list_lhs_ref_p ; rewrite H3 /size_of_ftype.
  1-3: rewrite /mkseq ; simpl map ; simpl foldr ; rewrite N.add_0_r -surjective_pairing H2.
  1-3: destruct gt_tgt, gt_src ;
        try (by discriminate H5) ;
        try (by discriminate H11) ;
        try (by discriminate (proj1 H15)).
  1-12: injection H5 ; clear H5 ; intros ; subst conn_map scope.
  1-12: destruct e ; split ; try (by apply H14) ; destruct H14 as [_ H14].
  - (* Econst *)
    1,8,15,22,29,36,43,50,57,64,71,78: split ; first by done.
    1-12: simpl.
    1-12: split ;
                first by (intro n1 ;
                          destruct n1 as [|[|]] ; simpl ; try (by trivial) ;
                          split ; last (by rewrite H14 /extend_defined_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.find_add_eq // /PVM.SE.eq //) ;
                          specialize (H6 var) ; specialize (H7 _ Logic.eq_refl) ;
                          rewrite H7 // in H6).
    1-12: intro v0 ; rewrite mem_seq1.
    1-12: destruct (v0 == var) eqn: Hv0v ; first by trivial.
    1-12: rewrite H14 /extend_defined_map_with CEP.Lemmas.map2_1bis //
                  (CEP.Lemmas.find_add_neq (elimT negP (negbT Hv0v)))
                  CEP.Lemmas.empty_o //.
  - (* Ecast *)
    1,7,13,19,25,31,37,43,49,55,61,67: split ; first by done.
    1-12: simpl.
    1-12: split ;
                first by (intro n1 ;
                          destruct n1 as [|[|]] ; simpl ; try (by trivial) ;
                          split ; last (by rewrite H14 /extend_defined_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.find_add_eq // /PVM.SE.eq //) ;
                          specialize (H6 var) ; specialize (H7 _ Logic.eq_refl) ;
                          rewrite H7 // in H6).
    1-12: intro v0 ; rewrite mem_seq1.
    1-12: destruct (v0 == var) eqn: Hv0v ; first by trivial.
    1-12: rewrite H14 /extend_defined_map_with CEP.Lemmas.map2_1bis //
                  (CEP.Lemmas.find_add_neq (elimT negP (negbT Hv0v)))
                  CEP.Lemmas.empty_o //.
  - (* Eprim_unop *)
    1,6,11,16,21,26,31,36,41,46,51,56: split ; first by done.
    1-12: simpl.
    1-12: split ;
                first by (intro n1 ;
                          destruct n1 as [|[|]] ; simpl ; try (by trivial) ;
                          split ; last (by rewrite H14 /extend_defined_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.find_add_eq // /PVM.SE.eq //) ;
                          specialize (H6 var) ; specialize (H7 _ Logic.eq_refl) ;
                          rewrite H7 // in H6).
    1-12: intro v0 ; rewrite mem_seq1.
    1-12: destruct (v0 == var) eqn: Hv0v ; first by trivial.
    1-12: rewrite H14 /extend_defined_map_with CEP.Lemmas.map2_1bis //
                  (CEP.Lemmas.find_add_neq (elimT negP (negbT Hv0v)))
                  CEP.Lemmas.empty_o //.
  - (* Eprim_binop *)
    1,5,9,13,17,21,25,29,33,37,41,45: split ; first by done.
    1-12: simpl.
    1-12: split ;
                first by (intro n1 ;
                          destruct n1 as [|[|]] ; simpl ; try (by trivial) ;
                          split ; last (by rewrite H14 /extend_defined_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.find_add_eq // /PVM.SE.eq //) ;
                          specialize (H6 var) ; specialize (H7 _ Logic.eq_refl) ;
                          rewrite H7 // in H6).
    1-12: intro v0 ; rewrite mem_seq1.
    1-12: destruct (v0 == var) eqn: Hv0v ; first by trivial.
    1-12: rewrite H14 /extend_defined_map_with CEP.Lemmas.map2_1bis //
                  (CEP.Lemmas.find_add_neq (elimT negP (negbT Hv0v)))
                  CEP.Lemmas.empty_o //.
  - (* Emux *)
    1,4,7,10,13,16,19,22,25,28,31,34: split ; first by done.
    1-12: simpl.
    1-12: split ;
                first by (intro n1 ;
                          destruct n1 as [|[|]] ; simpl ; try (by trivial) ;
                          split ; last (by rewrite H14 /extend_defined_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.find_add_eq // /PVM.SE.eq //) ;
                          specialize (H6 var) ; specialize (H7 _ Logic.eq_refl) ;
                          rewrite H7 // in H6).
    1-12: intro v0 ; rewrite mem_seq1.
    1-12: destruct (v0 == var) eqn: Hv0v ; first by trivial.
    1-12: rewrite H14 /extend_defined_map_with CEP.Lemmas.map2_1bis //
                  (CEP.Lemmas.find_add_neq (elimT negP (negbT Hv0v)))
                  CEP.Lemmas.empty_o //.
  - (* Evalidif *)
    1,3,5,7,9,11,13,15,17,19,21,23: split ; first by done.
    1-12: simpl.
    1-12: split ;
                first by (intro n1 ;
                          destruct n1 as [|[|]] ; simpl ; try (by trivial) ;
                          split ; last (by rewrite H14 /extend_defined_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.find_add_eq // /PVM.SE.eq //) ;
                          specialize (H6 var) ; specialize (H7 _ Logic.eq_refl) ;
                          rewrite H7 // in H6).
    1-12: intro v0 ; rewrite mem_seq1.
    1-12: destruct (v0 == var) eqn: Hv0v ; first by trivial.
    1-12: rewrite H14 /extend_defined_map_with CEP.Lemmas.map2_1bis //
                  (CEP.Lemmas.find_add_neq (elimT negP (negbT Hv0v)))
                  CEP.Lemmas.empty_o //.
  - (* Eref *)
    1-4,9-12: rename h into h0.
    1-12: generalize (list_lhs_ref_p_type tmap h0) ; intro.
    1-12: generalize (list_lhs_ref_p_size tmap h0) ; intro.
    1-12: simpl in H2.
    1-12: assert (match list_lhs_ref_p h0 tmap with
                    | Some (lst_src, (_, _)) => var \notin lst_src
                    | None => true
                    end).
            1,3,5,7,9,11,13,15,17,19,21,23: clear -H1.
            1-12: induction h0 ; simpl ; try done.
            + (* Eid *)
              1,4,7,10,13,16,19,22,25,28,31,34:
                   destruct (CEP.find s tmap) as [[ft ori]|] eqn: Hfind ;
                         try (by trivial).
              1-12: destruct (var == s) eqn: Hvars ; first (by rewrite CEP.Lemmas.remove_eq_o // in Hfind).
              1-12: rewrite CEP.Lemmas.remove_neq_o in Hfind ; last by rewrite /PVM.SE.eq Hvars //.
              1-12: specialize (H1 s) ; rewrite Hfind in H1.
              1-12: destruct ft as [gt| |] ; try by contradiction H1.
              1-12: unfold mkseq ; simpl map ; rewrite N.add_0_r -surjective_pairing mem_seq1.
              1-12: apply negbT ; exact Hvars.
            + (* Esubfield *)
              1,3,5,7,9,11,13,15,17,19,21,23:
                    destruct (list_lhs_ref_p h0 tmap) as [[lst_src [[| |] ori_src]]|] ;
                          try by trivial.
              1-12: revert lst_src IHh0.
              1-12: induction f ; simpl ; try done.
              1-12: intros.
              1-12: destruct (size lst_src < size_of_ftype f0) ; first by done.
              1-12: destruct (v != v0) eqn: Hvv0 ; rewrite Hvv0 ;
                          first (by apply IHf, (introT negP) ; contradict IHh0 ;
                                    rewrite (mem_drop IHh0) //).
              1-12: destruct f, ori_src ; try (by trivial) ;
                    apply (introT negP) ; contradict IHh0 ;
                    rewrite (mem_take IHh0) //.
            + (* Esubindex *)
              1-12: destruct (list_lhs_ref_p h0 tmap) as [[lst_src [[| |] ori_src]]|] ; try by trivial.
              1-12: destruct ((n < n0) && (size lst_src == n0 * size_of_ftype f)) ; last by trivial.
              1-12: apply (introT negP) ; contradict IHh0.
              1-12: apply (mem_take (s := drop (n * size_of_ftype f) lst_src)), mem_drop in IHh0.
              1-12: rewrite IHh0 //.
    1-12: destruct (type_of_ref h0 tmap) as [[type_ft [| | | |]]|] ;
                try by discriminate H2.
    1-24: destruct (list_lhs_ref_p h0 tmap) as [[lst_src [ft_src ori_src]]|] eqn: Hlist ;
                last by contradiction H5.
    1-24: injection H5 ; clear H5 ; intros ; subst type_ft ori_src.
    1-24: destruct ft_src as [[| | | | | |]| |] ; 
          simpl make_ftype_explicit in H2;
          try (by discriminate H2) ;
          try (by destruct (make_ftype_explicit ft_src) ;
                  discriminate H2) ;
          try (by destruct (make_ffield_explicit f) ;
                  discriminate H2).
    1-8,13-20,25-32: injection H2 ; intro ; subst n1.
    1-36: clear H2 ; split ; first by reflexivity.
    1-36: destruct lst_src as [|] ; simpl in H18 ; try by discriminate H18.
    1-36: injection H18 ; clear H18 ; intro H18 ; apply size0nil in H18 ; subst lst_src.
    1-36: split.
    -  1, 3, 5, 7, 9,11,13,15,17,19,21,23,25,27,29,31,33,35,
      37,39,41,43,45,47,49,51,53,55,57,59,61,63,65,67,69,71:
            simpl ; specialize (H6 var).
      1-36: specialize (H7 _ Logic.eq_refl).
      1-36: rewrite H7 in H6.
      1-36: move /eqP : H6 => H6.
      1-36: rewrite H6 andTb.
      1-36: rewrite (H14 var) /extend_defined_map_with CEP.Lemmas.map2_1bis //
                    (CEP.Lemmas.find_add_eq (eq_refl var)) eq_refl andTb.
      1-36: rewrite mem_seq1 eq_sym in H19 ; move /negP : H19 => H19.
      1-36: by rewrite (H14 k) /extend_defined_map_with CEP.Lemmas.map2_1bis //
                       (CEP.Lemmas.find_add_neq H19) CEP.Lemmas.empty_o //.
    - 1-36: intro.
      1-36: rewrite mem_seq1 mem_seq1.
      1-36: destruct ((v0 == var) || (v0 == k)) eqn: Hv0var ; first by trivial.
      1-36: apply negbT in Hv0var.
      1-36: rewrite negb_or in Hv0var.
      1-36: move /andP : Hv0var => [/negP Hv0var _].
      1-36: rewrite H14 /extend_defined_map_with CEP.Lemmas.map2_1bis //
                    (CEP.Lemmas.find_add_neq Hv0var) CEP.Lemmas.empty_o //.
* (* Sinvalid *)
  assert (ct_has_fully_inferred_ground_types (CEP.empty def_expr))
        by (intro ; rewrite CEP.Lemmas.F.empty_o //).
  apply (ExpandBranch_fun_preserves_fully_inferred (Sinvalid r) (Qnil ProdVarOrder.T) (CEP.empty def_expr) old_scope
              H0) in H9.
  simpl ExpandBranch_fun in H9.
  rewrite H5 in H9.
  destruct r as [var| | |] ; try by discriminate H5.
  unfold ports_stmt_tmap in H2 ; simpl stmt_tmap in H2.
  specialize (ports_tmap_and_ExpandPorts_fun pp old_scope vm_port port_conn_map)
             with (1 := H) (2 := H4) ; intro.
  destruct (ports_tmap pp vm_port) as [pmap|] ; last by discriminate H2.
  specialize (H10 pmap Logic.eq_refl).
  destruct H10 as [_ [H12 _]].
  specialize (convert_to_connect_stmts_Sem conn_map vm_old ct_old vm_new ct_new tmap
              H1 H9 H8) ; intro H14.
  specialize (H12 var).
  rewrite CEP.Lemmas.map_o /option_map in H12.
  specialize (H7 var).
  destruct (CEP.find var old_scope) as [[gt_tgt|gt_tgt|gt_tgt|gt_tgt|gt_tgt]|] ;
       try by discriminate H5.
  1-3: injection H5 ; clear H5 ; intros ; subst conn_map scope.
  1-3: rewrite -H12 in H2.
  1-3: injection H2 ; clear H2 ; intro ; subst temp_tmap.
  1-3: specialize (H3 var) ; rewrite -H12 in H3 ; specialize (H3 _ Logic.eq_refl).
  1-3: simpl list_lhs_ref_p ; rewrite H3 /size_of_ftype.
  1-3: rewrite /mkseq ; simpl map ; rewrite N.add_0_r -surjective_pairing.
  1-3: split ; first (by apply H14) ; destruct H14 as [_ H14].
  1-3: split ;
             first by (intro n1 ;
                       destruct n1 as [|[|]] ; simpl ; try (by trivial) ;
                       split ; last (by rewrite H14 /extend_defined_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.find_add_eq // /PVM.SE.eq //) ;
                       specialize (H6 var) ; specialize (H7 _ Logic.eq_refl) ;
                       rewrite H7 // in H6).
  1-3: intro v0 ; rewrite mem_seq1.
  1-3: destruct (v0 == var) eqn: Hv0v ; first by trivial.
  1-3: by rewrite H14 /extend_defined_map_with CEP.Lemmas.map2_1bis //
                  (CEP.Lemmas.find_add_neq (elimT negP (negbT Hv0v)))
                  CEP.Lemmas.empty_o //.
* (* Swhen *)
  unfold ports_stmt_tmap in H4.
  specialize (ports_tmap_and_ExpandPorts_fun pp old_scope vm_port port_conn_map)
             with (1 := H1) (2 := H6) ; intro.
  destruct (ports_tmap pp vm_port) as [pmap|] ; last by discriminate H4.
  specialize (H11 pmap Logic.eq_refl).
  move /andP : H2 => [/andP [H12 H2t] H2f].
  apply (type_of_expr_and_rhs_type_of_expr cond old_scope tmap)
        with (2 := H3) in H12.
  destruct (rhs_type_of_expr cond old_scope) as [[[[|[|]]| | | | | |] p]|] ;
        try by discriminate H7.
  destruct H12 as [_ H12] ; rewrite H12.
  admit.
* (* Qnil *)
  injection H5 ; clear H5 ; intros ; subst conn_map scope.
  simpl in H8.
  exact H8.
* (* Qcons *)
  (* Here we'll see that Ps is not sufficient,
     but we should allow some old_conn_map and possibly others as well... *)
  admit.
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
rewrite stmts_tmap_cat in H0.
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


