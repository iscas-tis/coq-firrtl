From Coq Require Import BinNat ZArith Lia.
From mathcomp Require Import ssreflect ssrbool eqtype seq fintype ssrnat div ssrfun.
From simplssrlib Require Import SsrOrder Var FMaps.
From firrtl Require Import Firrtl Env HiEnv HiFirrtl.

Section ExpandWhens.

  (* a type to indicate connects *)
Inductive def_expr : Type :=
  | D_undefined (* declared but not connected, no "is invalid" statement *)
  | D_invalidated (* declared but not connected, there is a "is invalid" statement *)
  | D_fexpr : HiFP.hfexpr -> def_expr (* declared and connected *)
  .

(* equality of def_expr is decidable [because equality of hfexpr is decidable] *)
Lemma def_expr_eq_dec : forall {x y : def_expr}, {x = y} + {x <> y}.
  Proof.
  decide equality.
  apply hfexpr_eq_dec.
Qed.

Definition def_expr_eqn (x y : def_expr) : bool :=
  match x, y with
  | D_undefined, D_undefined => true
  | D_invalidated, D_invalidated => true
  | D_fexpr expr1, D_fexpr expr2 => expr1 == expr2
  | _, _ => false
  end.

Lemma def_expr_eqP : Equality.axiom def_expr_eqn.
Proof.
  unfold Equality.axiom, def_expr_eqn.
  intros ; induction x, y ; try (apply ReflectF ; discriminate) ; try (apply ReflectT ; reflexivity).
  case Eq: (h == h0).
  all: move /hfexpr_eqP : Eq => Eq.
  apply ReflectT ; replace h0 with h ; reflexivity.
  apply ReflectF ; injection ; apply Eq.
Qed.

Canonical def_expr_eqMixin := EqMixin def_expr_eqP.
Canonical def_expr_eqType := Eval hnf in EqType def_expr def_expr_eqMixin.

Definition helper_tf (c : HiFP.hfexpr) (true_expr : option def_expr) (false_expr : option def_expr) : option def_expr := (* ? *)
  match true_expr, false_expr with
  | None, None => None
  | Some (D_fexpr t), Some (D_fexpr f) => (*if t == f then true_expr 
                                      else*) Some (D_fexpr (Emux c t f)) 
  | Some D_invalidated, Some (D_fexpr f) => false_expr
  | Some (D_fexpr t), Some D_invalidated => true_expr
  | _,_ => true_expr (* impossible? *)
  end.

(*Definition combine_branches (c : HiFP.hfexpr) (true_branch : (HiFP.hfstmt_seq * CEP.t def_expr)) (false_branch: (HiFP.hfstmt_seq * CEP.t def_expr)) : (HiFP.hfstmt_seq * CEP.t def_expr) :=
  let combined_cm := CEP.map2 (helper_tf c) (snd true_branch) (snd false_branch) (* CE.map2 for what? *)
   in (Qcat (fst true_branch) (fst false_branch), combined_cm). (* 直接Qcat？如果有重复定义 *)

Definition init_ref (r : pvar) (type : ftype) (cm : CEP.t def_expr) : CEP.t def_expr :=
  match type with
  | Gtyp _ => CEP.add r D_undefined cm
  | _ => cm (* should be changed in expand connects *)
  end.

Definition init_register (r : pvar) (type : ftype) (cm : CEP.t def_expr) : CEP.t def_expr :=
   match type with
   | Gtyp _ => CEP.add r (D_fexpr (Eref (Eid r))) cm
   | _ => cm
   end.

Definition init_inv (r : pvar) (cm : CEP.t def_expr) : CEP.t def_expr :=
  CEP.add r D_invalidated cm.

Definition init_inst (r : pvar) (mv: pvar) (ce_other_modules : CEP.env) (cm : CEP.t def_expr) : CEP.t def_expr :=
   match CEP.find mv ce_other_modules with
   | Some (HiFP.aggr_typ t, Instanceof) => init_ref r t cm
   (* CEP.find v1 ce' = Some (fst (CEP.vtyp v2 ce), Instanceof) -> *)
   | _ => cm (* wrong initialization *)
   end.

   old version

 Fixpoint expandBranch_fun (ss : HiFP.hfstmt_seq) (ce_other_modules : CEP.env) (hseq_result : HiFP.hfstmt_seq) (cm_result : CEP.t def_expr) : (HiFP.hfstmt_seq * CEP.t def_expr) :=
  (* ss : statement seq going to be expanded 
     ce_other_modules : type information for ports of other modules, used in inst case
     hseq_result : declaration statement in ss, including those in branches
     cm_result : rhs expr map for every var that is connected to, also solving last connecting*)
  match ss with
  | Qnil => (hseq_result, cm_result)
  | Qcons s st => let (new_hseq, new_cm) := 
    match s with
    | Sskip => (hseq_result, cm_result) (* no translation needed *)
    | Swire v type => let cm_wire := init_ref v type cm_result
                      in (Qcons s hseq_result, cm_wire)
    | Sreg v r => let cm_reg := init_register v (type r) cm_result
                  in (Qcons s hseq_result, cm_reg)
    | Smem v m => let cm_mem := cm_result
                  in (Qcons s hseq_result, cm_mem) (* TBD *)
    | Sinvalid (Eid r) => let cm_inv := init_inv r cm_result
                    in (hseq_result, cm_inv)
    | Sinst v v0 => let cm_inst := cm_result 
                    in (Qcons s hseq_result, cm_inst) (* TBD *)
    | Snode v e => (Qcons s hseq_result, cm_result)
    | Sfcnct (Eid r) e2 => let cm_cnct := CEP.add r (D_fexpr e2) cm_result
                            in (hseq_result, cm_cnct)
    | Swhen c s1 s2 => let cm_true := expandBranch_fun s1 ce_other_modules hseq_result cm_result in
                       let cm_false := expandBranch_fun s2 ce_other_modules (Qnil ProdVarOrder.T) cm_result in
                       combine_branches c cm_true cm_false
    | _ => (hseq_result, cm_result) (* subindex subaccess subfield don't exist *)
    end in expandBranch_fun st ce_other_modules new_hseq new_cm
  end.*)

Fixpoint expandBranch_fun (s : HiFP.hfstmt) (hseq_result : option HiFP.hfstmt_seq) (cm_result : CEP.t def_expr) : (option HiFP.hfstmt_seq * CEP.t def_expr) :=
  (* ss : statement seq going to be expanded 
     ce_other_modules : type information for ports of other modules, used in inst case
     hseq_result : declaration statement in ss, including those in branches
     cm_result : rhs expr map for every var that is connected to, also solving last connecting*)
  match s with
  | Sskip => (hseq_result, cm_result)
  | Swire v type => let new_seq := match hseq_result with
                    | None => None
                    | Some hseq_result => if (Qin s hseq_result) then None else Some (Qcons s hseq_result)
                    end in
                    let cm_wire := CEP.add v D_undefined cm_result
                    in (new_seq, cm_wire)
  | Sreg v r => let new_seq := match hseq_result with
                | None => None
                | Some hseq_result => if (Qin s hseq_result) then None else Some (Qcons s hseq_result)
                end in
                let cm_reg := CEP.add v (D_fexpr (Eref (Eid v))) cm_result
                in (new_seq, cm_reg)
  | Smem v m => let new_seq := match hseq_result with
                | None => None
                | Some hseq_result => if (Qin s hseq_result) then None else Some (Qcons s hseq_result)
                end in
                let cm_mem := CEP.add v D_undefined cm_result
                in (new_seq, cm_mem) (* TBD *)
  | Sinvalid (Eid r) => let cm_inv := CEP.add r D_invalidated cm_result
                        in (hseq_result, cm_inv)
  | Sinst v v0 => let new_seq := match hseq_result with
                  | None => None
                  | Some hseq_result => if (Qin s hseq_result) then None else Some (Qcons s hseq_result)
                  end in
                  let cm_inst := CEP.add v D_undefined cm_result
                  in (new_seq, cm_inst) (* TBD *)
  | Snode v e => let new_seq := match hseq_result with
                | None => None
                | Some hseq_result => if (Qin s hseq_result) then None else Some (Qcons s hseq_result)
                end in (new_seq, cm_result)
  | Sfcnct (Eid r) e2 => let cm_cnct := CEP.add r (D_fexpr e2) cm_result
                          in (hseq_result, cm_cnct)
  | Swhen c s1 s2 => (*let (new_seq0, cm_true) := expandBranch_funs s1 hseq_result cm_result in*)
                     (*let (new_seq, cm_false) := expandBranch_funs s2 (fst (expandBranch_funs s1 hseq_result cm_result)) cm_result in*)
                     ((fst (expandBranch_funs s2 (fst (expandBranch_funs s1 hseq_result cm_result)) cm_result)),
                      CEP.map2 (helper_tf c) (snd (expandBranch_funs s1 hseq_result cm_result)) (snd (expandBranch_funs s2 (fst (expandBranch_funs s1 hseq_result cm_result)) cm_result)))
  | _ => (hseq_result, cm_result) 
  end
with expandBranch_funs (ss : HiFP.hfstmt_seq) (hseq_result : option HiFP.hfstmt_seq) (cm_result : CEP.t def_expr) : (option HiFP.hfstmt_seq * CEP.t def_expr) :=
  match ss with
  | Qnil => (hseq_result, cm_result)
  | Qcons s stl => (*let (new_hseq, new_cm) := expandBranch_fun s hseq_result cm_result in *)
                   expandBranch_funs stl (fst (expandBranch_fun s hseq_result cm_result)) (snd (expandBranch_fun s hseq_result cm_result))
  end.

Definition unfold_cm (cml : seq (pvar * def_expr)) sts := 
  match cml with 
  | nil => sts
  | e :: es => match e with
              | (v, D_fexpr tempe) => Qcons (Sfcnct (Eid v) tempe) sts
              | (v, D_invalidated) => Qcons (Sinvalid (Eid v)) sts
              | _ => sts (* D_undefined 未被连接error *)
              end
  end.

Definition expandwhens_ss (dclseq : HiFP.hfstmt_seq) (cm : CEP.t def_expr) : HiFP.hfstmt_seq :=
  let newcncts := unfold_cm (CEP.elements cm) (Qnil ProdVarOrder.T) in
  (Qcat newcncts dclseq). (* rev *)

  (* Definition cm_true := expandBranch_fun (Qcons est (Qnil ProdVarOrder.T)) ce0 (Qnil ProdVarOrder.T) (CEP.empty def_expr).
  Definition cm_false := expandBranch_fun (Qcons esf (Qnil ProdVarOrder.T)) ce0 (Qnil ProdVarOrder.T) (CEP.empty def_expr).
  Compute (CEP.find p1 (snd cm_true)).
  Compute (CEP.find p1 (snd cm_false)).
  Definition cm_new := CEP.map2 (helper_tf ec0) (snd cm_true) (snd cm_false).
  Compute (CEP.find p1 cm_new). 

  Definition ss := fst (expandBranch_fun ess ce0 (Qnil ProdVarOrder.T) (CEP.empty def_expr)).
  Definition cm1 := snd (expandBranch_fun ess ce0 (Qnil ProdVarOrder.T) (CEP.empty def_expr)).
  Compute (ss). *)
 
(* another case: true branch == false branch 需要化简，没有mux *)

(* Proof of declarations *)
Fixpoint expandBranch_declaration (init_decl_map : CEP.env) (s : HiFP.hfstmt) (ce : CEP.env) : CEP.env :=
  match s with
  | Sskip => init_decl_map
  | Swire v type => match (CEP.find v init_decl_map) with
                    | None => CEP.add v (HiFP.aggr_typ type, Wire) init_decl_map
                    | Some _ => CEP.remove v init_decl_map
                    end
  | Sreg v r => match (CEP.find v init_decl_map) with
                | None => CEP.add v (HiFP.reg_typ r, Register) init_decl_map
                | Some _ => CEP.remove v init_decl_map
                end
  | Smem v m => match (CEP.find v init_decl_map) with
                | None => CEP.add v (HiFP.mem_typ m, Memory) init_decl_map
                | Some _ => CEP.remove v init_decl_map
                end
  | Sinst v v0 => match (CEP.find v init_decl_map) with
                | None => CEP.add v (fst (CEP.vtyp v0 ce), Instanceof) init_decl_map
                | Some _ => CEP.remove v init_decl_map
                end
  | Snode v e => match (CEP.find v init_decl_map) with
                | None => CEP.add v (HiFP.aggr_typ (HiFP.type_of_hfexpr e ce), Node) init_decl_map
                | Some _ => CEP.remove v init_decl_map
                end
  | Swhen c s1 s2 => let new_decl_map := expandBranch_declarations init_decl_map s1 ce in
                      expandBranch_declarations new_decl_map s2 ce
  | _ => init_decl_map
  end
with expandBranch_declarations (init_decl_map : CEP.env) (ss : HiFP.hfstmt_seq) (ce : CEP.env) : CEP.env :=
  match ss with
  | Qnil => init_decl_map
  | Qcons s stl => let newmap := expandBranch_declaration init_decl_map s ce in 
                   expandBranch_declarations newmap stl ce
  end.
(* old version
  match ss with
  | Qnil => init_decl_map
  | Qcons s st => let new_decl_map := (match s with
                  | Sskip => init_decl_map
                  | Swire v type => CEP.add v (HiFP.aggr_typ type, Wire) init_decl_map
                  | Sreg v r => CEP.add v (HiFP.reg_typ r, Register) init_decl_map
                  | Smem v m => CEP.add v (HiFP.mem_typ m, Memory) init_decl_map
                  | Sinst v v0 => CEP.add v (fst (CEP.vtyp v0 ce), Instanceof) init_decl_map
                  | Snode v e => CEP.add v (HiFP.aggr_typ (HiFP.type_of_hfexpr e ce), Node) init_decl_map
                  | Swhen c s1 s2 => let new_decl_map := expandBranch_declarations init_decl_map s1 ce in
                                      expandBranch_declarations new_decl_map s2 ce
                  | _ => init_decl_map
                  end) in
                  expandBranch_declarations new_decl_map st ce
  end.
*)

Inductive expandBranch_declaration_stmt : HiFP.hfstmt -> HiFP.hfstmt_seq -> CEP.env -> CEP.env -> Prop :=
  | ExpandBranch_declaration_skip seq_init ce ce':
      expandBranch_declaration_stmt (HiFP.sskip) seq_init ce ce'
  | ExpandBranch_declaration_wire v t seq_init ce ce' :
      forall envce, 
      CEP.Equal (expandBranch_declarations (expandBranch_declaration ce (Swire v t) envce) seq_init envce) ce' -> 
      expandBranch_declaration_stmt (Swire v t) seq_init ce ce'
  | ExpandBranch_declaration_reg v r seq_init ce ce' :
      forall envce, 
      CEP.Equal (expandBranch_declarations (expandBranch_declaration ce (Sreg v r) envce) seq_init envce) ce' -> 
      expandBranch_declaration_stmt (Sreg v r) seq_init ce ce'
  | ExpandBranch_declaration_inst v1 v2 seq_init ce ce' :
      forall envce, 
      CEP.Equal (expandBranch_declarations (expandBranch_declaration ce (Sinst v1 v2) envce) seq_init envce) ce' -> 
      expandBranch_declaration_stmt (Sinst v1 v2) seq_init ce ce'
  | ExpandBranch_declaration_node v e seq_init ce ce' :
      forall envce, 
      CEP.Equal (expandBranch_declarations (expandBranch_declaration ce (Snode v e) envce) seq_init envce) ce' -> 
      expandBranch_declaration_stmt (Snode v e) seq_init ce ce'
  | ExpandBranch_declaration_mem v m seq_init ce ce' :
      forall envce, 
      CEP.Equal (expandBranch_declarations (expandBranch_declaration ce (Smem v m) envce) seq_init envce) ce' -> 
      expandBranch_declaration_stmt (Smem v m) seq_init ce ce'
  | ExpandBranch_declaration_invalid v seq_init ce ce' :
      forall envce, 
      CEP.Equal (expandBranch_declarations (expandBranch_declaration ce (Sinvalid v) envce) seq_init envce) ce' -> 
      expandBranch_declaration_stmt (Sinvalid v) seq_init ce ce'
  | ExpandBranch_declaration_fcnct v e seq_init ce ce' :
      forall envce, 
      CEP.Equal (expandBranch_declarations (expandBranch_declaration ce (Sfcnct v e) envce) seq_init envce) ce' -> 
      expandBranch_declaration_stmt (Sfcnct v e) seq_init ce ce'
  | ExpandBranch_declaration_when c s1 s2 seq_init seq_init' ce ce' ce'' :
      expandBranch_declaration_stmts s1 seq_init ce ce' ->
      expandBranch_declaration_stmts s2 seq_init' ce ce'' ->
      expandBranch_declaration_stmt (Swhen c s1 s2) seq_init ce ce''
with expandBranch_declaration_stmts : HiFP.hfstmt_seq -> HiFP.hfstmt_seq -> CEP.env -> CEP.env -> Prop := 
  | ExpandBranch_declarations_nil seq_init ce ce' :
      expandBranch_declaration_stmts HiFP.qnil seq_init ce ce'
  | ExpandBranch_declarations_con s ss seq_init seq_init' ce ce' ce'' :
      expandBranch_declaration_stmt s seq_init ce ce' ->
      expandBranch_declaration_stmts ss seq_init' ce ce'' ->
      expandBranch_declaration_stmts (Qcons s ss) seq_init ce ce''.

(* old version lemma

Lemma cons_expandBranch_declarations (ss : HiFP.hfstmt_seq):
forall (seq_init : HiFP.hfstmt_seq) (seq_result : HiFP.hfstmt_seq) (cm_result : CEP.t def_expr),
  (expandBranch_funs ss (Some (Qnil ProdVarOrder.T)) cm_result).1 = Some seq_result ->
  (expandBranch_funs ss (Some seq_init) cm_result).1 = Some (Qcat seq_result seq_init).
Proof. 
  Admitted.

Lemma cat_expandBranch_delarations ss0 ss1:
  forall (ce: CEP.env) (cm : CEP.env),
  expandBranch_declarations cm (Qcat ss0 ss1) ce = expandBranch_declarations (expandBranch_declarations cm ss1 ce) ss0 ce.
Proof.
  Admitted.

Definition well_defined_stmt s cm seq_init : Prop :=
  match (expandBranch_fun s (Some seq_init) cm).1 with
  | Some _ => True
  | None => False
  end.

Fixpoint well_defined_stmts ss cm seq_init : Prop :=
  match ss with
  | Qnil => True
  | Qcons s st => match (expandBranch_funs st (Some (Qnil ProdVarOrder.T)) (expandBranch_fun s (Some (Qnil ProdVarOrder.T)) cm).1) with
                  | Some _ => True
                  | None => False
                  end
  end.*)

(* old version

Definition expandBranch_declaration_stmts_match (ss : HiFP.hfstmt_seq) : Prop :=
  forall ce cm thfstmt envce,
  (*well_defined_stmts ss cm (Qnil ProdVarOrder.T) ->*)
  fst (expandBranch_funs ss (Some (Qnil ProdVarOrder.T)) cm) = Some thfstmt ->
  CEP.Equal (expandBranch_declarations ce ss envce) (expandBranch_declarations ce thfstmt envce).

Lemma ExpandWhens_declarations_correct :
  forall (ss : HiFP.hfstmt_seq),
  expandBranch_declaration_stmts_match ss
with ExpandBranch_declaration_when :
  forall s,
  match s with
  | Swhen c s1 s2 => expandBranch_declaration_stmts_match s1 /\ expandBranch_declaration_stmts_match s2
  | _ => True
  end.
Proof.
  clear ExpandWhens_declarations_correct.
  induction ss.
  - rewrite /expandBranch_declaration_stmts_match.
    simpl.
    move => ce cm thfstmt envce Hseq.
    inversion Hseq.
    rewrite /expandBranch_declarations //.
  - rewrite /expandBranch_declaration_stmts_match.
    move => ce cm thfstmt envce Hseq.
    rewrite /expandBranch_declaration_stmts_match in IHss.
    simpl in Hseq.
    simpl.
    move : Hseq.
    case Hh : h => [|v t|||||||c ts fs]; try done.
      - simpl.
      apply IHss.
      (*rewrite Hh in H.
      simpl in H.
      move : H => [_ H].
      apply H. 
      done.*)
      - intro.
      simpl in Hseq.
      case Hcons : (expandBranch_funs ss (Some (Qnil ProdVarOrder.T)) (CEP.add v D_undefined cm)).1 => [tss|].
      specialize cons_expandBranch_declarations with (ss := ss) (seq_init := (Qcons (Swire (var:=ProdVarOrder.T) v t) (Qnil ProdVarOrder.T))) (cm_result := (CEP.add v D_undefined cm)) 
        (seq_result := tss).
      move => Hcons'.
      generalize Hcons.
      apply Hcons' in Hcons.
      clear Hcons'.
      move => Hcons'.
      rewrite Hcons in Hseq. 
      inversion Hseq.
      rewrite cat_expandBranch_delarations.

      specialize IHss with (ce := (match CEP.find v ce with
        | Some _ => CEP.remove v ce
        | None => CEP.add v (HiFP.aggr_typ t, Wire) ce
        end)) (cm := (CEP.add v D_undefined cm)) (envce := envce) (thfstmt := tss).

      simpl.
      rewrite IHss //.
      admit.
      (* (expandBranch_funs ss
           (Some (Qnil ProdVarOrder.T))
           (CEP.add v D_undefined cm)).1 =
        None *)

      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      (* when *)
      intro.
      specialize ExpandBranch_declaration_when with (s := (Swhen c ts fs)).
      simpl in ExpandBranch_declaration_when.
      move : ExpandBranch_declaration_when => [Ht Hf].
      (*case Hcons : (expandBranch_funs ss (Some (Qnil ProdVarOrder.T)) (CEP.add v D_undefined cm)).1 => [tss|].

      simpl in Hseq.
      simpl.

      - (* wire,register,mem,node,inst *)
      1,2,3,4,5: intros.
      1,2,3,4,5: rewrite cons_expandBranch_declarations.
      1,2,3,4,5: rewrite cat_expandBranch_delarations.
      1,2,3,4,5: simpl.
      specialize IHss with (ce_other_modules := ce_other_modules) (cm_init := (init_ref s f cm_init)) (init_decl_map := (CEP.add s (HiFP.aggr_typ f, Wire) init_decl_map)) (ce := ce).
      exact IHss.
      specialize IHss with (ce_other_modules := ce_other_modules) (cm_init := (init_register s (type h0) cm_init)) (init_decl_map := (CEP.add s (HiFP.reg_typ h0, Register) init_decl_map)) (ce := ce).
      exact IHss.
      specialize IHss with (ce_other_modules := ce_other_modules) (cm_init := cm_init) (init_decl_map := (CEP.add s (HiFP.mem_typ h0, Memory) init_decl_map)) (ce := ce).
      exact IHss.
      specialize IHss with (ce_other_modules := ce_other_modules) (cm_init := cm_init) (init_decl_map := (CEP.add s ((CEP.vtyp s0 ce).1, Instanceof) init_decl_map)) (ce := ce).
      exact IHss.
      specialize IHss with (ce_other_modules := ce_other_modules) (cm_init := cm_init) (init_decl_map := (CEP.add s (HiFP.aggr_typ (HiFP.type_of_hfexpr h0 ce), Node) init_decl_map)) (ce := ce).
      exact IHss.
      - (* cnct *)
      intros.
      case h0 => [r|||]; try done.
      - (* invalid *)
      intros.
      case h0 => [r|||]; try done.
      - (* when *)
      specialize ExpandWhens_declarations_correct_Swhen with (s := (Swhen c ts fs)).
      simpl in ExpandWhens_declarations_correct_Swhen.
      move : ExpandWhens_declarations_correct_Swhen => [Ht Hf].

      case Hcombine : (combine_branches c
        (expandBranch_fun ts ce_other_modules
          (Qnil ProdVarOrder.T) cm_init)
        (expandBranch_fun fs ce_other_modules
          (Qnil ProdVarOrder.T) cm_init)) => [new_hseq new_cm].
      rewrite cons_expandBranch_declarations.
      rewrite cat_expandBranch_delarations.
      have ->: new_hseq = fst (combine_branches c
        (expandBranch_fun ts ce_other_modules
          (Qnil ProdVarOrder.T) cm_init)
        (expandBranch_fun fs ce_other_modules
          (Qnil ProdVarOrder.T) cm_init)) by rewrite Hcombine.
      rewrite /combine_branches.
      simpl.
      clear Hcombine.
      rewrite /ExpandBranch_declarations_is_correct in Ht.
      rewrite /ExpandBranch_declarations_is_correct in Hf. 
      assert (Hcombine : (expandBranch_declarations
        (expandBranch_declarations init_decl_map ts ce) fs ce) = (expandBranch_declarations init_decl_map
        (Qcat
           (expandBranch_fun ts ce_other_modules
              (Qnil ProdVarOrder.T) cm_init).1
           (expandBranch_fun fs ce_other_modules
              (Qnil ProdVarOrder.T) cm_init).1) ce)).
      admit.
      rewrite -Hcombine.
      specialize IHss with (ce_other_modules := ce_other_modules) (cm_init := new_cm) (init_decl_map := (expandBranch_declarations
      (expandBranch_declarations init_decl_map ts ce) fs ce)) (ce := ce).
      exact IHss.
  
  (* prove ExpandWhens_declarations_correct_Swhen *)
  clear ExpandWhens_declarations_correct_Swhen.
  intro.
  destruct s; try done.
  Admitted.

  (* CEP.Lemmas.add_same:
  forall [elt : Type] [x : PVM.key] [e : elt] [m : PVM.t elt],
  PVM.find x m = Some e -> PVM.Equal (PVM.add x e m) m 

  CEP.Lemmas.add_m:
  forall [elt : Type] [x y : PVM.SE.t],
  PVM.SE.eq x y ->
  forall x0 y0 : elt,
  x0 = y0 ->
  forall x1 y1 : PVM.t elt,
  PVM.Equal x1 y1 -> PVM.Equal (PVM.add x x0 x1) (PVM.add y y0 y1)*)
  *)
  Admitted.*)

Lemma expandBranch_declaration_skip_match :
  forall ce seq_init cm thfstmt envce,
  fst (expandBranch_fun (HiFP.sskip) (Some seq_init) cm) = Some thfstmt ->
  expandBranch_declaration_stmt (HiFP.sskip) seq_init ce (expandBranch_declarations ce thfstmt envce).
Proof.
  intros.
  apply ExpandBranch_declaration_skip.
Qed.
  
Lemma expandBranch_declaration_wire_match :
  forall v t ce seq_init envce thfstmt cm,
  (*~~ CEP.mem v ce ->*)
  fst (expandBranch_fun (Swire v t) (Some seq_init) cm) = Some thfstmt ->
  expandBranch_declaration_stmt (Swire v t) seq_init ce (expandBranch_declarations ce thfstmt envce).
Proof.
  move => v t ce seq_init envce thfstmt cm H0.
  apply ExpandBranch_declaration_wire with (envce := envce).
  simpl in H0. 
  case Hin : (Qin (Swire v t) seq_init).
  - rewrite Hin in H0. 
    discriminate.
  - rewrite Hin in H0. 
    inversion H0. 
    simpl.
    apply HiFP.PCELemmas.Equal_refl.
  Qed.

Lemma expandBranch_declaration_reg_match :
  forall v r ce seq_init envce thfstmt cm,
  fst (expandBranch_fun (Sreg v r) (Some seq_init) cm) = Some thfstmt ->
  expandBranch_declaration_stmt (Sreg v r) seq_init ce (expandBranch_declarations ce thfstmt envce).
Proof.
  move => v r ce seq_init envce thfstmt cm H0.
  apply ExpandBranch_declaration_reg with (envce := envce).
  simpl in H0. 
  case Hin : (Qin (Sreg v r) seq_init).
  - rewrite Hin in H0. 
    discriminate.
  - rewrite Hin in H0. 
    inversion H0. 
    simpl.
    apply HiFP.PCELemmas.Equal_refl.
  Qed.

Lemma expandBranch_declaration_mem_match :
  forall v t ce seq_init envce thfstmt cm,
  fst (expandBranch_fun (Smem v t) (Some seq_init) cm) = Some thfstmt ->
  expandBranch_declaration_stmt (Smem v t) seq_init ce (expandBranch_declarations ce thfstmt envce).
Proof.
  move => v t ce seq_init envce thfstmt cm H0.
  apply ExpandBranch_declaration_mem with (envce := envce).
  simpl in H0. 
  case Hin : (Qin (Smem v t) seq_init).
  - rewrite Hin in H0. 
    discriminate.
  - rewrite Hin in H0. 
    inversion H0. 
    simpl.
    apply HiFP.PCELemmas.Equal_refl.
  Qed.
  
Lemma expandBranch_declaration_node_match :
  forall v t ce seq_init envce thfstmt cm,
  fst (expandBranch_fun (Snode v t) (Some seq_init) cm) = Some thfstmt ->
  expandBranch_declaration_stmt (Snode v t) seq_init ce (expandBranch_declarations ce thfstmt envce).
Proof.
  move => v t ce seq_init envce thfstmt cm H0.
  apply ExpandBranch_declaration_node with (envce := envce).
  simpl in H0. 
  case Hin : (Qin (Snode v t) seq_init).
  - rewrite Hin in H0. 
    discriminate.
  - rewrite Hin in H0. 
    inversion H0. 
    simpl.
    apply HiFP.PCELemmas.Equal_refl.
  Qed.

Lemma expandBranch_declaration_inst_match :
  forall v t ce seq_init envce thfstmt cm,
  fst (expandBranch_fun (Sinst v t) (Some seq_init) cm) = Some thfstmt ->
  expandBranch_declaration_stmt (Sinst v t) seq_init ce (expandBranch_declarations ce thfstmt envce).
Proof.
  move => v t ce seq_init envce thfstmt cm H0.
  apply ExpandBranch_declaration_inst with (envce := envce).
  simpl in H0. 
  case Hin : (Qin (Sinst v t) seq_init).
  - rewrite Hin in H0. 
    discriminate.
  - rewrite Hin in H0. 
    inversion H0. 
    simpl.
    apply HiFP.PCELemmas.Equal_refl.
  Qed.

Lemma expandBranch_declaration_invalid_match :
  forall v ce seq_init envce thfstmt cm,
  fst (expandBranch_fun (Sinvalid v) (Some seq_init) cm) = Some thfstmt ->
  expandBranch_declaration_stmt (Sinvalid v) seq_init ce (expandBranch_declarations ce thfstmt envce).
Proof.
  move => v ce seq_init envce thfstmt cm H0.
  apply ExpandBranch_declaration_invalid with (envce := envce).
  simpl in H0.
  move : H0. 
  case : v.
  1,2,3,4: intros.
  1,2,3,4: simpl.
  1,2,3,4: simpl in H0.
  1,2,3,4: inversion H0.
  1,2,3,4: apply HiFP.PCELemmas.Equal_refl.
  Qed.
  
Lemma expandBranch_declaration_fcnct_match :
  forall v e ce seq_init envce thfstmt cm,
  fst (expandBranch_fun (Sfcnct v e) (Some seq_init) cm) = Some thfstmt ->
  expandBranch_declaration_stmt (Sfcnct v e) seq_init ce (expandBranch_declarations ce thfstmt envce).
Proof.
  move => v e ce seq_init envce thfstmt cm H0.
  apply ExpandBranch_declaration_fcnct with (envce := envce).
  simpl in H0.
  move : H0. 
  case : v.
  1,2,3,4: intros.
  1,2,3,4: simpl.
  1,2,3,4: simpl in H0.
  1,2,3,4: inversion H0.
  1,2,3,4: apply HiFP.PCELemmas.Equal_refl.
  Qed.

Lemma expandBranch_declaration_when_match :
  forall c s1 s2 ce seq_init envce thfstmt cm seq_init',
  fst (expandBranch_funs s1 (Some seq_init) cm) = Some seq_init' ->
  fst (expandBranch_fun (Swhen c s1 s2) (Some seq_init) cm) = Some thfstmt ->
  expandBranch_declaration_stmts s1 seq_init ce (expandBranch_declarations ce seq_init' envce) ->
  expandBranch_declaration_stmts s2 seq_init' ce (expandBranch_declarations ce thfstmt envce) ->
  expandBranch_declaration_stmt (Swhen c s1 s2) seq_init ce (expandBranch_declarations ce thfstmt envce).
Proof.
  intros.
  apply ExpandBranch_declaration_when with (seq_init' := seq_init') (ce' := (expandBranch_declarations ce seq_init' envce)); try by done.
Qed.

Lemma expandBranch_declaration_match (s : HiFP.hfstmt) :
  forall ce envce thfstmt seq_init cm,
  fst (expandBranch_fun s (Some seq_init) cm) = Some thfstmt ->
  expandBranch_declaration_stmt s seq_init ce (expandBranch_declarations ce thfstmt envce)
with expandBranch_declarations_match (ss : HiFP.hfstmt_seq) :
  forall ce envce thfstmt seq_init cm,
  fst (expandBranch_funs ss (Some seq_init) cm) = Some thfstmt ->
  expandBranch_declaration_stmts ss seq_init ce (expandBranch_declarations ce thfstmt envce).
Proof.
  clear expandBranch_declaration_match.
  case Hs : s => [|v t|||||||c s1 s2]; try done.
  - move => ce envce thfstmt seq_init cm.
    apply expandBranch_declaration_skip_match.
  - move => ce envce thfstmt seq_init cm.
    apply expandBranch_declaration_wire_match.
  - move => ce envce thfstmt seq_init cm.
    apply expandBranch_declaration_reg_match.
  - move => ce envce thfstmt seq_init cm.
    apply expandBranch_declaration_mem_match.
  - move => ce envce thfstmt seq_init cm.
    apply expandBranch_declaration_inst_match.
  - move => ce envce thfstmt seq_init cm.
    apply expandBranch_declaration_node_match.
  - move => ce envce thfstmt seq_init cm.
    apply expandBranch_declaration_fcnct_match.
  - move => ce envce thfstmt seq_init cm.
    apply expandBranch_declaration_invalid_match.
  - intros.
    case Hf : (fst (expandBranch_funs s1 (Some seq_init) cm)) => [seq_init'|].
    apply expandBranch_declaration_when_match with (cm := cm) (seq_init' := seq_init'); try by done.
    apply expandBranch_declarations_match with (cm := cm); try by done.
    simpl in H.
    rewrite Hf in H. 
    apply expandBranch_declarations_match with (cm := cm); try by done.
    admit. (* (expandBranch_funs s1 (Some seq_init) cm).1 = None *)
  clear expandBranch_declarations_match.
  induction ss.
  - simpl.
    intros.
    inversion H. 
    simpl.
    apply ExpandBranch_declarations_nil.
    - intros.
    case Hf : ((expandBranch_fun h (Some seq_init) cm).1) => [seq_init'|].
    apply ExpandBranch_declarations_con with (s := h) (ss := ss) (seq_init := seq_init) 
    (seq_init' := seq_init') (ce := ce) (ce' := (expandBranch_declarations ce seq_init' envce)); try by done.
    apply expandBranch_declaration_match with (cm := cm); try by done.
    simpl in H.
    apply IHss with (cm:= (snd (expandBranch_fun h (Some seq_init) cm))); try by done.
    rewrite -Hf //.
Admitted.



(* Proof of connections *)
Inductive expr_tree : Type :=
  (*| T_undeclared (* in this execution path, the component is not declared *) *)
  | T_undefined (* the component is erroneously not connected *)
  | T_invalidated (* the component is not connected but the programmer has
                    indicated with an "is invalid" statement that this is ok *)
  | T_fexpr : HiFP.hfexpr -> expr_tree
  | T_choice : HiFP.hfexpr (* condition *) ->
              expr_tree (* choice if condition is true *) ->
              expr_tree (* choice if condition is false *) -> expr_tree
  .
  
Definition helper_tree (c : HiFP.hfexpr) (true_tree : option expr_tree) (false_tree : option expr_tree) : option expr_tree := 
  match true_tree, false_tree with
  (*| Some T_undeclared, _ => false_tree
  | _, Some T_undeclared => true_tree*)
  | None, None => None
  | Some T_invalidated, _ => false_tree
  | _, Some T_invalidated => true_tree
  | Some T_undefined, _ => false_tree (* 任何branch有undefined都是错误 *)
  | _, Some T_undefined => true_tree (* 任何branch有undefined都是错误 *)
  | Some tree1, Some tree2 => Some (T_choice c tree1 tree2)
  | _, _ => true_tree
  end.

Fixpoint expandBranch_connection_tree (s : HiFP.hfstmt) (expr_tree_map : CEP.t expr_tree) : CEP.t expr_tree :=
  match s with
  | Swire v _
  | Smem v _
  | Sinst v _ => CEP.add v T_undefined expr_tree_map 
  | Sreg v r => CEP.add v (T_fexpr (Eref (Eid v))) expr_tree_map
  | Sfcnct (Eid r) e => CEP.add r (T_fexpr e) expr_tree_map
  | Sinvalid (Eid r) => CEP.add r T_invalidated expr_tree_map
  | Swhen c s1 s2 => let true_child := expandBranch_connection_trees s1 expr_tree_map in
                     let false_child := expandBranch_connection_trees s2 expr_tree_map in
                     CEP.map2 (helper_tree c) true_child false_child
  | _ => expr_tree_map
  end
with expandBranch_connection_trees (ss : HiFP.hfstmt_seq) (expr_tree_map : CEP.t expr_tree) : CEP.t expr_tree :=
  match ss with
  | Qnil => expr_tree_map
  | Qcons s st => let new_expr_tree_map := expandBranch_connection_tree s expr_tree_map in
                  expandBranch_connection_trees st new_expr_tree_map
  end.

(*Definition ce0 :CEP.env:= CEP.empty (cmpnt_init_typs ProdVarOrder.T * fcomponent).
Definition agt := HiFP.aggr_typ (Gtyp (Fuint 1)).

Definition p1 : pvar := (N.of_nat 1, N0).
Definition p2 : pvar := (N.of_nat 2, N0).
Definition ec0 := (HiFP.econst (Fuint 1) [::false]).
Definition ec1 := (HiFP.econst (Fuint 2) [::false;false]).
Definition ec2 := (HiFP.econst (Fuint 2) [::false;true]).
Definition ec3 := (HiFP.econst (Fuint 2) [::true;true]).
Definition ty0 := Gtyp (Fuint 2).
Definition es1 := Swire p1 ty0.
Definition esinvalid := Sinvalid (Eid p1).
Definition est := Sfcnct (Eid p1) ec2.
Definition esf := Sfcnct (Eid p1) ec3.
Definition esw := Swhen ec0 (Qcons est (Qnil ProdVarOrder.T)) ((Qnil ProdVarOrder.T)).
Definition ess := Qcons es1 (Qcons esf (Qcons esw (Qnil ProdVarOrder.T))).

Definition temp_tree_map := expandBranch_connection_tree ess (CEP.empty expr_tree).
Definition a_tree := CEP.find p1 temp_tree_map.
Compute (a_tree).*)

Fixpoint connection_tree2expr (tree: expr_tree) : option def_expr :=
  match tree with
  (*| T_undeclared => None*)
  | T_undefined => Some D_undefined
  | T_invalidated => Some D_invalidated
  | T_fexpr e => Some (D_fexpr e)
  | T_choice cond true_tree false_tree => let true_expr := connection_tree2expr true_tree in
                                          let false_expr := connection_tree2expr false_tree in
                                          match true_expr, false_expr with
                                          | Some (D_fexpr te), Some (D_fexpr fe) => (*if te == fe then Some (D_fexpr te)
                                                        else*) Some (D_fexpr (Emux cond te fe))
                                          | Some D_invalidated, Some (D_fexpr fe) => false_expr
                                          | Some (D_fexpr fe), Some D_invalidated => true_expr
                                          | _, _ => true_expr
                                          end
   end.

Definition texpr_match_ttree cm tm : Prop :=
  forall v texpr1 ttree1,
  CEP.find v cm = texpr1 ->
  CEP.find v tm = Some ttree1 ->
  texpr1 = connection_tree2expr ttree1.

Inductive expandBranch_connection_stmt : HiFP.hfstmt -> CEP.t def_expr -> CEP.t def_expr -> CEP.t expr_tree -> CEP.t expr_tree -> Prop :=
  | ExpandBranch_connection_skip cm cm' tm tm':
      expandBranch_connection_stmt (HiFP.sskip) cm cm' tm tm'
  (* old version
  | ExpandBranch_connection_wire v t cm cm' tm tm':
      forall texpr ttree,
      CEP.find v cm' = texpr -> (* D_undefined *)
      CEP.find v tm' = Some ttree -> 
      texpr = connection_tree2expr ttree ->
      expandBranch_connection_stmt (Swire v t) cm cm' tm tm'
  | ExpandBranch_connection_reg v r cm cm' tm tm' :
      forall texpr ttree,
      CEP.find v cm' = texpr -> (* D_expr (Eid r) *)
      CEP.find v tm' = Some ttree -> 
      texpr = connection_tree2expr ttree ->
      expandBranch_connection_stmt (Sreg v r) cm cm' tm tm'
  | ExpandBranch_connection_inst v1 v2 cm cm' tm tm':
      forall texpr ttree,
      CEP.find v1 cm' = texpr -> (* D_undefined *)
      CEP.find v1 tm' = Some ttree -> 
      texpr = connection_tree2expr ttree ->
      expandBranch_connection_stmt (Sinst v1 v2) cm cm' tm tm'
  | ExpandBranch_connection_node v e cm tm:
      expandBranch_connection_stmt (Snode v e) cm cm tm tm
  | ExpandBranch_connection_mem v m cm cm' tm tm' :
      forall texpr ttree,
      CEP.find v cm' = texpr -> (* D_undefined *)
      CEP.find v tm' = Some ttree -> 
      texpr = connection_tree2expr ttree ->
      expandBranch_connection_stmt (Smem v m) cm cm' tm tm'
  | ExpandBranch_connection_invalid v cm cm' tm tm':
      forall texpr ttree,
      CEP.find v cm' = texpr -> (* D_invalid *)
      CEP.find v tm' = Some ttree -> 
      texpr = connection_tree2expr ttree ->
      expandBranch_connection_stmt (Sinvalid (Eid v)) cm cm' tm tm'
  | ExpandBranch_connection_fcnct v e cm cm' tm tm':
      forall texpr ttree,
      CEP.find v cm' = texpr -> (* D_expr *)
      CEP.find v tm' = Some ttree -> 
      texpr = connection_tree2expr ttree ->
      expandBranch_connection_stmt (Sfcnct (Eid v) e) cm cm' tm tm'
  | ExpandBranch_connection_when c s1 s2 cm cm' cm'' cm0 tm tm' tm' tm0 :
      expandBranch_connection_stmts s1 cm cm' tm tm' ->
      expandBranch_connection_stmts s2 cm cm'' tm tm'' ->
      (forall v texpr1 texpr2 ttree1 ttree2 ttree',
      CEP.mem v cm0 /\ CEP.mem v tm0 ->
      CEP.find v cm' = texpr1 ->
      CEP.find v cm'' = texpr2 ->
      CEP.find v tm' = Some ttree1 ->
      CEP.find v tm'' = Some ttree2 ->
      helper_tree c (Some ttree1) (Some ttree2) = Some ttree' ->
      helper_tf c texpr1 texpr2 = connection_tree2expr ttree'
      ) ->
      expandBranch_connection_stmt (Swhen c s1 s2) cm cm0 tm tm0
  *)
  | ExpandBranch_connection_wire v t cm cm' tm tm':
      texpr_match_ttree cm tm ->
      texpr_match_ttree cm' tm' ->
      expandBranch_connection_stmt (Swire v t) cm cm' tm tm'
  | ExpandBranch_connection_reg v r cm cm' tm tm' :
      texpr_match_ttree cm tm ->
      texpr_match_ttree cm' tm' ->
      expandBranch_connection_stmt (Sreg v r) cm cm' tm tm'
  | ExpandBranch_connection_inst v1 v2 cm cm' tm tm':
      texpr_match_ttree cm tm ->
      texpr_match_ttree cm' tm' ->
      expandBranch_connection_stmt (Sinst v1 v2) cm cm' tm tm'
  | ExpandBranch_connection_node v e cm cm' tm tm':
      texpr_match_ttree cm tm ->
      texpr_match_ttree cm' tm' ->
      expandBranch_connection_stmt (Snode v e) cm cm tm tm
  | ExpandBranch_connection_mem v m cm cm' tm tm' :
      texpr_match_ttree cm tm ->
      texpr_match_ttree cm' tm' ->
      expandBranch_connection_stmt (Smem v m) cm cm' tm tm'
  | ExpandBranch_connection_invalid v cm cm' tm tm':
      texpr_match_ttree cm tm ->
      texpr_match_ttree cm' tm' ->
      expandBranch_connection_stmt (Sinvalid (Eid v)) cm cm' tm tm'
  | ExpandBranch_connection_fcnct v e cm cm' tm tm':
      texpr_match_ttree cm tm ->
      texpr_match_ttree cm' tm' ->
      expandBranch_connection_stmt (Sfcnct (Eid v) e) cm cm' tm tm'
  | ExpandBranch_connection_when c s1 s2 cm cm0 tm tm0 :
      texpr_match_ttree cm tm ->
      texpr_match_ttree cm0 tm0 ->
      expandBranch_connection_stmt (Swhen c s1 s2) cm cm0 tm tm0

with expandBranch_connection_stmts : HiFP.hfstmt_seq -> CEP.t def_expr -> CEP.t def_expr -> CEP.t expr_tree -> CEP.t expr_tree -> Prop :=
  | ExpandBranch_connections_nil cm tm :
      expandBranch_connection_stmts HiFP.qnil cm cm tm tm
  | ExpandBranch_connections_con s ss cm cm' cm'' tm tm' tm'':
      expandBranch_connection_stmt s cm cm' tm tm' ->
      expandBranch_connection_stmts ss cm' cm'' tm' tm'' ->
      expandBranch_connection_stmts (Qcons s ss) cm cm'' tm tm''.

(* old version
  for every statement case only look at the corresponding varaiable, hard to use to handle statement sequence.
Lemma expandBranch_connection_wire_match :
  forall v ty cm tm seq_result texpr ttree,
  CEP.find v (snd (expandBranch_fun (Swire v ty) seq_result cm)) = texpr -> 
  CEP.find v (expandBranch_connection_tree (Swire v ty) tm) = Some ttree -> 
  expandBranch_connection_stmt (Swire v ty) cm (snd (expandBranch_fun (Swire v ty) seq_result cm)) tm (expandBranch_connection_tree (Swire v ty) tm).
Proof.
  intros.
  apply ExpandBranch_connection_wire with (texpr := texpr) (ttree := ttree); try done.
  rewrite /expandBranch_fun in H. 
  simpl in H. 
  assert (Hfindadd : CEP.find v (CEP.add v D_undefined cm) = Some D_undefined).
  apply HiFP.PCELemmas.add_eq_o.
  apply CEP.SE.eq_refl.
  rewrite Hfindadd in H.
  clear Hfindadd.
  rewrite -H.
  rewrite /expandBranch_connection_tree in H0.
  assert (Hfindadd : CEP.find v (CEP.add v T_undefined tm) = Some T_undefined).
  apply HiFP.PCELemmas.add_eq_o.
  apply CEP.SE.eq_refl.
  rewrite Hfindadd in H0.
  clear Hfindadd.
  inversion H0.
  rewrite /connection_tree2expr //.
Qed.
*)

(* new lemma should prove that after dealing with any single statement, for every element, its texpr and ttree match property should hold. *)
Lemma expandBranch_connection_wire_match :
  forall v ty cm cm' tm tm' seq_result,
  texpr_match_ttree cm tm ->
  cm' = snd (expandBranch_fun (Swire v ty) seq_result cm) -> 
  tm' = expandBranch_connection_tree (Swire v ty) tm -> 
  expandBranch_connection_stmt (Swire v ty) cm cm' tm tm'.
Proof.
  move => v ty cm cm' tm tm' seq_result Hpre Hcm' Htm'.
  apply ExpandBranch_connection_wire; try by done.
  simpl in Hcm'.
  simpl in Htm'.
  rewrite /texpr_match_ttree in Hpre.
  rewrite /texpr_match_ttree.
  move => v1 texpr1 ttree1.
  (* discuss on whether v1 equals to v? *)
Admitted.

(* old version on all the other single statement case
Lemma expandBranch_connection_reg_match :
  forall v r cm tm seq_result texpr ttree,
  CEP.find v (snd (expandBranch_fun (Sreg v r) seq_result cm)) = texpr -> 
  CEP.find v (expandBranch_connection_tree (Sreg v r) tm) = Some ttree -> 
  expandBranch_connection_stmt (Sreg v r) cm (snd (expandBranch_fun (Sreg v r) seq_result cm)) tm (expandBranch_connection_tree (Sreg v r) tm).
Proof.
  intros.
  apply ExpandBranch_connection_reg with (texpr := texpr) (ttree := ttree); try done.
  rewrite /expandBranch_fun in H. 
  simpl in H. 
  assert (Hfindadd : CEP.find v (CEP.add v (D_fexpr (Eref (Eid (var:=ProdVarOrder.T) v))) cm) = Some (D_fexpr (Eref (Eid (var:=ProdVarOrder.T) v)))).
  apply HiFP.PCELemmas.add_eq_o.
  apply CEP.SE.eq_refl.
  rewrite Hfindadd in H.
  clear Hfindadd.
  rewrite -H.
  rewrite /expandBranch_connection_tree in H0.
  assert (Hfindadd : CEP.find v (CEP.add v (T_fexpr (Eref (Eid (var:=ProdVarOrder.T) v))) tm) = Some (T_fexpr (Eref (Eid (var:=ProdVarOrder.T) v)))).
  apply HiFP.PCELemmas.add_eq_o.
  apply CEP.SE.eq_refl.
  rewrite Hfindadd in H0.
  clear Hfindadd.
  inversion H0.
  rewrite /connection_tree2expr //.
Qed.

Lemma expandBranch_connection_inst_match :
  forall v1 v2 cm tm seq_result texpr ttree,
  CEP.find v1 (snd (expandBranch_fun (Sinst v1 v2) seq_result cm)) = texpr -> 
  CEP.find v1 (expandBranch_connection_tree (Sinst v1 v2) tm) = Some ttree -> 
  expandBranch_connection_stmt (Sinst v1 v2) cm (snd (expandBranch_fun (Sinst v1 v2) seq_result cm)) tm (expandBranch_connection_tree (Sinst v1 v2) tm).
Proof.
  intros.
  apply ExpandBranch_connection_inst with (texpr := texpr) (ttree := ttree); try done.
  rewrite /expandBranch_fun in H. 
  simpl in H. 
  assert (Hfindadd : CEP.find v1 (CEP.add v1 (D_undefined) cm) = Some (D_undefined)).
  apply HiFP.PCELemmas.add_eq_o.
  apply CEP.SE.eq_refl.
  rewrite Hfindadd in H.
  clear Hfindadd.
  rewrite -H.
  rewrite /expandBranch_connection_tree in H0.
  assert (Hfindadd : CEP.find v1 (CEP.add v1 (T_undefined) tm) = Some (T_undefined)).
  apply HiFP.PCELemmas.add_eq_o.
  apply CEP.SE.eq_refl.
  rewrite Hfindadd in H0.
  clear Hfindadd.
  inversion H0.
  rewrite /connection_tree2expr //.
Qed.

Lemma expandBranch_connection_snode_match :
  forall v e cm tm seq_result,
  expandBranch_connection_stmt (Snode v e) cm (snd (expandBranch_fun (Snode v e) seq_result cm)) tm (expandBranch_connection_tree (Snode v e) tm).
Proof.
  intros.
  apply ExpandBranch_connection_node.
Qed.

Lemma expandBranch_connection_mem_match :
  forall v m cm tm seq_result texpr ttree,
  CEP.find v (snd (expandBranch_fun (Smem v m) seq_result cm)) = texpr -> 
  CEP.find v (expandBranch_connection_tree (Smem v m) tm) = Some ttree -> 
  expandBranch_connection_stmt (Smem v m) cm (snd (expandBranch_fun (Smem v m) seq_result cm)) tm (expandBranch_connection_tree (Smem v m) tm).
Proof.
  intros.
  apply ExpandBranch_connection_mem with (texpr := texpr) (ttree := ttree); try done.
  rewrite /expandBranch_fun in H. 
  simpl in H. 
  assert (Hfindadd : CEP.find v (CEP.add v D_undefined cm) = Some D_undefined).
  apply HiFP.PCELemmas.add_eq_o.
  apply CEP.SE.eq_refl.
  rewrite Hfindadd in H.
  clear Hfindadd.
  rewrite -H.
  rewrite /expandBranch_connection_tree in H0.
  assert (Hfindadd : CEP.find v (CEP.add v T_undefined tm) = Some T_undefined).
  apply HiFP.PCELemmas.add_eq_o.
  apply CEP.SE.eq_refl.
  rewrite Hfindadd in H0.
  clear Hfindadd.
  inversion H0.
  rewrite /connection_tree2expr //.
Qed.

Lemma expandBranch_connection_invalid_match :
  forall v cm tm seq_result texpr ttree,
  CEP.find v (snd (expandBranch_fun (Sinvalid (Eid v)) seq_result cm)) = texpr -> 
  CEP.find v (expandBranch_connection_tree (Sinvalid (Eid v)) tm) = Some ttree -> 
  expandBranch_connection_stmt (Sinvalid (Eid v)) cm (snd (expandBranch_fun (Sinvalid (Eid v)) seq_result cm)) tm (expandBranch_connection_tree (Sinvalid (Eid v)) tm).
Proof.
  intros.
  apply ExpandBranch_connection_invalid with (texpr := texpr) (ttree := ttree); try done.
  rewrite /expandBranch_fun in H. 
  simpl in H. 
  assert (Hfindadd : CEP.find v (CEP.add v D_invalidated cm) = Some D_invalidated).
  apply HiFP.PCELemmas.add_eq_o.
  apply CEP.SE.eq_refl.
  rewrite Hfindadd in H.
  clear Hfindadd.
  rewrite -H.
  rewrite /expandBranch_connection_tree in H0.
  assert (Hfindadd : CEP.find v (CEP.add v T_invalidated tm) = Some T_invalidated).
  apply HiFP.PCELemmas.add_eq_o.
  apply CEP.SE.eq_refl.
  rewrite Hfindadd in H0.
  clear Hfindadd.
  inversion H0.
  rewrite /connection_tree2expr //.
Qed.

Lemma expandBranch_connection_fcnct_match :
  forall v e cm tm seq_result texpr ttree,
  CEP.find v (snd (expandBranch_fun (Sfcnct (Eid v) e) seq_result cm)) = texpr -> 
  CEP.find v (expandBranch_connection_tree (Sfcnct (Eid v) e) tm) = Some ttree -> 
  expandBranch_connection_stmt (Sfcnct (Eid v) e) cm (snd (expandBranch_fun (Sfcnct (Eid v) e) seq_result cm)) tm (expandBranch_connection_tree (Sfcnct (Eid v) e) tm).
Proof.
  intros.
  apply ExpandBranch_connection_fcnct with (texpr := texpr) (ttree := ttree); try done.
  rewrite /expandBranch_fun in H. 
  simpl in H. 
  assert (Hfindadd : CEP.find v (CEP.add v (D_fexpr e) cm) = Some (D_fexpr e)).
  apply HiFP.PCELemmas.add_eq_o.
  apply CEP.SE.eq_refl.
  rewrite Hfindadd in H.
  clear Hfindadd.
  rewrite -H.
  rewrite /expandBranch_connection_tree in H0.
  assert (Hfindadd : CEP.find v (CEP.add v (T_fexpr e) tm) = Some (T_fexpr e)).
  apply HiFP.PCELemmas.add_eq_o.
  apply CEP.SE.eq_refl.
  rewrite Hfindadd in H0.
  clear Hfindadd.
  Info 1 auto.
  inversion H0.
  rewrite /connection_tree2expr //.
Qed.

Lemma expandBranch_connection_when_match :
  forall c s1 s2 cm cm' cm'' cm0 tm tm' tm'' tm0 (seq_result : HiFP.hfstmt_seq),
  cm' = (snd (expandBranch_funs s1 (Some seq_result) cm)) ->
  cm'' = (snd (expandBranch_funs s2 (Some seq_result) cm)) ->
  tm' = (expandBranch_connection_trees s1 tm) ->
  tm'' = (expandBranch_connection_trees s2 tm) ->
  (forall v texpr1 ttree1,
  CEP.find v cm' = texpr1 ->
  CEP.find v tm' = Some ttree1 ->
  texpr1 = connection_tree2expr ttree1) ->
  (forall v texpr2 ttree2,
  CEP.find v cm'' = texpr2 ->
  CEP.find v tm'' = Some ttree2 ->
  texpr2 = connection_tree2expr ttree2) ->
  expandBranch_connection_stmts s1 cm cm' tm tm' ->
  expandBranch_connection_stmts s2 cm cm'' tm tm'' ->
  expandBranch_connection_stmt (Swhen c s1 s2) cm cm0 tm tm0.
Proof.
  intros.
  apply ExpandBranch_connection_when with (cm' := cm') (cm'' := cm'') (tm' := tm') (tm'' := tm''); try by done.
  intros.
  specialize H3 with (v := v) (texpr1 := texpr1) (ttree1 := ttree1).
  specialize H4 with (v := v) (texpr2 := texpr2) (ttree2 := ttree2).
  rewrite H3; try by done.
  rewrite H4; try by done.
  clear H3 H4 H8 H9 H10 H11.
  move : H12.
  case Ht1 : ttree1 => [||e1|c1 tt1 ft1].
    - (* T_undefined *)
    admit.
    - (* T_invalid *)
    admit.
    - (* T_expr *)
    case Ht2 : ttree2 => [||e2|c2 tt2 ft2].
      - (* T_undefined *)
      admit.
      - (* T_invalid *)
      admit.
      - (* T_expr *)
      simpl.
      move => Hchoice.
      inversion Hchoice.
      clear H4 Hchoice.
      simpl.
      done.
      - (* T_choice *)
      move => Hchoice.
      simpl in Hchoice.
      inversion Hchoice.
      clear H4 Hchoice.
      rewrite {1}/connection_tree2expr.
      case Hsn: (connection_tree2expr (T_choice c2 tt2 ft2)) => [texpr|]; try by done.
      case Htexpr: texpr => [||te]; try by done.
      rewrite Htexpr in Hsn.
      admit.
      admit.
      admit.
      admit. 
    - (* T_choice *)
    case Hsn1: (connection_tree2expr (T_choice c1 tt1 ft1)) => [texpr|]; try by done.
    case Htexpr1: texpr => [||te]; try by done.
    rewrite Htexpr1 in Hsn1.
    admit. (* undefined *)

    case Ht2 : ttree2 => [||e2|c2 tt2 ft2].
      - (* T_undefined *)
      simpl.
      move => Hchoice.
      inversion Hchoice.
      clear H4 Hchoice.
      rewrite Hsn1 Htexpr1//.
      - (* T_invalid *)
      simpl.
      move => Hchoice.
      inversion Hchoice.
      clear H4 Hchoice.
      rewrite Hsn1 Htexpr1//.
      - (* T_expr *)
      rewrite {1}/connection_tree2expr.
      simpl.
      move => Hchoice.
      inversion Hchoice.
      rewrite Htexpr1 in Hsn1.
      clear H4 Hchoice.
      admit.
      - (* T_choice *)
      case Hsn2: (connection_tree2expr (T_choice c2 tt2 ft2)) => [texpr'|]; try by done.
      case Htexpr2: texpr' => [||te']; try by done.
      rewrite Htexpr2 in Hsn2.
        (* undefined *)
        admit.
        (* invalid *)
        rewrite Htexpr1 in Hsn1.
        rewrite Htexpr2 in Hsn2.
        simpl.
        admit.
        (* expr *)
        rewrite Htexpr1 in Hsn1.
        rewrite Htexpr2 in Hsn2.
        simpl.
        admit.
        (* None *)
        admit.
    case Ht2 : ttree2 => [||e2|c2 tt2 ft2].
      - (* T_undefined *)
      simpl.
      move => Hchoice.
      inversion Hchoice.
      clear H4 Hchoice.
      rewrite Hsn1 Htexpr1//.
      - (* T_invalid *)
      simpl.
      move => Hchoice.
      inversion Hchoice.
      clear H4 Hchoice.
      rewrite Hsn1 Htexpr1//.
      - (* T_expr *)
      rewrite {1}/connection_tree2expr.
      simpl.
      move => Hchoice.
      inversion Hchoice.
      rewrite Htexpr1 in Hsn1.
      clear H4 Hchoice.
      admit.
      - (* T_choice *)
      case Hsn2: (connection_tree2expr (T_choice c2 tt2 ft2)) => [texpr'|]; try by done.
      case Htexpr2: texpr' => [||te']; try by done.
      rewrite Htexpr2 in Hsn2.
        (* undefined *)
        admit.
        (* invalid *)
        rewrite Htexpr1 in Hsn1.
        rewrite Htexpr2 in Hsn2.
        simpl.
        admit.
        (* expr *)
        rewrite Htexpr1 in Hsn1.
        rewrite Htexpr2 in Hsn2.
        simpl.
        admit.
        (* None *)
        admit.
    (* None *)
    admit.
Admitted.
*)

Lemma expandBranch_connection_when_match' : 
  forall c s1 s2 cm cm0 tm tm0 (seq_result : HiFP.hfstmt_seq),
  texpr_match_ttree cm tm ->
  cm0 = (snd (expandBranch_fun (Swhen c s1 s2) (Some seq_result) cm)) ->
  tm0 = (expandBranch_connection_tree (Swhen c s1 s2) tm) ->
  expandBranch_connection_stmt (Swhen c s1 s2) cm cm0 tm tm0.
Proof.
  move => c s1 s2 cm cm0 tm tm0 seq_result Hpre Hcm0 Htm0.
  apply ExpandBranch_connection_when; try by done.
  simpl in Hcm0.
  simpl in Htm0.
  assert (Hm1 : texpr_match_ttree ((expandBranch_funs s1 (Some seq_result) cm).2) (expandBranch_connection_trees s1 tm)).
  admit. (* 从stmts match可得 *)
  assert (Hm2 : texpr_match_ttree ((expandBranch_funs s2 (expandBranch_funs s1 (Some seq_result) cm).1 cm).2) ((expandBranch_connection_trees s2 tm))).
  admit.
  rewrite /texpr_match_ttree.
  rewrite Hcm0 Htm0.
  clear Hcm0 Htm0.
  move => v texpr0 ttree0 Hexpr0 Htree0.
  rewrite StructStateP.Lemmas.map2_1bis in Hexpr0.
  rewrite StructStateP.Lemmas.map2_1bis in Htree0.
  case Ht1 : (CEP.find v (expandBranch_connection_trees s1 tm)).


  (*rewrite /texpr_match_ttree in Hm1.
  rewrite /texpr_match_ttree in Hm2.*)

  admit.
  1,2: simpl.
  1,2: done.

Qed.


Lemma expandBranch_connection_stmt_match (s : HiFP.hfstmt) :
  forall cm cm' tm tm' (seq_result : HiFP.hfstmt_seq),
  texpr_match_ttree cm tm ->
  cm' = snd (expandBranch_fun s (Some seq_result) cm) ->
  tm' = expandBranch_connection_tree s tm ->
  expandBranch_connection_stmt s cm cm' tm tm'
with expandBranch_connection_stmts_match (ss : HiFP.hfstmt_seq) :
  forall cm cm' tm tm' (seq_result : HiFP.hfstmt_seq),
  texpr_match_ttree cm tm ->
  cm' = snd (expandBranch_funs ss (Some seq_result) cm) ->
  tm' = expandBranch_connection_trees ss tm ->
  expandBranch_connection_stmts ss cm cm' tm tm'.
Proof.
  clear expandBranch_connection_stmt_match.
  case Hs : s => [|v t|||||||c s1 s2]; try done.
  - move => cm cm' tm tm' seq_result Hpre Hcm' Htm'.
    simpl in Hcm'.
    simpl in Htm'.
    rewrite Hcm' Htm'.
    apply ExpandBranch_connection_skip.
  - 
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  - (* when *)
  admit.

  clear expandBranch_connection_stmts_match.

  induction ss.
  - move => cm cm' tm tm' seq_result Hpre Hcm' Htm'.
    simpl in Hcm'.
    simpl in Htm'.
    rewrite Hcm' Htm'.
    apply ExpandBranch_connections_nil.
  - move => cm cm' tm tm' seq_result Hpre Hcm' Htm'.
    simpl in Hcm'.
    simpl in Htm'.
    apply ExpandBranch_connections_con with (cm' := snd (expandBranch_fun h (Some seq_result) cm)) (tm' := (expandBranch_connection_tree h tm)).
    apply expandBranch_connection_stmt_match with (seq_result := seq_result); try by done.
    case Hf : ((expandBranch_fun h (Some seq_result) cm).1) => [seq_result'|].
    rewrite Hf in Hcm'.
    apply IHss with (seq_result := seq_result'); try by done.
    admit. (* same as 单条 *)
    admit. (* (expandBranch_fun h (Some seq_result) cm).1 = None *)
Admitted.

(* old version
Definition ExpandBranch_connection_match (ss : HiFP.hfstmt_seq) : Prop :=
 forall (v : pvar) (ce_other_modules : CEP.env) (cm_init : CEP.t def_expr) (init_decl_map : CEP.env) (ce : CEP.env),
 match (CEP.find v (expandBranch_connection_tree ss (CEP.empty expr_tree))) with
 | None => True (* ? *)
 | Some expr_tree => CEP.find v (snd (expandBranch_fun ss ce_other_modules (Qnil ProdVarOrder.T) cm_init))
 = connection_tree2expr expr_tree
end.

(*Lemma expandBranch_connection_stmt_match (s : HiFP.hfstmt) :
  forall cm cm' tm tm' (seq_result : HiFP.hfstmt_seq),
  cm' = snd (expandBranch_fun s (Some seq_result) cm) ->
  tm' = expandBranch_connection_tree s tm ->
  expandBranch_connection_stmt s cm cm' tm tm'
with expandBranch_connection_stmts_match (ss : HiFP.hfstmt_seq) :
  forall cm cm' tm tm' (seq_result : HiFP.hfstmt_seq),
  cm' = snd (expandBranch_funs ss (Some seq_result) cm) ->
  tm' = expandBranch_connection_trees ss tm ->
  expandBranch_connection_stmts ss cm cm' tm tm'.
Proof.
  clear expandBranch_connection_stmt_match.
      case Hh : h => [|v t|v r|v m|v1 v2|v e|v e|v|e s1 s2].
    - (* skip *)
      apply ExpandBranch_connection_skip.
    - (* wire *)
    case Hf : (CEP.find v (expandBranch_connection_tree (Swire v t) tm)) => [e|].
    apply expandBranch_connection_wire_match with (texpr := (CEP.find v (snd (expandBranch_fun (Swire v t) (Some seq_result) cm))))  (ttree := e).
    done.
    rewrite Hf //.
    assert (CEP.mem v (expandBranch_connection_tree (Swire v t) tm)).
    simpl.
    rewrite HiFP.PCELemmas.mem_add_eq //.
    apply CEP.SE.eq_refl.
    simpl in Hf.
    rewrite HiFP.PCELemmas.add_eq_o in Hf.
    discriminate.
    apply CEP.SE.eq_refl.
      (* reg *)
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
    (* when *)
    apply expandBranch_connection_when_match with (cm' := (snd (expandBranch_funs s1 (Some seq_result) cm)))
      (cm'' := (snd (expandBranch_funs s2 (Some seq_result) cm))) (tm' := (expandBranch_connection_trees s1 tm)) 
      (tm'' := (expandBranch_connection_trees s2 tm)) (seq_result := seq_result); try by done.
    admit.
    admit.
    admit.
    admit.

    case Hf : (fst (expandBranch_fun h (Some seq_result) cm)) => [seq_result'|].
    specialize IHss with (cm := snd (expandBranch_fun h (Some seq_result) cm)) (cm' := cm') 
    (tm := (expandBranch_connection_tree h tm)) (tm' := tm') (seq_result := seq_result').
    apply IHss; try by done.
    rewrite H. 
    clear H H0.
    move : IHss.
    case Hh :( expandBranch_fun h (Some seq_result) cm) => [t1 t2].
    move => IHss.
    rewrite -Hf Hh.
    simpl.
    done.

    (* (expandBranch_fun h (Some seq_result) cm).1 = None
    discriminate. *)

Fixpoint already_ground_type (ss : HiFP.hfstmt_seq) (prop : Prop) : Prop :=
  match ss with
  | Qnil => prop
  | Qcons s st => let new_prop := (match s with
                  | Sskip => prop
                  | Swire _ ty => match ty with
                                  | Gtyp _ => prop
                                  | _ => False
                                  end
                  | Sreg r reg => match (type reg) with
                                  | Gtyp _ => prop
                                  | _ => False
                                  end
                  | Smem r mem => match (data_type mem) with
                                  | Gtyp _ => prop
                                  | _ => False
                                  end
                  | Swhen _ s1 s2 => already_ground_type s1 prop /\ already_ground_type s2 prop
                  | _ => prop
                  end) 
                  in already_ground_type st new_prop
  end.

Lemma add_expandBranch_connection : 
  forall (ss : HiFP.hfstmt_seq) (ce_other_modules : CEP.env) (result : HiFP.hfstmt_seq) (cm_init : CEP.t def_expr)
  (v r : pvar) (texpr : def_expr),
  if v == r then CEP.find v (snd (expandBranch_fun ss ce_other_modules result (CEP.add r texpr cm_init))) = Some texpr
  else CEP.find v (snd (expandBranch_fun ss ce_other_modules result (CEP.add r texpr cm_init))) = CEP.find v (snd (expandBranch_fun ss ce_other_modules result cm_init)).
Proof.
Admitted.

Lemma add_expandBranch_connection_tree :
  forall (ss : HiFP.hfstmt_seq) (v r : pvar) (tchild : expr_tree),
  if v == r then CEP.find v
    (expandBranch_connection_tree ss
      (CEP.add r T_undefined (CEP.empty expr_tree))) = Some T_undefined
  else (expandBranch_connection_tree ss (CEP.add r T_undefined (CEP.empty expr_tree))) = (expandBranch_connection_tree ss (CEP.empty expr_tree)).
Proof.
Admitted.

Theorem ExpandWhens_connection_correct :
  forall (ss : HiFP.hfstmt_seq),
  already_ground_type ss True -> ExpandBranch_connection_match ss
with ExpandWhens_connection_correct_Swhen :
  forall (s : HiFP.hfstmt),
  match s with
  | Swhen c ss_true ss_false => already_ground_type ss_true True ->
                                already_ground_type ss_false True ->
                                ExpandBranch_connection_match ss_true /\
                                ExpandBranch_connection_match ss_false
  | _ => True
  end.
Proof.
  (* prove ExpandWhens_connection_correct *)
  clear ExpandWhens_connection_correct.
  intros.
  induction ss. 
  - rewrite /ExpandBranch_connection_match.
    simpl.
    trivial.
  - rewrite /ExpandBranch_connection_match.
    intros.
    rewrite /ExpandBranch_connection_match in IHss.
    case Htree : (CEP.find v (expandBranch_connection_tree (Qcons h ss) (CEP.empty expr_tree))) => [t|]; try done.
    unfold expandBranch_connection_tree in Htree; fold expandBranch_connection_tree in Htree.
    unfold expandBranch_fun; fold expandBranch_fun.
    move : t Htree.
    case Hh : h => [|r ty|r reg||||||c ts fs]; try done.
      - (* skip *)
      intros.
      specialize IHss with (v := v) (ce_other_modules := ce_other_modules) (cm_init := cm_init).
      rewrite Htree in IHss.
      simpl in H. 
      rewrite Hh in H.
      rewrite IHss //.
      - (* wire *)
      intros.
      rewrite /init_ref.
      simpl in H. 
      rewrite Hh in H.
      move : H.
      case ty => [gt||]; try done.
        - (* ground type *)
        move => Hground.
        case Heq : (v == r).
        specialize add_expandBranch_connection with (ss := ss) (ce_other_modules := ce_other_modules)
          (result := (Qcons (Swire (var:=ProdVarOrder.T) r (Gtyp gt)) (Qnil ProdVarOrder.T))) (cm_init := cm_init) (v := v) (r := r) (texpr := D_undefined).
        move => Hadd.
        rewrite Heq in Hadd.
        rewrite Hadd.
        rewrite /connection_tree2expr.
        
  admit.
  (* prove ExpandWhens_connection_correct_Swhen *)
  clear ExpandWhens_connection_correct_Swhen.
  intro.
  destruct s; try done.
  intros.
  split.
  apply ExpandWhens_connection_correct.
  done.
  apply ExpandWhens_connection_correct.
  done.
Admitted.
*)*)



End ExpandWhens.