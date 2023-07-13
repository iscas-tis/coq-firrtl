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

Definition helper_tf (c : HiFP.hfexpr) (true_expr : option def_expr) (false_expr : option def_expr) : option def_expr := 
  match true_expr, false_expr with
  | None, None => None
  | None, _ => false_expr
  | _, None => true_expr
  | Some (D_fexpr t), Some (D_fexpr f) => (*if t == f then true_expr 
                                      else*) Some (D_fexpr (Emux c t f)) 
  | Some D_invalidated, Some (D_fexpr f) => false_expr
  | Some D_undefined, _ => Some D_undefined
  | _, Some D_undefined => Some D_undefined
  | _, Some D_invalidated => true_expr
  end.

(*Fixpoint expandBranch_fun (s : HiFP.hfstmt) (hseq_result : option HiFP.hfstmt_seq) (cm_result : CEP.t def_expr) : (option HiFP.hfstmt_seq * CEP.t def_expr) :=
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
  end.*)

Inductive em : Type :=
  | OK : (CEP.t def_expr) -> em
  | Eundeclared : em
  | Egtyp : em.

Fixpoint expandBranch_fun (s : HiFP.hfstmt) (hseq_result : option HiFP.hfstmt_seq) (cm_result : em) : (option HiFP.hfstmt_seq * em) :=
  (* ss : statement seq going to be expanded 
     ce_other_modules : type information for ports of other modules, used in inst case
     hseq_result : declaration statement in ss, including those in branches
     cm_result : rhs expr map for every var that is connected to, also solving last connecting*)
  match cm_result with
  | OK cm_result =>
    (match s with
    | Sskip => (hseq_result, OK cm_result)
    | Swire v type => let new_seq := match hseq_result with
                      | None => None
                      | Some hseq_result => if (Qin s hseq_result) then None else Some (Qcons s hseq_result)
                      end in
                      let cm_wire := CEP.add v D_undefined cm_result
                      in (new_seq, OK cm_wire)
    | Sreg v r => let new_seq := match hseq_result with
                  | None => None
                  | Some hseq_result => if (Qin s hseq_result) then None else Some (Qcons s hseq_result)
                  end in
                  let cm_reg := CEP.add v (D_fexpr (Eref (Eid v))) cm_result
                  in (new_seq, OK cm_reg)
    | Smem v m => let new_seq := match hseq_result with
                  | None => None
                  | Some hseq_result => if (Qin s hseq_result) then None else Some (Qcons s hseq_result)
                  end in
                  let cm_mem := CEP.add v D_undefined cm_result
                  in (new_seq, OK cm_mem) (* TBD *)
    | Sinvalid (Eid r) => let cm_inv := match (CEP.find r cm_result) with
                          | None => Eundeclared
                          | _ => OK (CEP.add r D_invalidated cm_result)
                          end in (hseq_result, cm_inv)
    | Sinst v v0 => let new_seq := match hseq_result with
                    | None => None
                    | Some hseq_result => if (Qin s hseq_result) then None else Some (Qcons s hseq_result)
                    end in
                    let cm_inst := CEP.add v D_undefined cm_result
                    in (new_seq, OK cm_inst) (* TBD *)
    | Snode v e => let new_seq := match hseq_result with
                  | None => None
                  | Some hseq_result => if (Qin s hseq_result) then None else Some (Qcons s hseq_result)
                  end in (new_seq, OK cm_result)
    | Sfcnct (Eid r) e2 => let cm_cnct := match (CEP.find r cm_result) with
                          | None => Eundeclared
                          | _ => OK (CEP.add r (D_fexpr e2) cm_result)
                          end in (hseq_result, cm_cnct)
    | Swhen c s1 s2 => (*let (new_seq0, cm_true) := expandBranch_funs s1 hseq_result cm_result in*)
                      (*let (new_seq, cm_false) := expandBranch_funs s2 (fst (expandBranch_funs s1 hseq_result cm_result)) cm_result in*)
                      match snd (expandBranch_funs s1 hseq_result (OK cm_result)), snd (expandBranch_funs s2 (fst (expandBranch_funs s1 hseq_result (OK cm_result))) (OK cm_result)) with
                      | OK cm1, OK cm2 =>
                        (fst (expandBranch_funs s2 (fst (expandBranch_funs s1 hseq_result (OK cm_result))) (OK cm_result)),
                          OK (CEP.map2 (helper_tf c) (cm1) (cm2)))
                      | e, OK _ => (fst (expandBranch_funs s2 (fst (expandBranch_funs s1 hseq_result (OK cm_result))) (OK cm_result)), e)
                      | OK _, e => (fst (expandBranch_funs s2 (fst (expandBranch_funs s1 hseq_result (OK cm_result))) (OK cm_result)), e)
                      | e1, _ => (fst (expandBranch_funs s2 (fst (expandBranch_funs s1 hseq_result (OK cm_result))) (OK cm_result)), e1)
                      end
    | _ => (hseq_result, Egtyp) 
    end)
  | e => (hseq_result, e)
  end
with expandBranch_funs (ss : HiFP.hfstmt_seq) (hseq_result : option HiFP.hfstmt_seq) (cm_result : em) : (option HiFP.hfstmt_seq * em) :=
  match cm_result with
  | OK cm_result =>
    (match ss with
    | Qnil => (hseq_result, OK cm_result)
    | Qcons s stl => (*let (new_hseq, new_cm) := expandBranch_fun s hseq_result cm_result in *)
                    expandBranch_funs stl (fst (expandBranch_fun s hseq_result (OK cm_result))) (snd (expandBranch_fun s hseq_result (OK cm_result)))
    end)
  | e => (hseq_result, e)
  end.

Inductive ret_seq : Type :=
  | ans : HiFP.hfstmt_seq -> ret_seq
  | Erepeatdef : ret_seq
  | Eundeclare : ret_seq
  | Eaggtyp : ret_seq
  | Eundefine : ret_seq.

Fixpoint unfold_cm (cml : seq (pvar * def_expr)) sts : ret_seq := 
  match cml with 
  | nil => sts
  | e :: es => match e with
              | (v, D_fexpr tempe) => match sts with
                                      | ans s' => unfold_cm es (ans (Qcons (Sfcnct (Eid v) tempe) s'))
                                      | err => err
                                      end
              | (v, D_invalidated) => match sts with
                                      | ans s' => unfold_cm es (ans (Qcons (Sinvalid (Eid v)) s'))
                                      | err => err
                                      end
              | (v, D_undefined) => Eundefine (* D_undefined 未被连接error *)
              end
  end.   

Definition expandwhens_ss (dclseq : option HiFP.hfstmt_seq) (cm : em) : ret_seq :=
  match dclseq with
  | None => Erepeatdef
  | Some dseq => match cm with
                | OK cm' => match unfold_cm (CEP.elements cm') (ans (Qnil ProdVarOrder.T)) with
                            | ans res_seq => ans (Qcat dseq res_seq)
                            | err => err
                            end
                | Eundeclared => Eundeclare
                | Egtyp => Eaggtyp
                end
  end
  . (* rev *)

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

*)

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
  fst (expandBranch_fun (Swire v t) (Some seq_init) (OK cm)) = Some thfstmt ->
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
  fst (expandBranch_fun (Sreg v r) (Some seq_init) (OK cm)) = Some thfstmt ->
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
  fst (expandBranch_fun (Smem v t) (Some seq_init) (OK cm)) = Some thfstmt ->
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
  fst (expandBranch_fun (Snode v t) (Some seq_init) (OK cm)) = Some thfstmt ->
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
  fst (expandBranch_fun (Sinst v t) (Some seq_init) (OK cm)) = Some thfstmt ->
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
  fst (expandBranch_fun (Sinvalid v) (Some seq_init) (OK cm)) = Some thfstmt ->
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
  fst (expandBranch_fun (Sfcnct v e) (Some seq_init) (OK cm)) = Some thfstmt ->
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
  fst (expandBranch_funs s1 (Some seq_init) (OK cm)) = Some seq_init' ->
  fst (expandBranch_fun (Swhen c s1 s2) (Some seq_init) (OK cm)) = Some thfstmt ->
  expandBranch_declaration_stmts s1 seq_init ce (expandBranch_declarations ce seq_init' envce) ->
  expandBranch_declaration_stmts s2 seq_init' ce (expandBranch_declarations ce thfstmt envce) ->
  expandBranch_declaration_stmt (Swhen c s1 s2) seq_init ce (expandBranch_declarations ce thfstmt envce).
Proof.
  intros.
  apply ExpandBranch_declaration_when with (seq_init' := seq_init') (ce' := (expandBranch_declarations ce seq_init' envce)); try by done.
Qed.

Definition well_connected_m cm :=
  forall v, match CEP.find v cm with
            | Some D_undefined => false
            | _ => true
  end.

Fixpoint well_defined_stmt s cm seq_init :=
  match s with
  | Swhen _ s1 s2 => match (expandBranch_funs s1 seq_init cm) with
                    | (Some _, OK cm1) => well_defined_stmts s1 cm seq_init /\ well_connected_m cm1
                    | _ => False
                    end /\
                    match (expandBranch_funs s2 (expandBranch_funs s1 seq_init cm).1 cm).2 with
                    | OK cm2 => well_defined_stmts s2 cm (expandBranch_funs s1 seq_init cm).1 /\ well_connected_m cm2
                    | _ => False
                    end
  | Sfcnct (Eid v0) _ => match cm with
                        | OK cm' => CEP.mem v0 cm'
                        | _ => False
                        end
  | Sinvalid (Eid v0) => match cm with
                        | OK cm' => CEP.mem v0 cm'
                        | _ => False
                        end
  | Sfcnct _ _ => False
  | Sinvalid _ => False
  | _ => True
  end
with well_defined_stmts ss cm seq_init :=
  match ss with
  | Qnil => True
  | Qcons s st => well_defined_stmt s cm seq_init /\
                  match (expandBranch_fun s seq_init cm) with
                  | (Some _, OK _) => True
                  | _ => False
                  end /\ well_defined_stmts st ((expandBranch_fun s seq_init cm).2) ((expandBranch_fun s seq_init cm).1)
  end.

Lemma expandBranch_declaration_match (s : HiFP.hfstmt) :
  forall ce envce thfstmt seq_init cm(*seq_init' cm1 cm2*),
  (*match s with
  | Swhen _ s1 s2 => (expandBranch_funs s1 (Some seq_init) (OK cm)) = (Some seq_init', OK cm1) /\ 
    (expandBranch_funs s2 (expandBranch_funs s1 (Some seq_init) (OK cm)).1 (OK cm)).2 = OK cm2
  | _ => True
  end *)
  well_defined_stmt s (OK cm) (Some seq_init) ->
  fst (expandBranch_fun s (Some seq_init) (OK cm)) = Some thfstmt ->
  expandBranch_declaration_stmt s seq_init ce (expandBranch_declarations ce thfstmt envce)
with expandBranch_declarations_match (ss : HiFP.hfstmt_seq) :
  forall ce envce thfstmt seq_init cm, (*  (seq_init' : HiFP.hfstmt_seq) (cm1 : CEP.t def_expr) (cm2 : CEP.t def_expr) *)
  well_defined_stmts ss (OK cm) (Some seq_init) ->
  fst (expandBranch_funs ss (Some seq_init) (OK cm)) = Some thfstmt ->
  expandBranch_declaration_stmts ss seq_init ce (expandBranch_declarations ce thfstmt envce).
Proof.
  clear expandBranch_declaration_match.
  case Hs : s => [|v t|||||||c s1 s2]; try done.
  - move => ce envce thfstmt seq_init cm _.
    apply expandBranch_declaration_skip_match.
  - move => ce envce thfstmt seq_init cm _.
    apply expandBranch_declaration_wire_match.
  - move => ce envce thfstmt seq_init cm _.
    apply expandBranch_declaration_reg_match.
  - move => ce envce thfstmt seq_init cm _.
    apply expandBranch_declaration_mem_match.
  - move => ce envce thfstmt seq_init cm _.
    apply expandBranch_declaration_inst_match.
  - move => ce envce thfstmt seq_init cm _.
    apply expandBranch_declaration_node_match.
  - move => ce envce thfstmt seq_init cm _.
    apply expandBranch_declaration_fcnct_match.
  - move => ce envce thfstmt seq_init cm _.
    apply expandBranch_declaration_invalid_match.
  - move => ce envce thfstmt seq_init cm.
    move : Hs. 
    case H : (expandBranch_funs s1 (Some seq_init) (OK cm)) => [s' m'].
    move => Hs Hwd H0.
    simpl in Hwd.
    move : Hwd => [H1 H2].
    case Hs' : s' => [seq_init'|].
    rewrite Hs' in H. 
    rewrite H in H1.
    case Hm' : m' => [cm'||].
    rewrite Hm' in H. 
    apply expandBranch_declaration_when_match with (cm := cm) (seq_init' := seq_init'); try by done.
    rewrite H //.
    apply expandBranch_declarations_match with (cm := cm); try by done.
    rewrite Hm' in H1.
    move : H1 => [H1 _]; done.
    rewrite H //.
    apply expandBranch_declarations_match with (cm := cm); try by done.
    rewrite H in H2.
    simpl in H2.
    case H2' : (expandBranch_funs s2 (Some seq_init') (OK cm)).2 => [cm2||].
    rewrite H2' in H2.
    move : H2 => [H2 _]; done.
    rewrite H2' in H2; done.
    rewrite H2' in H2; done.
    simpl in H0.
    rewrite H in H0.
    simpl in H0.
    rewrite H in H2.
    simpl in H2.
    case H2' : (expandBranch_funs s2 (Some seq_init') (OK cm)).2 => [cm2||].
    rewrite H2' in H0.
    simpl in H0; done.
    rewrite H2' in H2; done.
    rewrite H2' in H2; done.
    simpl in H0.
    rewrite Hm' in H1; done.
    rewrite Hm' in H1; done.
    rewrite Hs' in H. 
    rewrite H in H1; done.
  clear expandBranch_declarations_match.
  induction ss.
  - simpl.
    intros.
    inversion H. 
    simpl.
    apply ExpandBranch_declarations_nil.
  - move => ce envce thfstmt seq_init cm Hwd H.
    simpl in Hwd.
    move : Hwd => [H0 H1].
    move : H1 => [H1 H2].
    case Hf : (expandBranch_fun h (Some seq_init) (OK cm)) => [s' m'].
    case Hs' : s' => [seq_init'|].
    case Hm' : m' => [cm1||].
    rewrite Hs' Hm' in Hf.
    apply ExpandBranch_declarations_con with (s := h) (ss := ss) (seq_init := seq_init) 
    (seq_init' := seq_init') (ce := ce) (ce' := (expandBranch_declarations ce seq_init' envce)); try by done.
    apply expandBranch_declaration_match with (cm := cm); try by done.
    simpl in H.
    rewrite Hf; done.
    apply IHss with (seq_init := seq_init') (cm := cm1); try by done.
    rewrite Hf in H2; done.
    simpl in H. 
    rewrite Hf in H; done.
    rewrite Hs' Hm' in Hf.
    rewrite Hf in H1; done.
    rewrite Hs' Hm' in Hf.
    rewrite Hf in H1; done.
    rewrite Hf Hs' in H1; done.
Qed.

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
  | None, _ => false_tree
  | _, None => true_tree
  | Some T_undefined, _ => true_tree
  | _, Some T_undefined => false_tree
  | Some T_invalidated, _ => false_tree
  | _, Some T_invalidated => true_tree
  | Some t1, Some t2 => Some (T_choice c t1 t2)
  end.

  (* no None in T_choice *)

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
  | (T_fexpr e) => Some (D_fexpr e)
  | (T_choice cond true_tree false_tree) => let true_expr := connection_tree2expr true_tree in
                                          let false_expr := connection_tree2expr false_tree in
                                          match true_expr, false_expr with
                                          | Some (D_fexpr te), Some (D_fexpr fe) => (*if te == fe then Some (D_fexpr te)
                                                        else*) Some (D_fexpr (Emux cond te fe))
                                          | Some D_invalidated, Some (D_fexpr fe) => false_expr
                                          | Some (D_fexpr fe), Some D_invalidated => true_expr
                                          | None, _ => false_expr
                                          | _, _ => true_expr
                                          end
   end.

(*Definition texpr_match_ttree cm tm : Prop :=
  forall v texpr1 ttree1,
  CEP.find v cm = texpr1 ->
  CEP.find v tm = Some ttree1 ->
  texpr1 = connection_tree2expr ttree1.*)
Definition texpr_match_ttree cm tm : Prop :=
  forall v texpr1,
  CEP.find v cm = texpr1 ->
  (match (CEP.find v tm) with
  | Some ttree1 => texpr1 = connection_tree2expr ttree1
  | None => texpr1 = None
  end).

Inductive expandBranch_connection_stmt : HiFP.hfstmt -> CEP.t def_expr -> CEP.t def_expr -> CEP.t expr_tree -> CEP.t expr_tree -> Prop :=
  | ExpandBranch_connection_skip cm cm' tm tm':
      expandBranch_connection_stmt (HiFP.sskip) cm cm' tm tm'
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

(* new lemma should prove that after dealing with any single statement, for every element, its texpr and ttree match property should hold. *)
Lemma expandBranch_connection_wire_match :
  forall v ty cm cm0 tm tm' seq_result,
  texpr_match_ttree cm tm ->
  cm0 = snd (expandBranch_fun (Swire v ty) (Some seq_result) (OK cm)) -> 
  tm' = expandBranch_connection_tree (Swire v ty) tm -> 
  match cm0 with
  | OK cm' => texpr_match_ttree cm' tm'
  | _ => True
  end.
Proof .
  move => v ty cm cm0 tm tm' seq_result Hpre Hcm' Htm'.
  move : Hcm'.
  case : cm0 => [cm'||]; try by done.
  move => Hcm'.
  (*apply ExpandBranch_connection_wire; try by done.*)
  simpl in Hcm'.
  inversion Hcm'.
  simpl in Htm'.
  rewrite /texpr_match_ttree in Hpre.
  rewrite /texpr_match_ttree.
  move => v1 texpr1 Hte.
  rewrite Htm'.
  specialize Hpre with (v := v1) (texpr1 := texpr1).
  case Heq : (v1 == v).
  rewrite StructStateP.Lemmas.P.F.add_eq_o in Hte.
  rewrite StructStateP.Lemmas.P.F.add_eq_o.
  simpl.
  rewrite -Hte //.
  1,2: move /eqP : Heq => Heq.
  1,2: rewrite Heq.
  1,2: apply CEP.SE.eq_refl.

  rewrite StructStateP.Lemmas.add_neq_o in Hte.
  rewrite StructStateP.Lemmas.add_neq_o.
  apply Hpre in Hte; done.
  1,2:apply contra_not with (P := (v1 == v)).
  1,3:apply StructStateP.Lemmas_M.KeySetoid.
  1,2:apply elimF with (b := (v1 == v)); try by done.
  1,2:apply idP.
Qed.

Lemma expandBranch_connection_reg_match :
  forall v ty cm cm0 tm tm' seq_result,
  texpr_match_ttree cm tm ->
  cm0 = snd (expandBranch_fun (Sreg v ty) (Some seq_result) (OK cm)) -> 
  tm' = expandBranch_connection_tree (Sreg v ty) tm -> 
  match cm0 with
  | OK cm' => texpr_match_ttree cm' tm'
  | _ => True
  end.
Proof.
  move => v ty cm cm0 tm tm' seq_result Hpre Hcm' Htm'.
  move : Hcm'.
  case : cm0 => [cm'||]; try by done.
  move => Hcm'.
  (*apply ExpandBranch_connection_reg; try by done.*)
  simpl in Hcm'.
  inversion Hcm'.
  simpl in Htm'.
  rewrite /texpr_match_ttree in Hpre.
  rewrite /texpr_match_ttree.
  move => v1 texpr1 ttree1.
  rewrite Htm'.
  move => Hte Htt.
  case Heq : (v1 == v).
  rewrite StructStateP.Lemmas.P.F.add_eq_o in Hte.
  rewrite StructStateP.Lemmas.P.F.add_eq_o in Htt.
  inversion Htt.
  rewrite -Hte.
  simpl.
  done.
  1,2: move /eqP : Heq => Heq.
  1,2: rewrite Heq.
  1,2: apply CEP.SE.eq_refl.

  rewrite StructStateP.Lemmas.add_neq_o in Hte.
  rewrite StructStateP.Lemmas.add_neq_o in Htt.
  apply Hpre with (v := v1); try by done.

  1,2:apply contra_not with (P := (v1 == v)).
  1,3:apply StructStateP.Lemmas_M.KeySetoid.
  1,2:apply elimF with (b := (v1 == v)); try by done.
  1,2:apply idP.
Qed.

Lemma expandBranch_connection_mem_match :
  forall v ty cm cm0 tm tm' seq_result,
  texpr_match_ttree cm tm ->
  cm0 = snd (expandBranch_fun (Smem v ty) (Some seq_result) (OK cm)) -> 
  tm' = expandBranch_connection_tree (Smem v ty) tm -> 
  match cm0 with
  | OK cm' => texpr_match_ttree cm' tm'
  | _ => True
  end.
Proof.
  move => v ty cm cm0 tm tm' seq_result Hpre Hcm' Htm'.
  move : Hcm'.
  case : cm0 => [cm'||]; try by done.
  move => Hcm'.
  (*apply ExpandBranch_connection_mem; try by done.*)
  simpl in Hcm'.
  inversion Hcm'.
  simpl in Htm'.
  rewrite /texpr_match_ttree in Hpre.
  rewrite /texpr_match_ttree.
  move => v1 texpr1 ttree1.
  rewrite Htm'.
  move => Hte Htt.
  case Heq : (v1 == v).
  rewrite StructStateP.Lemmas.P.F.add_eq_o in Hte.
  rewrite StructStateP.Lemmas.P.F.add_eq_o in Htt.
  inversion Htt.
  rewrite -Hte.
  simpl.
  done.
  1,2: move /eqP : Heq => Heq.
  1,2: rewrite Heq.
  1,2: apply CEP.SE.eq_refl.

  rewrite StructStateP.Lemmas.add_neq_o in Hte.
  rewrite StructStateP.Lemmas.add_neq_o in Htt.
  apply Hpre with (v := v1); try by done.

  1,2:apply contra_not with (P := (v1 == v)).
  1,3:apply StructStateP.Lemmas_M.KeySetoid.
  1,2:apply elimF with (b := (v1 == v)); try by done.
  1,2:apply idP.
Qed.

Lemma expandBranch_connection_inst_match :
  forall v ty cm cm0 tm tm' seq_result,
  texpr_match_ttree cm tm ->
  cm0 = snd (expandBranch_fun (Sinst v ty) (Some seq_result) (OK cm)) -> 
  tm' = expandBranch_connection_tree (Sinst v ty) tm -> 
  match cm0 with
  | OK cm' => texpr_match_ttree cm' tm'
  | _ => True
  end.
Proof.
  move => v ty cm cm0 tm tm' seq_result Hpre Hcm' Htm'.
  move : Hcm'.
  case : cm0 => [cm'||]; try by done.
  move => Hcm'.
  (*apply ExpandBranch_connection_inst; try by done.*)
  simpl in Hcm'.
  inversion Hcm'.
  simpl in Htm'.
  rewrite /texpr_match_ttree in Hpre.
  rewrite /texpr_match_ttree.
  move => v1 texpr1 ttree1.
  rewrite Htm'.
  move => Hte Htt.
  case Heq : (v1 == v).
  rewrite StructStateP.Lemmas.P.F.add_eq_o in Hte.
  rewrite StructStateP.Lemmas.P.F.add_eq_o in Htt.
  inversion Htt.
  rewrite -Hte.
  simpl.
  done.
  1,2: move /eqP : Heq => Heq.
  1,2: rewrite Heq.
  1,2: apply CEP.SE.eq_refl.

  rewrite StructStateP.Lemmas.add_neq_o in Hte.
  rewrite StructStateP.Lemmas.add_neq_o in Htt.
  apply Hpre with (v := v1); try by done.
  1,2:apply contra_not with (P := (v1 == v)).
  1,3:apply StructStateP.Lemmas_M.KeySetoid.
  1,2:apply elimF with (b := (v1 == v)); try by done.
  1,2:apply idP.
Qed.

Lemma expandBranch_connection_node_match :
  forall v ty cm cm0 tm tm' seq_result,
  texpr_match_ttree cm tm ->
  cm0 = snd (expandBranch_fun (Snode v ty) (Some seq_result) (OK cm)) -> 
  tm' = expandBranch_connection_tree (Snode v ty) tm -> 
  match cm0 with
  | OK cm' => texpr_match_ttree cm' tm'
  | _ => True
  end.
Proof.
  move => v ty cm cm0 tm tm' seq_result Hpre Hcm' Htm'.
  simpl in Hcm'.
  simpl in Htm'.
  rewrite Hcm' Htm' //.
  (*apply ExpandBranch_connection_node with (cm' := cm) (tm' := tm); try by done.*)
Qed.

Lemma expandBranch_connection_invalid_match :
  forall v cm cm0 tm tm' seq_result,
  CEP.mem v cm ->
  texpr_match_ttree cm tm ->
  cm0 = snd (expandBranch_fun (Sinvalid (Eid v)) (Some seq_result) (OK cm)) -> 
  tm' = expandBranch_connection_tree (Sinvalid (Eid v)) tm -> 
  match cm0 with
  | OK cm' => texpr_match_ttree cm' tm'
  | _ => True
  end.
Proof.
  move => v cm cm0 tm tm' seq_result.
  case : cm0 => [cm'||]; try by done.
  case Hc : (CEP.find v cm) => [t|].
  move => Hmem Hpre Hcm' Htm'.
  (*apply ExpandBranch_connection_invalid; try by done.*)
  simpl in Hcm'.
  rewrite Hc in Hcm'.
  inversion Hcm'.
  simpl in Htm'.
  rewrite /texpr_match_ttree in Hpre.
  rewrite /texpr_match_ttree.
  move => v1 texpr1 Hte.
  rewrite Htm'.
  case Heq : (v1 == v).
  rewrite StructStateP.Lemmas.P.F.add_eq_o in Hte.
  rewrite StructStateP.Lemmas.P.F.add_eq_o.
  simpl.
  rewrite -Hte //.
  1,2: move /eqP : Heq => Heq.
  1,2: rewrite Heq.
  1,2: apply CEP.SE.eq_refl.

  rewrite StructStateP.Lemmas.add_neq_o in Hte.
  rewrite StructStateP.Lemmas.add_neq_o.
  apply Hpre with (v := v1) (texpr1 := texpr1); try by done.

  1,2:apply contra_not with (P := (v1 == v)).
  1,3:apply StructStateP.Lemmas_M.KeySetoid.
  1,2:apply elimF with (b := (v1 == v)); try by done.
  1,2:apply idP.
  move => Hmem.
  apply StructStateP.Lemmas.find_none_not_mem in Hc. 
  rewrite Hc in Hmem; discriminate.
Qed.

Lemma expandBranch_connection_fcnct_match :
  forall v e cm cm0 tm tm' seq_result,
  CEP.mem v cm ->
  texpr_match_ttree cm tm ->
  cm0 = snd (expandBranch_fun (Sfcnct (Eid v) e) (Some seq_result) (OK cm)) -> 
  tm' = expandBranch_connection_tree (Sfcnct (Eid v) e) tm -> 
  match cm0 with
  | OK cm' => texpr_match_ttree cm' tm'
  | _ => True
  end.
Proof.
  move => v e cm cm0 tm tm' seq_result.
  case : cm0 => [cm'||]; try by done.
  case Hc : (CEP.find v cm) => [t|].
  move => Hmem Hpre Hcm' Htm'.
  (*apply ExpandBranch_connection_fcnct; try by done.*)
  simpl in Hcm'.
  rewrite Hc in Hcm'.
  inversion Hcm'.
  simpl in Htm'.
  rewrite /texpr_match_ttree in Hpre.
  rewrite /texpr_match_ttree.
  move => v1 texpr1 ttree1.
  rewrite Htm'.
  move => Hte Htt.
  case Heq : (v1 == v).
  rewrite StructStateP.Lemmas.P.F.add_eq_o in Hte.
  rewrite StructStateP.Lemmas.P.F.add_eq_o in Htt.
  inversion Htt.
  rewrite -Hte.
  simpl.
  done.
  1,2: move /eqP : Heq => Heq.
  1,2: rewrite Heq.
  1,2: apply CEP.SE.eq_refl.

  rewrite StructStateP.Lemmas.add_neq_o in Hte.
  rewrite StructStateP.Lemmas.add_neq_o in Htt.
  apply Hpre with (v := v1); try by done.

  1,2:apply contra_not with (P := (v1 == v)).
  1,3:apply StructStateP.Lemmas_M.KeySetoid.
  1,2:apply elimF with (b := (v1 == v)); try by done.
  1,2:apply idP.
  move => Hmem.
  apply StructStateP.Lemmas.find_none_not_mem in Hc. 
  rewrite Hc in Hmem; discriminate.
Qed.

Lemma Tchoice_no_none : forall c t1 t2, connection_tree2expr (T_choice c t1 t2) != None.
Proof.
  intros.
  case H1 : t1.
  case H2 : t2.

Admitted.

Lemma texpr_match_ttree_none s : forall seq_init cm cm' tm v, texpr_match_ttree cm tm -> CEP.find v (expandBranch_connection_trees s tm) = None -> 
(expandBranch_funs s seq_init (OK cm)).2 = OK cm' -> (CEP.find v cm') = None.
Proof.
  induction s.
  
Admitted.

Lemma ttree_match_texpr_none: forall s seq_init cm cm' tm v, texpr_match_ttree cm tm -> (expandBranch_funs s seq_init (OK cm)).2 = OK cm'
-> (CEP.find v cm') = None -> CEP.find v (expandBranch_connection_trees s tm) = None.
Proof.
  
Admitted.

Lemma expandBranch_connection_when_match' : 
  forall c s1 s2 cm cm' tm tm0 (seq_result : HiFP.hfstmt_seq),
  well_defined_stmt (Swhen c s1 s2) (OK cm) (Some seq_result) ->
  texpr_match_ttree cm tm ->
  match (expandBranch_funs s1 (Some seq_result) (OK cm)).2 with
  | OK cm1 => texpr_match_ttree cm1 (expandBranch_connection_trees s1 tm)
  | _ => True
  end ->
  match (expandBranch_funs s2 (expandBranch_funs s1 (Some seq_result) (OK cm)).1 (OK cm)).2 with
  | OK cm2 => texpr_match_ttree cm2 (expandBranch_connection_trees s2 tm)
  | _ => True 
  end -> 
  cm' = (snd (expandBranch_fun (Swhen c s1 s2) (Some seq_result) (OK cm))) ->
  tm0 = (expandBranch_connection_tree (Swhen c s1 s2) tm) ->
  match cm' with
  | OK cm0 => texpr_match_ttree cm0 tm0
  | _ => True
  end.
  
  (* texpr_match_ttree ((expandBranch_funs s1 (Some seq_result) (OK cm)).2) (expandBranch_connection_trees s1 tm) ->
  texpr_match_ttree ((expandBranch_funs s2 (expandBranch_funs s1 (Some seq_result) cm).1 (OK cm)).2) ((expandBranch_connection_trees s2 tm)) ->
  cm' = (snd (expandBranch_fun (Swhen c s1 s2) (Some seq_result) (OK cm))) ->
  tm0 = (expandBranch_connection_tree (Swhen c s1 s2) tm) ->
  match cm' with
  | OK cm0 => texpr_match_ttree cm0 tm0
  | _ => True
  end.*)
(*with texpr_match_tree_stmts : 
  forall ss cm cm0 tm tm0 (seq_result : HiFP.hfstmt_seq),
  texpr_match_ttree cm tm ->
  cm0 = (snd (expandBranch_funs ss (Some seq_result) cm)) ->
  tm0 = (expandBranch_connection_trees ss tm) ->
  texpr_match_ttree cm0 tm0*)
Proof.
  (*clear expandBranch_connection_when_match'.*)
  move => c s1 s2 cm cm0 tm tm0 seq_result Hwd Hpre Hm1 Hm2.
simpl in Hwd.
move : Hwd => [H1 H2].
case H : (expandBranch_funs s1 (Some seq_result) (OK cm)) => [s' m'].
case Hm' : m' => [cm'||].
rewrite H Hm' in Hm1.
simpl in Hm1.
case H' : (expandBranch_funs s2 (expandBranch_funs s1 (Some seq_result) (OK cm)).1 (OK cm)).2 => [cm2||].
rewrite H' in Hm2.

  (*case : cm0 => [cm'||]; try by done.  
  move => Hpre.
  case H1 : (expandBranch_funs s1 (Some seq_result) (OK cm)).2 => [cm1||]; try discriminate.
  move => Hm1.
  case H2 : (expandBranch_funs s2 (expandBranch_funs s1 (Some seq_result) (OK cm)).1 (OK cm)).2 => [cm2||]; try discriminate.
  move => Hm2 Hcm0 Htm0.*)
  move => Hcm0 Htm0.
  simpl in Hcm0.
  rewrite H Hm' in Hcm0.
  simpl in Hcm0.
  rewrite H in H'.
  rewrite H' in Hcm0.
  simpl in Hcm0.
  rewrite Hcm0.
  simpl in Htm0.
  rewrite /texpr_match_ttree.
  rewrite Htm0.
  clear Hcm0 Htm0.
  move => v texpr0 Hexpr0.
  rewrite StructStateP.Lemmas.map2_1bis in Hexpr0.
  rewrite StructStateP.Lemmas.map2_1bis.
  rewrite /texpr_match_ttree in Hm1.
  rewrite /texpr_match_ttree in Hm2.
  specialize Hm1 with (v := v) (texpr1 := CEP.find v cm'); try by done.
  specialize Hm2 with (v := v) (texpr1 := CEP.find v cm2); try by done.
  case Ht1' : (CEP.find v (expandBranch_connection_trees s1 tm)) => [ttree1|].
  rewrite Ht1' in Hm1.
  case Ht2' : (CEP.find v (expandBranch_connection_trees s2 tm)) => [ttree2|].
  rewrite Ht2' in Hm2.
  case Ht1 : ttree1 => [||e1|c1 tt1 ft1].
  - (* undefined *)
    (* case Hs' : s' => [seq_init'|].
    rewrite H Hs' Hm' in H1.
    move : H1 => [_ H1].
    rewrite /well_connected_m in H1.
    specialize H1 with (v := v).
    case Hf : (CEP.find v cm') => [y|].
    rewrite Hf in H1.
    case Hy : y => [||].
    rewrite Hy in H1; discriminate.
    apply Hm1 with (texpr1 := Some y)in Ht1';try done.
    rewrite Hy Ht1 in Ht1'.
    simpl in Ht1'.
    discriminate.
    apply Hm1 with (texpr1 := Some y)in Ht1'; try done.
    rewrite Hy Ht1 in Ht1'.
    simpl in Ht1'.
    discriminate.
    apply Hm1 with (texpr1 := None)in Ht1'; try done.
    rewrite Ht1 in Ht1'.
    simpl in Ht1'.
    discriminate.
    rewrite H Hs' in H1; done.*)
    admit.
  - (* T_invalid *)
  case Ht2 : ttree2 => [||e2|c2 tt2 ft2].
    - (* T_undefined *)
    admit.
    - (* T_invalid *)
    simpl.
    rewrite -Hexpr0.
    rewrite (Hm1 (Logic.eq_refl (CEP.find v cm'))).
    rewrite (Hm2 (Logic.eq_refl (CEP.find v cm2))).
    rewrite Ht1 Ht2.
    simpl.
    done.
    (* rewrite Ht1 Ht2 in Htree0.
    simpl in Htree0.
    inversion Htree0.
    specialize Hm1 with (v := v) (texpr1 := (CEP.find v cm')) (ttree1 := ttree1).
    rewrite Ht1 in Hm1.
    simpl in Hm1.
    specialize Hm2 with (v := v) (texpr1 := (CEP.find v cm2)) (ttree1 := ttree2).
    rewrite Ht2 in Hm2.
    simpl in Hm2.
    rewrite Hm1 in Hexpr0; try by done.
    rewrite Hm2 in Hexpr0; try by done.
    rewrite -Ht2 //.
    rewrite -Ht1 //. *)
    - (* T_expr *)
    rewrite Ht1 Ht2 in Htree0.
    simpl in Htree0.
    inversion Htree0.
    specialize Hm1 with (v := v) (texpr1 := (CEP.find v cm')) (ttree1 := ttree1).
    rewrite Ht1 in Hm1.
    simpl in Hm1.
    specialize Hm2 with (v := v) (texpr1 := (CEP.find v cm2)) (ttree1 := ttree2).
    rewrite Ht2 in Hm2.
    simpl in Hm2.
    rewrite Hm1 in Hexpr0; try by done.
    rewrite Hm2 in Hexpr0; try by done.
    rewrite -Ht2 //.
    rewrite -Ht1 //.
    - (* T_choice *)
    rewrite Ht1 Ht2 in Htree0.
    simpl in Htree0.
    inversion Htree0.
    specialize Hm1 with (v := v) (texpr1 := (CEP.find v cm')) (ttree1 := ttree1).
    rewrite Ht1 in Hm1.
    simpl in Hm1.
    specialize Hm2 with (v := v) (texpr1 := (CEP.find v cm2)) (ttree1 := ttree2).
    rewrite Ht2 in Hm2.
    case Hb2: (connection_tree2expr (T_choice c2 tt2 ft2)) => [texpr|].
    case Htexpr: texpr => [||te]; try by done.
      - (* undefined *)
      admit.
      - (* invalid *)
      rewrite Htexpr in Hb2.
      rewrite Hb2 in Hm2.
      rewrite Hm1 in Hexpr0; try by done.
      rewrite Hm2 in Hexpr0; try by done.
      rewrite -Ht2 //.
      rewrite -Ht1 //.
      - (* expr *)
      rewrite Htexpr in Hb2.
      rewrite Hb2 in Hm2.
      rewrite Hm1 in Hexpr0; try by done.
      rewrite Hm2 in Hexpr0; try by done.
      rewrite -Ht2 //.
      rewrite -Ht1 //.
      - (* T_choice 不全是none *)
      specialize Tchoice_no_none with (c := c2) (t1 := tt2) (t2 := ft2).
      move => Ht.
      rewrite Hb2 in Ht; discriminate.
  - (* T_expr *)
  case Ht2 : ttree2 => [||e2|c2 tt2 ft2].
    - (* T_undefined *)
    admit.
    - (* T_invalid *)
    rewrite Ht1 Ht2 in Htree0.
    simpl in Htree0.
    inversion Htree0.
    specialize Hm1 with (v := v) (texpr1 := (CEP.find v cm')) (ttree1 := ttree1).
    rewrite Ht1 in Hm1.
    simpl in Hm1.
    specialize Hm2 with (v := v) (texpr1 := (CEP.find v cm2)) (ttree1 := ttree2).
    rewrite Ht2 in Hm2.
    simpl in Hm2.
    rewrite Hm1 in Hexpr0; try by done.
    rewrite Hm2 in Hexpr0; try by done.
    rewrite -Ht2 //.
    rewrite -Ht1 //.
    - (* T_expr *)
    rewrite Ht1 Ht2 in Htree0.
    simpl in Htree0.
    inversion Htree0.
    specialize Hm1 with (v := v) (texpr1 := (CEP.find v cm')) (ttree1 := ttree1).
    rewrite Ht1 in Hm1.
    simpl in Hm1.
    specialize Hm2 with (v := v) (texpr1 := (CEP.find v cm2)) (ttree1 := ttree2).
    rewrite Ht2 in Hm2.
    simpl in Hm2.
    rewrite Hm1 in Hexpr0; try by done.
    rewrite Hm2 in Hexpr0; try by done.
    rewrite -Ht2 //.
    rewrite -Ht1 //.
    - (* T_choice *)
    rewrite Ht1 Ht2 in Htree0.
    simpl in Htree0.
    inversion Htree0.
    specialize Hm1 with (v := v) (texpr1 := (CEP.find v cm')) (ttree1 := ttree1).
    rewrite Ht1 in Hm1.
    simpl in Hm1.
    specialize Hm2 with (v := v) (texpr1 := (CEP.find v cm2)) (ttree1 := ttree2).
    rewrite Ht2 in Hm2.
    case Hb2: (connection_tree2expr (T_choice c2 tt2 ft2)) => [texpr|]; try by done.
    case Htexpr: texpr => [||te]; try by done.
      - (* undefined *)
      admit.
      - (* invalid *)
      rewrite Htexpr in Hb2.
      rewrite Hb2 in Hm2.
      rewrite Hm1 in Hexpr0; try by done.
      rewrite Hm2 in Hexpr0; try by done.
      simpl in Hexpr0.
      unfold connection_tree2expr; fold connection_tree2expr.
      simpl in Hb2.
      rewrite Hb2.
      rewrite -Hexpr0 //.
      rewrite -Ht2 //.
      rewrite -Ht1 //.
      - (* expr *)
      rewrite Htexpr in Hb2.
      rewrite Hb2 in Hm2.
      rewrite Hm1 in Hexpr0; try by done.
      rewrite Hm2 in Hexpr0; try by done.
      simpl in Hexpr0.
      unfold connection_tree2expr; fold connection_tree2expr.
      simpl in Hb2.
      rewrite Hb2.
      rewrite -Hexpr0 //.
      rewrite -Ht2 //.
      rewrite -Ht1 //.
      - admit.
  - (* T_choice *)
  case Hb1: (connection_tree2expr (T_choice c1 tt1 ft1)) => [texpr|]; try by done.
    case Htexpr1: texpr => [||te]; try by done.
    rewrite Htexpr1 in Hb1.
    admit. (* undefined *)
    - (* invalid *)
    case Ht2 : ttree2 => [||e2|c2 tt2 ft2].
      - (* T_undefined *)
      admit.
      - (* T_invalid *)
      rewrite Htexpr1 in Hb1.
      rewrite Ht1 Ht2 in Htree0.
      simpl in Htree0.
      inversion Htree0.
      rewrite Hb1.
      specialize Hm1 with (v := v) (texpr1 := (CEP.find v cm')) (ttree1 := ttree1).
      rewrite Ht1 Hb1 in Hm1.
      specialize Hm2 with (v := v) (texpr1 := (CEP.find v cm2)) (ttree1 := ttree2).
      rewrite Ht2 in Hm2.
      simpl in Hm2.
      rewrite Hm1 in Hexpr0; try by done.
      rewrite Hm2 in Hexpr0; try by done.
      rewrite -Ht2 //.
      rewrite -Ht1 //.
      - (* T_expr *)
      rewrite Htexpr1 in Hb1.
      rewrite Ht1 Ht2 in Htree0.
      simpl in Htree0.
      inversion Htree0.
      specialize Hm1 with (v := v) (texpr1 := (CEP.find v cm')) (ttree1 := ttree1).
      rewrite Ht1 Hb1 in Hm1.
      specialize Hm2 with (v := v) (texpr1 := (CEP.find v cm2)) (ttree1 := ttree2).
      rewrite Ht2 in Hm2.
      simpl in Hm2.
      rewrite Hm1 in Hexpr0; try by done.
      rewrite Hm2 in Hexpr0; try by done.
      simpl in Hexpr0.
      simpl in Hb1.
      simpl.
      rewrite Hb1.
      rewrite -Hexpr0 //.
      rewrite -Ht2 //.
      rewrite -Ht1 //.
      - (* T_choice *)
      case Hb2: (connection_tree2expr (T_choice c2 tt2 ft2)) => [texpr'|]; try by done.
      case Htexpr2: texpr' => [||te']; try by done.
      rewrite Htexpr2 in Hb2.
        (* undefined *)
        admit.
        (* invalid *)
        rewrite Htexpr1 in Hb1.
        rewrite Htexpr2 in Hb2.
        rewrite Ht1 Ht2 in Htree0.
        simpl in Htree0.
        inversion Htree0.
        specialize Hm1 with (v := v) (texpr1 := (CEP.find v cm')) (ttree1 := ttree1).
        rewrite Ht1 Hb1 in Hm1.
        specialize Hm2 with (v := v) (texpr1 := (CEP.find v cm2)) (ttree1 := ttree2).
        rewrite Ht2 in Hm2.
        rewrite Hm1 in Hexpr0; try by done.
        rewrite Hm2 in Hexpr0; try by done.
        rewrite Hb2 in Hexpr0.
        simpl in Hexpr0.
        simpl in Hb1.
        simpl in Hb2.
        simpl.
        rewrite Hb1 Hb2.
        rewrite -Hexpr0 //.
        rewrite -Ht2 //.
        rewrite -Ht1 //.
        (* expr *)
        rewrite Htexpr1 in Hb1.
        rewrite Htexpr2 in Hb2.
        rewrite Ht1 Ht2 in Htree0.
        simpl in Htree0.
        inversion Htree0.
        specialize Hm1 with (v := v) (texpr1 := (CEP.find v cm')) (ttree1 := ttree1).
        rewrite Ht1 Hb1 in Hm1.
        specialize Hm2 with (v := v) (texpr1 := (CEP.find v cm2)) (ttree1 := ttree2).
        rewrite Ht2 in Hm2.
        rewrite Hm1 in Hexpr0; try by done.
        rewrite Hm2 in Hexpr0; try by done.
        rewrite Hb2 in Hexpr0.
        simpl in Hexpr0.
        simpl in Hb1.
        simpl in Hb2.
        simpl.
        rewrite Hb1 Hb2.
        rewrite -Hexpr0 //.
        rewrite -Ht2 //.
        rewrite -Ht1 //.
        (* None *)
        admit.
    - (* expr *)
    case Ht2 : ttree2 => [||e2|c2 tt2 ft2].
      - (* T_undefined *)
      admit.
      - (* T_invalid *)
      rewrite Htexpr1 in Hb1.
      rewrite Ht1 Ht2 in Htree0.
      simpl in Htree0.
      inversion Htree0.
      rewrite Hb1.
      specialize Hm1 with (v := v) (texpr1 := (CEP.find v cm')) (ttree1 := ttree1).
      rewrite Ht1 Hb1 in Hm1.
      specialize Hm2 with (v := v) (texpr1 := (CEP.find v cm2)) (ttree1 := ttree2).
      rewrite Ht2 in Hm2.
      simpl in Hm2.
      rewrite Hm1 in Hexpr0; try by done.
      rewrite Hm2 in Hexpr0; try by done.
      rewrite -Ht2 //.
      rewrite -Ht1 //.
      - (* T_expr *)
      rewrite Htexpr1 in Hb1.
      rewrite Ht1 Ht2 in Htree0.
      simpl in Htree0.
      inversion Htree0.
      specialize Hm1 with (v := v) (texpr1 := (CEP.find v cm')) (ttree1 := ttree1).
      rewrite Ht1 Hb1 in Hm1.
      specialize Hm2 with (v := v) (texpr1 := (CEP.find v cm2)) (ttree1 := ttree2).
      rewrite Ht2 in Hm2.
      simpl in Hm2.
      rewrite Hm1 in Hexpr0; try by done.
      rewrite Hm2 in Hexpr0; try by done.
      simpl in Hexpr0.
      simpl in Hb1.
      simpl.
      rewrite Hb1.
      rewrite -Hexpr0 //.
      rewrite -Ht2 //.
      rewrite -Ht1 //.
      - (* T_choice *)
      case Hb2: (connection_tree2expr (T_choice c2 tt2 ft2)) => [texpr'|]; try by done.
      case Htexpr2: texpr' => [||te']; try by done.
      rewrite Htexpr2 in Hb2.
        (* undefined *)
        admit.
        (* invalid *)
        rewrite Htexpr1 in Hb1.
        rewrite Htexpr2 in Hb2.
        rewrite Ht1 Ht2 in Htree0.
        simpl in Htree0.
        inversion Htree0.
        specialize Hm1 with (v := v) (texpr1 := (CEP.find v cm')) (ttree1 := ttree1).
        rewrite Ht1 Hb1 in Hm1.
        specialize Hm2 with (v := v) (texpr1 := (CEP.find v cm2)) (ttree1 := ttree2).
        rewrite Ht2 in Hm2.
        rewrite Hm1 in Hexpr0; try by done.
        rewrite Hm2 in Hexpr0; try by done.
        rewrite Hb2 in Hexpr0.
        simpl in Hexpr0.
        simpl in Hb1.
        simpl in Hb2.
        simpl.
        rewrite Hb1 Hb2.
        rewrite -Hexpr0 //.
        rewrite -Ht2 //.
        rewrite -Ht1 //.
        (* expr *)
        rewrite Htexpr1 in Hb1.
        rewrite Htexpr2 in Hb2.
        rewrite Ht1 Ht2 in Htree0.
        simpl in Htree0.
        inversion Htree0.
        specialize Hm1 with (v := v) (texpr1 := (CEP.find v cm')) (ttree1 := ttree1).
        rewrite Ht1 Hb1 in Hm1.
        specialize Hm2 with (v := v) (texpr1 := (CEP.find v cm2)) (ttree1 := ttree2).
        rewrite Ht2 in Hm2.
        rewrite Hm1 in Hexpr0; try by done.
        rewrite Hm2 in Hexpr0; try by done.
        rewrite Hb2 in Hexpr0.
        simpl in Hexpr0.
        simpl in Hb1.
        simpl in Hb2.
        simpl.
        rewrite Hb1 Hb2.
        rewrite -Hexpr0 //.
        rewrite -Ht2 //.
        rewrite -Ht1 //.
        (* None *)
        admit.
  admit.
  (* 2 为none *)
  rewrite Ht1' Ht2' in Htree0.
  simpl in Htree0.
  assert (Htree0' : ttree1 = ttree0).
  case Htt1 : ttree1; rewrite Htt1 in Htree0.
  inversion Htree0; reflexivity.
  inversion Htree0; reflexivity.
  inversion Htree0; reflexivity.
  inversion Htree0; reflexivity.
  clear Htree0.
  rewrite -Htree0'.
  case Hfind1 : (CEP.find v cm') => [texpr1|].
  apply Hm1 with (texpr1 := Some texpr1) in Ht1'; try done.
  assert (Htexpr01 : texpr0 = Some texpr1).

  (*forall s seq_init, texpr_match_ttree cm tm -> CEP.find v (expandBranch_connection_trees s tm) = None -> 
  (expandBranch_funs s seq_init (OK cm)).2 = OK cm2 -> (CEP.find v cm2) = None. *)

  assert (Hfind2 : (CEP.find v cm2) = None).
  admit.
  rewrite Hfind1 Hfind2 in Hexpr0.
  simpl in Hexpr0.
  case H1' : texpr1; rewrite H1' in Hexpr0.
  1,2,3: rewrite -Hexpr0 //.
  rewrite Htexpr01 //.

  (*forall s seq_init, texpr_match_ttree cm tm -> (expandBranch_funs s seq_init (OK cm)).2 = OK cm2 
  -> (CEP.find v cm2) = None -> CEP.find v (expandBranch_connection_trees s tm) = None. *)
  admit.

  (* 1 为none *)
  assert (Hfind1 : (CEP.find v cm') = None).
  admit.

  admit.
  1,2: simpl.
  1,2: done.

rewrite H' in H2; done.
rewrite H' in H2; done.
case Hs' : s' => [seq_init'|].
rewrite H Hs' Hm' in H1; done.
rewrite H Hs' in H1; done.
case Hs' : s' => [seq_init'|].
rewrite H Hs' Hm' in H1; done.
rewrite H Hs' in H1; done.
  Admitted.


Lemma expandBranch_connection_stmt_match (s : HiFP.hfstmt) :
  forall cm cm0 tm tm' (seq_result : HiFP.hfstmt_seq),
  well_defined_stmt s (OK cm) (Some seq_result) ->
  texpr_match_ttree cm tm ->
  cm0 = snd (expandBranch_fun s (Some seq_result) (OK cm)) ->
  tm' = expandBranch_connection_tree s tm ->
  match cm0 with
  | OK cm' => texpr_match_ttree cm' tm'
  | _ => True
  end
with expandBranch_connection_stmts_match (ss : HiFP.hfstmt_seq) :
  forall cm cm0 tm tm' (seq_result : HiFP.hfstmt_seq),
  well_defined_stmts ss (OK cm) (Some seq_result) ->
  texpr_match_ttree cm tm ->
  cm0 = snd (expandBranch_funs ss (Some seq_result) (OK cm)) ->
  tm' = expandBranch_connection_trees ss tm ->
  match cm0 with
  | OK cm' => texpr_match_ttree cm' tm'
  | _ => True
  end.
Proof.
  clear expandBranch_connection_stmt_match.
  case Hs : s => [|v t|||||v e|v|c s1 s2]; try done.
  - move => cm cm' tm tm' seq_result Hwd Hpre Hcm' Htm'.
    simpl in Hcm'.
    simpl in Htm'.
    rewrite Hcm' Htm' //.
  - move => cm cm' tm tm' seq_result Hwd.
    apply expandBranch_connection_wire_match.
  - move => cm cm' tm tm' seq_result Hwd.
    apply expandBranch_connection_reg_match.
  - move => cm cm' tm tm' seq_result Hwd.
    apply expandBranch_connection_mem_match.
  - move => cm cm' tm tm' seq_result Hwd.
    apply expandBranch_connection_inst_match.
  - move => cm cm' tm tm' seq_result Hwd.
    apply expandBranch_connection_node_match.
  - move => cm cm' tm tm' seq_result Hwd.
    simpl in Hwd.
    move : Hs Hwd. 
    case Hv:v => [v0|||]; try done.
    move => Hs. 
    apply expandBranch_connection_fcnct_match.
  - move => cm cm' tm tm' seq_result Hwd.
    simpl in Hwd.
    move : Hs Hwd. 
    case Hv:v => [v0|||]; try done.
    move => Hs. 
    apply expandBranch_connection_invalid_match.
    - (* when *)
  move => cm cm' tm tm' seq_result Hwd Hpre Hcm' Htm'.
  apply expandBranch_connection_when_match' with (c := c) (s1 := s1) (s2 := s2) (cm := cm) (tm := tm) (seq_result := seq_result); try by done.
  simpl in Hwd.
  move : Hwd => [H1 H2].
  apply expandBranch_connection_stmts_match with (ss := s1) (cm := cm) (tm := tm) (seq_result := seq_result); try by done.
  case H : (expandBranch_funs s1 (Some seq_result) (OK cm)) => [s' m'].
  case Hs' : s' => [seq_init'|].
  case Hm' : m' => [cm1||].
  rewrite Hs' Hm' in H.
  rewrite H in H1. 
  move : H1 => [H1 _]; done.
  rewrite Hs' Hm' in H.
  rewrite H in H1; done.
  rewrite Hs' Hm' in H.
  rewrite H in H1; done.
  rewrite H Hs' in H1; done.
  simpl in Hwd.
  move : Hwd => [H1 H2].
  case H : (expandBranch_funs s1 (Some seq_result) (OK cm)) => [s' m'].
  case Hs' : s' => [seq_init'|].
  apply expandBranch_connection_stmts_match with (ss := s2) (cm := cm) (tm := tm) (seq_result := seq_init'); try by done.
  rewrite H Hs' in H2.
  simpl in H2.
  case H' : (expandBranch_funs s2 (Some seq_init') (OK cm)).2 => [cm2||].
  rewrite H' in H2.
  move : H2 => [H2 _]; done.
  rewrite H' in H2; done.
  rewrite H' in H2; done.
  rewrite H Hs' in H1; done.
  clear expandBranch_connection_stmts_match.
  induction ss.
  - move => cm cm' tm tm' seq_result Hwd Hpre Hcm' Htm'.
    simpl in Hcm'.
    simpl in Htm'.
    rewrite Hcm' Htm' //.
  - move => cm cm' tm tm' seq_result Hwd Hpre Hcm' Htm'.
    simpl in Hcm'.
    simpl in Htm'.
    simpl in Hwd.
    case H : (expandBranch_fun h (Some seq_result) (OK cm)) => [s' m'].
    case Hs' : s' => [seq_init'|].
    case Hm' : m' => [cm1||].
    apply IHss with (cm := cm1) (tm := (expandBranch_connection_tree h tm)) (seq_result := seq_init'); try by done.
    move : Hwd => [H0 H1].
    move : H1 => [H1 H2].
    rewrite H Hs' Hm' in H2; done.
    specialize expandBranch_connection_stmt_match with (s := h) (cm := cm) (cm0 := m') (tm := tm) (tm' := expandBranch_connection_tree h tm) (seq_result := seq_result); try by done.
    move : Hwd => [H0 H1].
    move : H1 => [H1 H2].
    apply expandBranch_connection_stmt_match in H0; try done.
    rewrite Hm' in H0; done.
    rewrite H; done.
    rewrite H Hs' Hm' in Hcm'; done.
    move : Hwd => [H0 H1].
    move : H1 => [H1 H2].
    rewrite H Hs' Hm' in H1; done.
    move : Hwd => [H0 H1].
    move : H1 => [H1 H2].
    rewrite H Hs' Hm' in H1; done.
    move : Hwd => [H0 H1].
    move : H1 => [H1 H2].
    rewrite H Hs' in H1; done.
Qed.

Lemma expandBranch_good_answer s :
  forall cm seq_init, well_defined_stmt s (OK cm) seq_init -> exists cm', (expandBranch_fun s seq_init (OK cm)).2 = OK cm'.
Proof.
  case Hs : s => [|v t|v r|v m|v v1|v n|v e|v|c s1 s2]; try done.
  - move => cm seq_result Hwd.
    simpl.
    exists cm; done.
  - move => cm seq_result Hwd.
    simpl.
    exists (CEP.add v D_undefined cm); done.
  admit.
  admit.
  admit.
  admit.
  - move => cm seq_result Hwd.
    simpl.
    admit.
  admit.
  - move => cm seq_result Hwd.
    simpl.
    simpl in Hwd.



Admitted.

Lemma expandBranchs_good_answer ss :
  forall cm seq_init, well_defined_stmts ss cm seq_init -> exists cm', (expandBranch_funs ss seq_init cm).2 = OK cm'.
Proof.
  
Admitted.

Definition well_typed_s (s : HiFP.hfstmt) : Prop :=
  match s with
  | Sfcnct (Eid v0) _ => True
  | Sinvalid (Eid v0) => True
  | Sfcnct _ _ => False
  | Sinvalid _ => False
  | _ => True
  end.

Lemma expandBranch_egty s :
  forall cm seq_init, ~well_typed_s s -> (expandBranch_fun s seq_init cm).2 = Egtyp .
Proof.
  
Admitted.

Fixpoint repeatdef_ss (ss : HiFP.hfstmt_seq) : Prop :=
  match ss with
  | Qnil => False
  | Qcons s st => match s with
                  | Swire _ _ 
                  | Smem _ _ 
                  | Sinst _ _ 
                  | Sreg _ _
                  | Snode _ _ => Qin s st
                  | Swhen _ s1 s2 => repeatdef_ss s1 \/ repeatdef_ss s2
                  | _ => False
                  end
  end.

Lemma expandBranch_repeat ss :
  forall cm seq_init, repeatdef_ss ss -> (expandBranch_funs ss seq_init cm).1 = None .
Proof.
  
Admitted.

Lemma expandBranch_undefined ss : (* error怎么给？ *)
  forall seq_init cm cm', (expandBranch_funs ss seq_init cm).2 = OK cm' -> exists v, CEP.find v cm' = Some D_undefined -> expandwhens_ss (expandBranch_funs ss seq_init cm).1 (expandBranch_funs ss seq_init cm).2 = Eundefine.
Proof.

Admitted.

(* ? *)
Lemma expandBranch_undeclared s :
  forall cm seq_init,被连接到在声明前-> (expandBranch_funs ss seq_init cm).2 = Eundeclared .
Proof.
  
Admitted.


precondition: 
所有v是gtyp, 不会return type error 
所有define在cnct前
所有没有未cnct的

End ExpandWhens.
