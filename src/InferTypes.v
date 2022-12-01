From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq ssrfun.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.
From firrtl Require Import Firrtl Env HiEnv.


From firrtl Require Import HiFirrtl.

  (** Pass InferType *)
Section InferTypeS.
  (* infer type according to a statement *)

  Inductive inferType_stmt : HiF.hfstmt -> CE.env -> CE.env -> Prop :=
  | Infertype_wire v t ce ce' :
      HiF.new_comp_name v ->
      (* CE.find v ce = None -> *)
      CE.find v ce' = Some (HiF.aggr_typ t, Wire) ->
      inferType_stmt (Swire v t) ce ce'
  | Infertype_reg v r ce ce' :
      HiF.new_comp_name v ->
      (* CE.find v ce = None -> *)
      CE.find v ce' = Some (HiF.reg_typ r, Register) ->
      inferType_stmt (Sreg v r) ce ce'
  | Infertype_inst v1 v2 ce ce' :
      HiF.new_comp_name v1 ->
      (* CE.find v1 ce = None -> *)
      ~~ (v1 == v2) ->
      (* CE.find v2 ce = Some t -> *)
      CE.find v1 ce' = Some (fst (CE.vtyp v2 ce), Instanceof) ->
      inferType_stmt (Sinst v1 v2) ce ce'
  | Infertype_node v e ce ce' :
      HiF.new_comp_name v ->
      (* CE.find v ce = None -> *)
      (* ~~ fexpr_has_v v e -> *)
      HiF.type_of_hfexpr e ce = HiF.type_of_hfexpr e ce' ->
      CE.find v ce' = Some (HiF.aggr_typ (HiF.type_of_hfexpr e ce), Node) ->
      inferType_stmt (Snode v e) ce ce'
  | Infertype_mem v m ce ce' :
      HiF.new_comp_name v ->
      (* CE.find v ce = None -> *)
      CE.find v ce' = Some (Mem_typ m, Memory) ->
      inferType_stmt (Smem v m) ce ce'
  | Infertype_invalid v ce :
      inferType_stmt (Sinvalid v) ce ce
  | Infertype_sfcnct r e ce :
      forall t t' c,
      CE.find (HiF.base_ref r) ce = Some (t, c) /\
      HiF.type_of_hfexpr e ce = t' /\
      HiF.ftype_equiv (type_of_cmpnttyp t) t' ->
      inferType_stmt (Sfcnct r e) ce ce
  | Infertype_spcnct r e ce :
      forall t t' c,
      CE.find (HiF.base_ref r) ce = Some (t, c) /\
      HiF.type_of_hfexpr e ce = t' /\
      HiF.ftype_weak_equiv (type_of_cmpnttyp t) t' ->
      inferType_stmt (Spcnct r e) ce ce
  | Infertype_sskip ce :
      inferType_stmt (HiF.sskip) ce ce
  | Infertype_swhen e s1 s2 ce ce' ce'' :
      inferType_stmts s1 ce ce' ->
      inferType_stmts s2 ce' ce'' ->
      inferType_stmt (Swhen e s1 s2) ce ce''
                     
  with inferType_stmts : HiF.hfstmt_seq -> CE.env -> CE.env -> Prop :=
  | Infertype_stmts_nil ce :
      inferType_stmts HiF.qnil ce ce
  | Infertype_stmts_con s ss ce ce' ce'' :
      inferType_stmt s ce ce' ->
      inferType_stmts ss ce' ce'' ->
      inferType_stmts (Qcons s ss) ce ce''.

   Definition find_unknown r (ce : CE.env) :=
     match (CE.find r ce) with
     | Some (Unknown_typ, _) => true
     | None => true
     | _ => false
     end.

  (*Inductive inferType_stmts : hfstmt_seq -> cenv -> cenv -> Prop :=
  | Infertype_stmts_know ss ce ce' :
      (exists v,
                 ~~ find_unknown v ce') ->
      inferType_stmts (ss) ce ce'.*)

  (* infer type according to ports declaration *)
  Inductive inferType_port : HiF.hfport -> CE.env -> CE.env -> Prop :=
  | Infertype_inport v t ce ce' :
      CE.find v ce' = Some (HiF.aggr_typ t, In_port) ->
      inferType_port (Finput v t) ce ce'
  | Infertype_outport v t ce ce' :
      CE.find v ce' = Some (HiF.aggr_typ t, Out_port) ->
      inferType_port (Foutput v t) ce ce'.

  Inductive inferType_ports : seq HiF.hfport -> CE.env -> CE.env -> Prop :=
  | infertype_ports_nil ce :
      inferType_ports [::] ce ce
  | infertype_ports_con s ss ce ce' ce'' :
      inferType_port s ce ce' ->
      inferType_ports ss ce' ce'' ->
      inferType_ports (s::ss) ce ce''.

  Fixpoint inst_type_of_ports (ps : seq HiF.hfport) :=
    match ps with
    | nil => Fnil
    | p :: ps => match p with
                   | Finput v t => Fflips v Flipped t (inst_type_of_ports ps)
                   | Foutput v t => Fflips v Nflip t (inst_type_of_ports ps)
                   end
    end.

  Definition inst_type_of_ports' ps :=
    let pt := inst_type_of_ports ps in
    match pt with
    | Fnil => HiF.def_ftype
    | ps => Btyp ps
    end.

  (* infer type of module according to ports declaration *)
  Inductive inferType_module : HiF.hfmodule -> CE.env -> CE.env -> Prop :=
  | infertype_inmod vm ps ss ce ce' ce1 ce2 :
      CE.find vm ce' = Some (HiF.aggr_typ (inst_type_of_ports' ps), Fmodule) ->
      inferType_ports ps ce' ce1 -> inferType_stmts ss ce1 ce2 ->
      inferType_module (FInmod vm ps ss) ce ce2
  | infertype_exmod vm ps ss ce ce' :
      CE.find vm ce' = Some (HiF.aggr_typ (inst_type_of_ports' ps), Fmodule) ->
      inferType_module (FExmod vm ps ss) ce ce'.

  Inductive inferType_modules : seq HiF.hfmodule -> CE.env -> CE.env -> Prop :=
  | infertype_modules_nil ce :
      inferType_modules [::] ce ce
  | infertype_modules_con s ss ce ce' ce'' :
      inferType_module s ce ce' ->
      inferType_modules ss ce' ce'' ->
      inferType_modules (s::ss) ce ce''.

  Fixpoint inferType_stmt_fun (st : HiF.hfstmt) (ce : CE.env) : CE.env :=
    match st with
    | Snode v e => CE.add v (HiF.aggr_typ (HiF.type_of_hfexpr e ce), Node) ce
    | Sinst v1 v2 => CE.add v1 (fst (CE.vtyp v2 ce), Instanceof) ce
    | Sreg v r => CE.add v (Reg_typ r, Register) ce
    | Smem v m => CE.add v (HiF.mem_typ m, Memory) ce
    | Swire v t => CE.add v (HiF.aggr_typ t, Wire) ce
    | Swhen _ sts_true sts_false => inferType_stmts_fun sts_false (inferType_stmts_fun sts_true ce)
    | Sfcnct _ _
    | Spcnct _ _
    | Sinvalid _
    (* | Sstop _ _ _ *)
    | Sskip => ce
    end

  with inferType_stmts_fun (sts : HiF.hfstmt_seq) (ce : CE.env) : CE.env :=
    match sts with
    | Qnil => ce
    | Qcons s stl => inferType_stmts_fun stl (inferType_stmt_fun s ce)
    end.


  Definition inferType_port_fun p ce :=
    match p with
    | Finput v t => CE.add v (HiF.aggr_typ t, In_port) ce
    | Foutput v t => CE.add v (HiF.aggr_typ t, Out_port) ce
    end.

  Fixpoint inferType_ports_fun ps ce := (*fold_right inferType_port_fun ps ce.*)
    match ps with
    | nil => ce
    | s :: stl => inferType_ports_fun stl (inferType_port_fun s ce)
    end.

  Definition inferType_module_fun m ce :=
    match m with
    | FInmod v ps ss => inferType_stmts_fun ss (inferType_ports_fun ps
    (CE.add v (HiF.aggr_typ (inst_type_of_ports' ps), Fmodule) ce))
    | FExmod v ps ss => CE.add v (HiF.aggr_typ (inst_type_of_ports' ps), Fmodule) ce
    end.

  Fixpoint inferType_modules_fun ms ce := (*fold_right inferType_module_fun ms ce.*)
    match ms with
    | nil => ce
    | s :: stl => inferType_modules_fun stl (inferType_module_fun s ce)
    end.

  Lemma ftype_equiv_ident :
    forall t , HiF.ftype_equiv t t
  with ffield_equiv_ident :
      forall(f:ffield),
      HiF.fbtyp_equiv f f.
  Proof.
    elim; rewrite /=; intros. elim f; done.
      rewrite eq_refl H//.
      rewrite ffield_equiv_ident//.

      elim; intros. rewrite /=; done.
      rewrite /=.
      rewrite eq_refl.
      simpl.
      rewrite H.
      rewrite ftype_equiv_ident.
      simpl.
      case f; done.
     Qed.

  Lemma ftype_weak_equiv_ident :
  forall t ,
      HiF.ftype_weak_equiv t t.
  Proof.
    move => t.
    rewrite /HiF.ftype_weak_equiv.
    induction t.
    rewrite /HiF.fgtyp_equiv.
    case f;try done.

    rewrite /HiF.ftype_equiv.
    induction t.
    apply IHt.
    rewrite eq_refl.
    try done.
    admit.

    rewrite /HiF.fbtyp_weak_equiv.
    case f;try done.
    intros.
    case f2.


    Admitted.

  (****** TODO. For KY ******)
  (** Begin **)

  Lemma inferType_snode_sem_conform :
    forall v e ce0 ,
      HiF.new_comp_name v ->
      HiF.type_of_hfexpr e ce0 = HiF.type_of_hfexpr e (inferType_stmt_fun (Snode v e) ce0) ->
      inferType_stmt (HiF.snode v e) ce0 (inferType_stmt_fun (HiF.snode v e) ce0).
  Proof.
    intros. apply Infertype_node; try done.
    rewrite /inferType_stmt_fun (HiF.CELemmas.add_eq_o _ _ (eq_refl v)) //.
  Qed.

  Lemma inferType_sreg_sem_conform :
    forall v r ce0 ,
      HiF.new_comp_name v ->
      inferType_stmt (HiF.sreg v r) ce0 (inferType_stmt_fun (HiF.sreg v r) ce0).
  Proof.
    intros. apply Infertype_reg. try done.
    rewrite /inferType_stmt_fun /CE.add_fst (HiF.CELemmas.add_eq_o _ _ (eq_refl v)) //.
  Qed.

  Lemma inferType_smem_sem_conform :
    forall v r ce0 ,
      HiF.new_comp_name v ->
      inferType_stmt (HiF.smem v r) ce0 (inferType_stmt_fun (HiF.smem v r) ce0).
  Proof.
    intros. apply Infertype_mem. try done.
    rewrite /inferType_stmt_fun /CE.add_fst (HiF.CELemmas.add_eq_o _ _ (eq_refl v)) //.
  Qed.

  Lemma inferType_sinvalid_sem_conform :
  forall v ce0 ,
      inferType_stmt (HiF.sinvalid v) ce0 (inferType_stmt_fun (HiF.sinvalid v) ce0).
  Proof.
    intros. apply Infertype_invalid.
  Qed.

  Lemma inferType_swire_sem_conform :
    forall v r ce0 ,
      HiF.new_comp_name v ->
      inferType_stmt (HiF.swire v r) ce0 (inferType_stmt_fun (HiF.swire v r) ce0).
  Proof.
    intros. apply Infertype_wire. try done.
    rewrite /inferType_stmt_fun.
    rewrite (HiF.CELemmas.add_eq_o _ _ (eq_refl v)) //.
  Qed.

  Lemma inferType_sinst_sem_conform :
    forall v1 v2 ce0 ,
      HiF.new_comp_name v1 ->
      v1 != v2 ->
      (*CE.find v2 ce0 = Some t ->*)
      inferType_stmt (Sinst v1 v2) ce0 (inferType_stmt_fun (Sinst v1 v2) ce0).
  Proof.
    intros. apply Infertype_inst ; try done.
    rewrite /inferType_stmt_fun.
    rewrite (HiF.CELemmas.add_eq_o _ _ (eq_refl v1))//. (* rewrite (CE.find_some_vtyp H1)//.  *)
  Qed.

  Lemma inferType_sfcnct_sem_conform :
    forall v1 t c e ce0 ,
      CE.find (HiF.base_ref v1) ce0 = Some (t, c) ->
      type_of_cmpnttyp t = HiF.type_of_hfexpr e ce0 ->
      inferType_stmt (Sfcnct v1 e) ce0 (inferType_stmt_fun (Sfcnct v1 e) ce0).
  Proof.
    intros.
    rewrite /inferType_stmt_fun.
    apply Infertype_sfcnct with t (type_of_cmpnttyp t) c.
    split.
    apply H.
    split.
    rewrite H0.
    reflexivity.
    apply ftype_equiv_ident.
  Qed.

  Lemma inferType_spcnct_sem_conform :
    forall v1 t c e ce0 ,
      CE.find (HiF.base_ref v1) ce0 = Some (t, c) ->
      type_of_cmpnttyp t = HiF.type_of_hfexpr e ce0 ->
      inferType_stmt (Spcnct v1 e) ce0 (inferType_stmt_fun (Spcnct v1 e) ce0).
  Proof.
    intros.
    rewrite /inferType_stmt_fun.
    apply Infertype_spcnct with t (type_of_cmpnttyp t) c.
    split.
    apply H.
    split.
    rewrite H0.
    reflexivity.
    apply ftype_weak_equiv_ident.
  Qed.

  Lemma inferType_swhen_sem_conform :
  forall (ce0 ce1 ce2 : CE.env) (e : HiF.hfexpr) (s1 s2 : HiF.hfstmt_seq),
      inferType_stmts s1 ce0 ce1 ->
      inferType_stmts s2 ce1 (inferType_stmt_fun (Swhen e s1 s2) ce0) ->
      inferType_stmt (Swhen e s1 s2) ce0 (inferType_stmt_fun (Swhen e s1 s2) ce0).
  Proof.
    intros. apply Infertype_swhen with (ce' := ce1). exact H. exact H0.
  Qed.

  (* Lemma inferType_sstop_sem_conform : *)
  (* forall ce0 e1 e2 n, *)
  (*     inferType_stmt (Sstop e1 e2 n) ce0 (inferType_stmt_fun (Sstop e1 e2 n) ce0). *)
  (* Proof. *)
  (*   intros. apply Infertype_sstop. *)
  (* Qed. *)
  
  Parameter init_new_comp_name :
     forall s, HiF.is_init s -> forall v, HiF.new_comp_name v.
  Parameter not_init_cefind_some :
     forall s, ~~ HiF.is_init s -> forall v (ce:CE.env) t, CE.find v ce = Some t.

  Parameter new_comp_name_not_rep :
     forall v1 v2, HiF.new_comp_name v1 -> v1 != v2.

  Parameter upd_new_comp_same_expr :
     forall v t e ce ce', HiF.new_comp_name v ->
                        ce' = CE.add v t ce ->
                        HiF.type_of_hfexpr e ce = HiF.type_of_hfexpr e ce'.

  Lemma inferType_sskip_sem_conform :
  forall ce0 ,
      inferType_stmt HiF.sskip ce0 (inferType_stmt_fun HiF.sskip ce0).
  Proof.
    intros. apply Infertype_sskip.
  Qed.

  Definition inferType_stmts_sem_conform_statement (ss : HiF.hfstmt_seq) : Prop :=
    forall ce0 : CE.env,
      inferType_stmts ss ce0 (inferType_stmts_fun ss ce0).

  Lemma inferType_stmts_init_sem_conform :
    forall ss : HiF.hfstmt_seq, inferType_stmts_sem_conform_statement ss.
  Proof.
    apply hfstmt_seq_hfstmt_ind with (P := inferType_stmts_sem_conform_statement)
                                     (P0 := fun st : HiF.hfstmt => match st with
                                                               | Swhen c s1 s2 => inferType_stmts_sem_conform_statement s1
                                                                               /\ inferType_stmts_sem_conform_statement s2
                                                               | _ => True end) ;
    try done.
    unfold inferType_stmts_sem_conform_statement. apply Infertype_stmts_nil.
    intros.
    unfold inferType_stmts_sem_conform_statement.
    intros.
    apply Infertype_stmts_con with (inferType_stmt_fun h ce0).
    have Hin : ((HiF.is_init h) \/ ~~(HiF.is_init h)) by (case (HiF.is_init h); [by left| by right]).
    move : Hin.
    induction h; intros; move : Hin => [Hin | Hin]; try done.
    - exact : (inferType_sskip_sem_conform). 
    - exact : (inferType_swire_sem_conform s f ce0 (init_new_comp_name _ Hin s)).
    - exact : (inferType_sreg_sem_conform s h ce0 (init_new_comp_name _ Hin s)).
    - exact : (inferType_smem_sem_conform s h ce0 (init_new_comp_name _  Hin s)).
    - exact : (inferType_sinst_sem_conform s s0 ce0 (init_new_comp_name _ Hin s) (new_comp_name_not_rep s s0 (init_new_comp_name _ Hin s))).
    - have Hte : (HiF.type_of_hfexpr h ce0 = HiF.type_of_hfexpr h (inferType_stmt_fun (Snode s h) ce0)).
      rewrite/=.
      apply upd_new_comp_same_expr with s (HiF.aggr_typ (HiF.type_of_hfexpr h ce0), Node); try done.
      exact : (init_new_comp_name _ Hin).
      exact : (inferType_snode_sem_conform s h ce0 (init_new_comp_name _ Hin _) Hte).
    - case Hf : (CE.find (HiF.base_ref h) ce0) => [[t c]|].
      move : (not_init_cefind_some _ Hin (HiF.base_ref h) ce0 (HiF.aggr_typ (HiF.type_of_hfexpr h1 ce0), c)) => Hni.
      apply inferType_sfcnct_sem_conform with t c; try done.
      move : (CE.find_some_vtyp Hf) => Hfv.
      move : (CE.find_some_vtyp Hni) => Hnv.
      rewrite Hfv in Hnv.
      inversion Hnv. rewrite /=//.
      move : (not_init_cefind_some _ Hin (HiF.base_ref h) ce0 (HiF.aggr_typ (HiF.type_of_hfexpr h1 ce0), Node)) => Hni.
      rewrite Hf in Hni; discriminate.
    - case Hf : (CE.find (HiF.base_ref h) ce0) => [[t c]|].
      move : (not_init_cefind_some _ Hin (HiF.base_ref h) ce0 (HiF.aggr_typ (HiF.type_of_hfexpr h1 ce0), c)) => Hni.
      apply inferType_spcnct_sem_conform with t c; try done.
      move : (CE.find_some_vtyp Hf) => Hfv.
      move : (CE.find_some_vtyp Hni) => Hnv.
      rewrite Hfv in Hnv.
      inversion Hnv. rewrite /=//.
      move : (not_init_cefind_some _ Hin (HiF.base_ref h) ce0 (HiF.aggr_typ (HiF.type_of_hfexpr h1 ce0), Node)) => Hni.
      rewrite Hf in Hni; discriminate.
    - apply inferType_sinvalid_sem_conform.
    - apply inferType_swhen_sem_conform with (ce1 := inferType_stmts_fun h1 ce0) ; try done.
      apply H. apply H.
    rewrite/=.
    exact : (H0 (inferType_stmt_fun h ce0) ).
  Qed.

  Lemma inferType_inport_sem_conform :
  forall v t ce0 ,
      inferType_port (Finput v t) ce0 (inferType_port_fun (Finput v t) ce0).
  Proof.
    intros.
    apply Infertype_inport.
    rewrite /inferType_port_fun.
    rewrite (HiF.CELemmas.add_eq_o _ _ (eq_refl v)) //.
  Qed.

  Lemma inferType_outport_sem_conform :
  forall v t ce0 ,
      inferType_port (Foutput v t) ce0 (inferType_port_fun (Foutput v t) ce0).
  Proof.
    intros.
    apply Infertype_outport.
    rewrite (HiF.CELemmas.add_eq_o _ _ (eq_refl v)) //.
  Qed.

  Lemma inferType_ports_sem_conform :
  forall ss ce0,
    inferType_ports ss ce0 (inferType_ports_fun ss ce0).
  Proof.
    elim. intros. apply infertype_ports_nil.
    intros.
    apply infertype_ports_con with (inferType_port_fun a ce0).
    elim a; intros; try done.
    - apply inferType_inport_sem_conform.
    - apply inferType_outport_sem_conform.
    - rewrite/=.
    apply (H (inferType_port_fun a
    ce0)).
    Qed.

  Lemma inferType_inmod_sem_conform :
  forall vm ps ss ce,
    (*inferType_ports ps ce' ce1 -> inferType_stmts ss ce1 ce2 ->*)
    inferType_module (FInmod vm ps ss) ce (inferType_module_fun (FInmod vm ps ss) ce).
  Proof.
    intros.
    rewrite /inferType_module_fun.
    apply infertype_inmod with (CE.add vm (HiF.aggr_typ (inst_type_of_ports' ps), Fmodule) ce) (inferType_ports_fun ps
    (CE.add vm (HiF.aggr_typ (inst_type_of_ports' ps), Fmodule) ce)).
    rewrite (HiF.CELemmas.add_eq_o _ _ (eq_refl vm)) //.
    apply inferType_ports_sem_conform.
    apply inferType_stmts_init_sem_conform.
Qed.

  Lemma inferType_exmod_sem_conform :
  forall vm ps ss ce,
  inferType_module (FExmod vm ps ss) ce (inferType_module_fun (FExmod vm ps ss) ce).
  Proof.
    intros.
    apply infertype_exmod.
    rewrite /inferType_module_fun.
    rewrite (HiF.CELemmas.add_eq_o _ _ (eq_refl vm)) //.
  Qed.

  Lemma inferType_mods_sem_conform :
  forall ms ce,
  inferType_modules ms ce (inferType_modules_fun ms ce).
  Proof.
    elim. intros. apply infertype_modules_nil.
    intros.
    apply infertype_modules_con with (inferType_module_fun a ce).
    elim a; intros; try done.
    - apply inferType_inmod_sem_conform.
    - apply inferType_exmod_sem_conform.
    - rewrite/=.
    apply (H (inferType_module_fun a ce)).
    Qed.

  (** End **)
End InferTypeS.

Section InferTypeP.
  
  
  Definition def_pvar := VarOrder.default. 
  
  Inductive inferType_stmtP : HiFP.hfstmt -> CEP.env -> CEP.env -> Prop :=
  | Infertype_wireP  v  t ce ce' :
      (* HiFP.new_comp_name v -> *)
      (* CE.find v ce = None -> *)
      CEP.find (v, def_pvar) ce' = Some (HiFP.aggr_typ t, Wire) ->
      inferType_stmtP (HiFP.swire (v, def_pvar) t) ce ce'
  | Infertype_regP v r ce ce' :
      (* HiFP.new_comp_name v -> *)
      (* CE.find v ce = None -> *)
      CEP.find (v, def_pvar) ce' = Some (HiFP.reg_typ r, Register) ->
      inferType_stmtP (HiFP.sreg (v, def_pvar) r) ce ce'
  | Infertype_inst v1 v2 ce ce' :
      HiFP.new_comp_name v1 ->
      (* CE.find v1 ce = None -> *)
      ~~ (v1 == v2) ->
      (* CE.find v2 ce = Some t -> *)
      CE.find v1 ce' = Some (fst (CE.vtyp v2 ce), Instanceof) ->
      inferType_stmt (Sinst v1 v2) ce ce'
  | Infertype_node v e ce ce' :
      HiFP.new_comp_name v ->
      (* CE.find v ce = None -> *)
      (* ~~ fexpr_has_v v e -> *)
      HiFP.type_of_hfexpr e ce = HiFP.type_of_hfexpr e ce' ->
      CE.find v ce' = Some (HiFP.aggr_typ (HiFP.type_of_hfexpr e ce), Node) ->
      inferType_stmt (Snode v e) ce ce'
  | Infertype_mem v m ce ce' :
      HiFP.new_comp_name v ->
      (* CE.find v ce = None -> *)
      CE.find v ce' = Some (Mem_typ m, Memory) ->
      inferType_stmt (Smem v m) ce ce'
  | Infertype_invalid v ce :
      inferType_stmt (Sinvalid v) ce ce
  | Infertype_sfcnct r e ce :
      forall t t' c,
      CE.find (HiFP.base_ref r) ce = Some (t, c) /\
      HiFP.type_of_hfexpr e ce = t' /\
      HiFP.ftype_equiv (type_of_cmpnttyp t) t' ->
      inferType_stmt (Sfcnct r e) ce ce
  | Infertype_spcnct r e ce :
      forall t t' c,
      CE.find (HiFP.base_ref r) ce = Some (t, c) /\
      HiFP.type_of_hfexpr e ce = t' /\
      HiFP.ftype_weak_equiv (type_of_cmpnttyp t) t' ->
      inferType_stmt (Spcnct r e) ce ce
  | Infertype_sskip ce :
      inferType_stmt (HiFP.sskip) ce ce
  | Infertype_swhen e s1 s2 ce ce' ce'' :
      inferType_stmts s1 ce ce' ->
      inferType_stmts s2 ce' ce'' ->
      inferType_stmt (Swhen e s1 s2) ce ce''


End InferTypeP.
