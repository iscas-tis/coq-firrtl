From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq ssrfun.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.
From firrtl Require Import Firrtl Env HiEnv HiFirrtl InferTypes.


(** Pass ExpandConnect *)
Section ExpandConnectsP.
  
  (*recursively add sub-elements accroding to the declared aggr_typ*)
  (*for element declaration statement, add a default connection*)
  Fixpoint upd_aggr_elements_aux_rdef (v:pvar) (ts: seq ftype) (sv:StructStateP.t) (n:N) :StructStateP.t:=
    match ts with
    | nil => sv
    | cons hd tl => upd_aggr_elements_aux_rdef v tl (StructStateP.upd (fst v, n) HiFP.r_default sv) (N.add n 1%num)
    end.

  (*use the types recorded in ce, since ce inclueds the result of type infering*)
  Definition upd_aggr_elements_rdef (v:pvar) (ce : CEP.env) (sv:StructStateP.t) : StructStateP.t :=
    let ts := ftype_list_all (type_of_cmpnttyp (fst (CEP.vtyp v ce))) nil in
    StructStateP.upd v HiFP.r_default (upd_aggr_elements_aux_rdef v ts sv initial_index).
  
  (*recursively expand reference on rhs*) 
  Fixpoint expand_eref_aux (r : pvar) (sz : nat) (rs : seq HiFP.hfexpr) : seq HiFP.hfexpr :=
    match sz with
    | 0 => rs
    | S n => expand_eref_aux r n (cons ((HiFP.eref (HiFP.eid (fst r, N.of_nat n)))) rs)
    end.
  
  Definition expand_eref (r : pvar) (t : ftype) : seq HiFP.hfexpr :=
    let ts := ftype_list t nil in
    let sz := size ts in
    expand_eref_aux r sz nil.

  (*recursively expand mux on rhs*) 
  Fixpoint expand_emux (c : HiFP.hfexpr) (ze : seq (HiFP.hfexpr * HiFP.hfexpr)) (es : seq HiFP.hfexpr) : seq HiFP.hfexpr :=
    match ze with
    | nil => es
    | (e1, e2) :: zes => expand_emux c zes ((HiFP.emux c e1 e2) :: es)
    end.
  
  (*TODO?: Somewhere "Replaces constant [[firrtl.WSubAccess]] with [[firrtl.WSubIndex]]"*)
  (*recursively expand expr on rhs*) 
  Fixpoint expand_expr (e : HiFP.hfexpr) (ce : CEP.env) (es : seq HiFP.hfexpr) : seq HiFP.hfexpr :=
    match e with
    | Eref (Eid (r, o)) => expand_eref (r, o) (type_of_cmpnttyp (CEP.vtyp (r,o) ce).1)
    | Emux c e1 e2 => expand_emux c (extzip (HiFP.econst (Fuint 0) nil) (HiFP.econst (Fuint 0) nil) (expand_expr e1 ce nil) (expand_expr e2 ce nil)) es
    | e => e :: es
    end.

  Fixpoint upd_expand_expr (v:pvar) (es: seq HiFP.hfexpr) (sv:StructStateP.t) (n:N) :StructStateP.t:=
    match es with
    | nil => sv
    | cons hd tl => upd_expand_expr v tl (StructStateP.upd (fst v, n) (HiFP.r_cnct (nth (HiFP.econst (Fuint 0) [::]) es n)) sv) (N.add n 1%num)
    end.
  
  Definition p1 : pvar := (N.of_nat 1, N0).
  Compute (expand_eref p1 (Atyp (Gtyp (Fuint 5)) 2)).
  Definition ec1 := (HiFP.econst (Fuint 1) [::b1]).
  Definition ec2 := (HiFP.econst (Fuint 1) [::b0]).
  Definition ev1 := HiFP.eref (Eid p1).
  Definition cem := CEP.empty (cmpnt_init_typs ProdVarOrder.T * fcomponent).
  Definition ce1 := CEP.add p1 (HiFP.aggr_typ (Atyp (Gtyp (Fuint 1)) 3), Wire) cem.
  Compute (expand_expr (HiFP.emux ec1 (HiFP.emux ec1 ev1 ev1) (HiFP.emux ec1 ev1 ev1)) ce1 nil).

  Fixpoint align_weak_equiv_ftype (t1 t2 : ftype) : ftype :=
    match t1, t2 with
    | Gtyp gt1, Gtyp gt2 => t1
    | Atyp at1 n1, Atyp at2 n2 => Atyp (align_weak_equiv_ftype at1 at2) (minn n1 n2)
    | Btyp bs1, Btyp bs2 => Btyp (align_weak_equiv_ffields bs1 bs2)
    | _ , _ => t1
    end
  with align_weak_equiv_ffields (bs1 bs2 : ffield) : ffield :=
         match bs1 with
         | Fnil => bs1
         | Fflips v1 f1 tf1 fs1 =>
             match bs2 with
             | Fnil => bs1
             | Fflips v2 f2 tf2 fs2 =>
                 if (v1 == v2)
                 then Fflips v1 f1 (align_weak_equiv_ftype tf1 tf2) (align_weak_equiv_ffields fs1 fs2)
                 else align_weak_equiv_ffields bs1 fs2
             end
         end.

  Fixpoint upd_expand_expr_weak_eq (v1 v2:pvar) (es: seq HiFP.hfexpr) (ce : CEP.env) (sv:StructStateP.t) (n:N) :StructStateP.t:=
    match es with
    | nil => sv
    | cons hd tl => match CEP.find (fst v2, n) ce with
                    | None => sv
                    | Some t =>
                        upd_expand_expr v1 tl (StructStateP.upd (fst v1, n) (HiFP.r_cnct (nth (HiFP.econst (Fuint 0) [::]) es n)) sv) (N.add n 1%num)
                    end
    end.

  Fixpoint upd_expand_expr_inv (v:pvar) (es: seq HiFP.hfexpr) (sv:StructStateP.t) (n:N) :StructStateP.t:=
    match es with
    | nil => sv
    | cons hd tl => upd_expand_expr v tl (StructStateP.upd (fst v, n) (HiFP.r_invalid (nth (HiFP.econst (Fuint 0) [::]) es n)) sv) (N.add n 1%num)
    end.
  
  Definition expandconnects_stmt (s : HiFP.hfstmt) (ce : CEP.env) (sv : StructStateP.t): StructStateP.t :=
    match s with
    | Sskip => sv
    | Swire v t => upd_aggr_elements_rdef v ce sv
    | Sreg v t => upd_aggr_elements_rdef v ce sv
    | Smem v t => upd_aggr_elements_rdef v ce sv
    | Snode v e => upd_expand_expr v (expand_expr e ce nil) sv 0
    | Sfcnct (Eid v) e => upd_expand_expr v (expand_expr e ce nil) sv 0
    | Spcnct (Eid v) e => upd_expand_expr v (expand_expr e ce nil) sv 0
    | Sinvalid (Eid v) => upd_expand_expr_inv v nil sv 0
    | _ => sv
    end.

  Definition elements_declaration (ce : CEP.env) (sts : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
    let es := CEP.elements ce in
    match es with
    | nil => sts
    | e :: es => match e with
                           | (v, (t, Wire)) => HiFP.qcons (HiFP.swire v (type_of_cmpnttyp t)) sts
                           | (v, (Reg_typ t, Register)) => HiFP.qcons (HiFP.sreg v t) sts
                           | (v, (Mem_typ t, Memory)) => HiFP.qcons (HiFP.smem v t) sts
                           | _ => sts
                           end
    end.

  Definition elements_connection (sv : StructStateP.t) (sts : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
    let cs := StructStateP.elements sv in
    match cs with
    | nil => sts
    | c :: cs => match c with
                | (v, R_cnct e) => HiFP.qcons (Sfcnct (Eid v) e) sts
                | (v, R_invalid e) => HiFP.qcons (Sinvalid (Eid v)) sts
                | (v, R_default') => sts
                end
    end.

End ExpandConnectsP.
    

   (* Fixpoint size_of_ftype (ft : ftype) : nat := *)
   (* (* calculates the number of ground type elements in the type ft. *) *)
   (*   match ft with *)
   (*   | Gtyp t => 1 *)
   (*   | Atyp t n => (size_of_ftype t) * n *)
   (*   | Btyp b => size_of_fields b *)
   (*   end *)
   (* with size_of_fields (b : ffield) : nat := *)
   (*        match b with *)
   (*        | Fnil => 0 *)
   (*        | Fflips v fl t fs => (size_of_ftype t) + size_of_fields fs *)
   (*        end. *)

   (* Fixpoint offset_of_subfield_b (ft : ffield) (fid : Var.var) (n : nat) : nat := *)
   (* (* calculates n + the offset of field fid in the bundle type ft. *) *)
   (*   match ft with *)
   (*   | Fnil => n *)
   (*   | Fflips v fl t fs => if fid == v then n else offset_of_subfield_b fs fid (n + size_of_ftype t) *)
   (*   end. *)

   (* Definition offset_of_subfield (ft : ftype) (fid : Var.var) (n : nat) : nat := *)
   (* (* calculates n + the offset of field fid, if ft is a bundle type; *)
   (*    if ft is a ground or an array type it returns 0. *) *)
   (*   match ft with *)
   (*   | Gtyp t => 0 *)
   (*   | Atyp t n => 0 *)
   (*   | Btyp b => offset_of_subfield_b b fid n *)
   (*   end. *)

   (* (** TBD *) *)
   (* Parameter new_var : var -> Var.var -> var. *)
   (* Parameter new_subvar : var -> nat -> var. *)
   (* Parameter new_subvar_i : var -> nat -> var. *)
   (* Parameter new_subvar_t : var -> var -> var. *)
   (* Parameter var2v : Var.var -> V.t. *)
   (* Parameter vtmp : var. *)


   (* Fixpoint list_repeat_fn (f : list ftype -> list ftype) (n : nat) (l : list ftype) : list ftype := *)
   (* (* calculates f(f(...(f l)...)) (n applications of f). *) *)
   (*   match n with *)
   (*   | 0 => l *)
   (*   | S m => list_repeat_fn f m (f l) *)
   (*   end. *)

   (* Fixpoint ftype_list (ft : ftype) (l : list ftype) : list ftype := *)
   (* (* prepends to l a list containing all the ground type elements' types in ft. *) *)
   (*   match ft with *)
   (*   | Gtyp t => Gtyp t :: l *)
   (*   | Atyp t n => list_repeat_fn (ftype_list t) n l *)
   (*   | Btyp b => ftype_list_btyp b l *)
   (*   end *)

   (* with ftype_list_btyp (b : ffield) (l : list ftype) : list ftype := *)
   (* (* prepends to l a list containing all the ground type elements' types in the fields b. *)
   (*    Note that the list has reverse order of the fields in b. *) *)
   (*   match b with *)
   (*   | Fnil => l *)
   (*   | Fflips v fl t fs => ftype_list_btyp fs (ftype_list t l) *)
   (*   end. *)

   (* Fixpoint vlist_repeat_fn (f : list (var * ftype) -> list (var * ftype)) (v : V.T) (i : nat) (n : nat) (l : list (var * ftype)) {struct n} : list (var * ftype) := *)
   (* (* calculates f(f(...(f l)...)) (n applications of f). *)
   (*    The parameteres v and i do not influence the result. *) *)
   (*   match n with *)
   (*   | 0 => l *)
   (*   | S m => vlist_repeat_fn f (new_subvar v i) i m (f l) *)
   (*   end. *)

   (* Fixpoint ftype_vlist (v : var) (ft : ftype) (l : list (var * ftype)) : list (var * ftype) := *)
   (* (* prepends to l a list containing, for every ground type element in ft, *)
   (*    a pair (identifier, type). *)
   (*    However, I think the case of vector types is implemented wrongly. *) *)
   (*   match ft with *)
   (*   | Gtyp t => (v, Gtyp t) :: l *)
   (*   | Atyp t n => vlist_repeat_fn (ftype_vlist v t) v (size_of_ftype t) n l *)
   (*   | Btyp b => ftype_vlist_btyp v b l *)
   (*   end *)

   (* with ftype_vlist_btyp (r : var) (b : ffield) (l : list (var * ftype)) : list (var * ftype) := *)
   (* (* prepends to l a list containing, for every ground type element in bundle b, *)
   (*    a pair (identifier, type).  The order in l is the reverse of the order in b. *)
   (*    However, I think the case of vector types is implemented wrongly. *) *)
   (*   match b with *)
   (*   | Fnil => l *)
   (*   | Fflips v fl t fs => ftype_vlist_btyp r fs (ftype_vlist (new_subvar r (offset_of_subfield_b b v 0)) t l) *)
   (*   end. *)

(*    (* A map to store types destruct *) *)
(*    Definition dmap := CE.t (fgtyp * fcomponent). *)
(*    Definition empty_dmap : dmap := CE.empty (fgtyp * fcomponent). *)
(*    Definition findsd (v:var) (d:dmap) := *)
(*      match CE.find v d with Some t => t | None => (Fuint 0, Node)  end. *)

(*    Fixpoint expand_eref (er : href) (ce : cenv) : var := *)
(*    (* find a var that corresponds to the reference er (which may be a complex reference) *) *)
(*      match er with *)
(*      | Eid v => v *)
(*      | Esubfield r v => new_subvar (expand_eref r ce) (offset_of_subfield (type_of_ref r ce) (v2var v) 0) *)
(*      | Esubindex r n => new_subvar (expand_eref r ce) n *)
(*      | Esubaccess r e => new_subvar (expand_eref r ce) 0 (* TBD *) *)
(*      end. *)

(*    (* *)
(*    Fixpoint expand_index r t n l : list (var * ftype) := *)
(*      match n with *)
(*      | 0 => l *)
(*      | S m => expand_index r t m ((expand_eref (Esubindex r n), t) :: l) *)
(*      end. *)

(*    Fixpoint expand_fields_fun r bs l : list (var * ftype) := *)
(*      match bs with *)
(*      | Fnil => l *)
(*      | Fflips v fl t fs => expand_fields_fun r fs ((expand_eref (Esubfield r (var2v v)), t) :: l ) *)
(*      end. *)
(* *) *)

(*    Fixpoint fcnct_list (l1 :list (var * ftype)) (l2:list (var * ftype)) (cs : cstate) : cstate := *)
(*    (* This function assumes that the i-th element of list l1 is assigned the value of the i-th element of list l2. *)
(*       It updates cs accordingly. *) *)
(*      match l1, l2 with *)
(*      | nil, nil => cs *)
(*      | (v1, t1) :: tl1, (v2, t2):: tl2 => fcnct_list tl1 tl2 (SV.upd v1 (r_fexpr (Eref (Eid v2))) cs) *)
(*      | _, _ => cs *)
(*      end. *)

(*    (* premise : passive type, weak type equiv *) *)

(*    Fixpoint pcnct_pair_b (v1 : var) (v2 : var) (t1 : ffield) (t2: ffield) (cs : cstate) : cstate := *)
(*    (* This function expands a partial connect (Eid v1) <- (Eref (Eid v2)). *)
(*       It assigns the value of the correct subfield of v2 to the first field of (Eid v1) *)
(*       and adds the corresponding entry to cs. *) *)
(*      match t1 with *)
(*      | Fnil => cs *)
(*      | Fflips vt1 fp1 tf1 fs1 => *)
(*        match t2 with *)
(*        | Fnil => cs *)
(*        | Fflips vt2 fp2 tf2 fs2 => *)
(*          if vt1 == vt2 *)
(*          then SV.upd (new_subvar v1 (offset_of_subfield (Btyp t1) vt1 0)) *)
(*                      (r_fexpr (Eref (Eid (new_subvar v2 (offset_of_subfield (Btyp t2) vt2 0))))) cs *)
(*          else pcnct_pair_b v1 v2 t1 fs2 cs *)
(*        end *)
(*      end. *)

(*    Fixpoint pcnct_pair (t1 : (var * ftype)) (t2: (var * ftype)) (cs : cstate) : cstate := *)
(*    (* This function expands a partial connect (t1) <- (t2), depending on the types of t1 and t2 *)
(*       and returns the changed cs accordingly. *)
(*       If the types are not weakly equivalent, cs is not changed. *) *)
(*      match t1, t2 with *)
(*      | (v1, Gtyp t1) , (v2, Gtyp t2) => SV.upd v1 (r_fexpr (Eref (Eid v2))) cs *)
(*      | (v1, Atyp t1 n1) , (v2, Atyp t2 n2) => *)
(*        let n := minn n1 n2 in let t := Atyp t1 n in *)
(*                               fcnct_list (ftype_vlist v1 t nil) (ftype_vlist v2 t nil) cs *)
(*      | (v1, Btyp b1), (v2, Btyp b2) => pcnct_pair_b v1 v2 b1 b2 cs *)
(*      | _, _ => cs *)
(*      end. *)

(*    (* premise : passive type, weak type equiv *) *)

(*    Parameter store_spcnct : href -> href -> ftype -> cstate -> cstate. *)

(*    Definition store_rhsexpr (s : hfstmt) (cs : cstate) ce : cstate := *)
(*      match s with *)
(*      | Swire v t => SV.upd v r_default cs *)
(*      | Snode v e => SV.upd v (r_fexpr e) cs *)
(*      | Sreg v r => SV.upd v r_default cs *)
(*      | Smem v m => SV.upd v r_default cs *)
(*      | Sfcnct r1 (Eref r2) => *)
(*        let t1 := type_of_ref r1 ce in *)
(*        let t2 := type_of_ref r2 ce in *)
(*        fcnct_list (ftype_vlist (expand_eref r1 ce) t1 nil) (ftype_vlist (expand_eref r2 ce) t2 nil) cs *)
(*      | Spcnct r1 (Eref r2) => *)
(*        let t1 := type_of_ref r1 ce in *)
(*        let t2 := type_of_ref r2 ce in *)
(*        pcnct_pair (expand_eref r1 ce, t1) (expand_eref r2 ce, t2) cs *)
(*      | Sinvalid r1 => SV.upd (expand_eref r1 ce) r_default cs *)
(*      | _ => cs *)
(*      end. *)


   (*
   (* premise : passive type, type equiv *)
   Fixpoint expand_connect_subindex r1 r2 n : hfstmt_seq :=
     match n with
     | 0 => qnil
     | S m => Qcons (Sfcnct (Esubindex r1 n) (Eref (Esubindex r2 n))) (expand_connect_subindex r1 r2 m)
     end.

   (* premise : passive type, type equiv *)
   Fixpoint expand_fullconnect_subfield r1 r2 bs :=
     match bs with
     | Fnil => qnil
     | Fflips v Nflip t bs' => Qcons (Sfcnct (Esubfield r1 (var2v v)) (Eref (Esubfield r2 (var2v v))))
                                     (expand_fullconnect_subfield r1 r2 bs')
     | _ => Qnil
     end.

   (* premise : type weak equiv *)
   Fixpoint expand_partconnect_subfield r1 r2 bs1 bs2 {struct bs1} :=
     match bs1 with
     | Fflips v1 Nflip t1 bs1' =>
       if have_field bs2 v1 then
         Qcons (Sfcnct (Esubfield r1 (var2v v1)) (Eref (Esubfield r2 (var2v v1))))
               (expand_partconnect_subfield r1 r2 bs1' bs2)
       else expand_partconnect_subfield r1 r2 bs1' bs2
     | Fflips v1 Flipped t1 bs1' =>
       if have_field bs2 v1 then
         Qcons (Sfcnct (Esubfield r2 (var2v v1)) (Eref (Esubfield r1 (var2v v1))))
               (expand_partconnect_subfield r1 r2 bs1' bs2)
       else expand_partconnect_subfield r1 r2 bs1' bs2
     | Fnil => qnil
     end.

   (* premise: valid lhs rhs (resolve flow), type equiv/weak_equiv (type infer, width infer) *)
   (* since types are lowered in Pass LoweringType, ExpandConnect is only in transform pass, not in semantics representation ce cs *)
   Fixpoint expandConnect_fun st ce : hfstmt_seq :=
     match st with
     | Sfcnct r1 (Eref r2) =>
       let tr1 := type_of_ref r1 ce in
       let tr2 := type_of_ref r2 ce in
       match tr1, tr2 with
       | Gtyp t1, Gtyp t2 => Qcons (Sfcnct r1 (Eref r2)) qnil
       | Atyp t1 n1, Atyp t2 n2 => expand_connect_subindex r1 r2 n1
       | Btyp bs1, Btyp bs2 => expand_fullconnect_subfield r1 r2 bs1
       | _, _ => qnil
       end
     | Sfcnct r1 (Emux c r2a r2b) => TBD
     | Sfcnct r1 (Evalidif c r2) => TBD
     | Spcnct r1 (Eref r2) =>
       let tr1 := type_of_ref r1 ce in
       let tr2 := type_of_ref r2 ce in
       match tr1, tr2 with
       | Gtyp t1, Gtyp t2 => Qcons (Sfcnct r1 (Eref r2)) qnil
       | Atyp t1 n1, Atyp t2 n2 => if n1 < n2 then expand_connect_subindex r1 r2 n1
                                   else expand_connect_subindex r1 r2 n2
       | Btyp bs1, Btyp bs2 => expand_partconnect_subfield r1 r2 bs1 bs2
       | _, _ => qnil
       end
     | st => Qcons st qnil
     end.

   Inductive expand_fields : var -> var -> ffield -> CE.env -> cstate -> CE.env -> cstate -> Prop :=
   | Expand_fnil r1 r2 ce cs ce' cs' : expand_fields r1 r2 (Fnil) ce cs ce' cs'
   | Expand_fields r1 r2 v t f ffs ce0 cs0 ce1 ce2 cs1 ce' cs':
       CE.Add (new_var r1 v) (aggr_typ t, Wire) ce0 ce1 ->
       CE.Add (new_var r2 v) (aggr_typ t, Wire) ce1 ce2 ->
       SV.Upd (new_var r1 v) (R_fexpr (Eref (Eid (new_var r2 v)))) cs0 cs1 ->
       expand_fields r1 r2 ffs ce2 cs1 ce' cs' ->
       expand_fields r1 r2 (Fflips (v) f t ffs) ce0 cs0 ce' cs'.
  *)

   (*
   Inductive expandConnect : hfstmt -> CE.env -> cstate -> CE.env -> cstate -> Prop :=
   | Expand_fcnnct :
       forall r f bs r2 ce0 cs0 ce cs ,
         base_type_of_ref r ce0 == Btyp bs ->
         have_field bs (v2var f) ->
         ftype_equiv (type_of_ref r ce0) (type_of_ref r2 ce0) ->
         expand_fields (base_ref r) (base_ref r2) bs ce0 cs0 ce cs ->
         expandConnect (Sfcnct r (Eref r2)) ce0 cs0 ce cs
   | Expand_pcnnct r r2 ce0 cs0 ce cs:
       expandConnect (Spcnct r (Eref r2)) ce0 cs0 ce cs.
    *)
