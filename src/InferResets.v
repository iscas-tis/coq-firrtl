
   (** Pass InferResets **)

   (* A map to store candidate reset signals *)
   (* Definition rmap := CE.t (ftype). *)
   (* Definition empty_rmap : rmap := CE.empty (ftype). *)
   (* Definition finds_r (v:var) (r:rmap) := match CE.find v r with Some t => t | None => def_ftype end. *)

   Definition rmap := CE.t (seq ftype).
   Definition empty_rmap : rmap := CE.empty (seq ftype).
   Definition findr (v:var) (r:rmap) := match CE.find v r with Some t => t | None => [::] end.

   (* store a list of abstract reset types, and check async/sync later *)
   Fixpoint add_ref_rmap r t ce m : rmap :=
     match r with
     | Eid v => CE.add v (cons t (findr v m)) m
     | Esubfield r f =>
       let br := base_ref r in
       CE.add br (cons (upd_name_ftype (base_type_of_ref r ce) (v2var f) t) (findr br m)) m
     | Esubindex rs n =>
       let br := base_ref rs in
       let vt := type_of_cmpnttyp (fst (CE.vtyp br ce)) in
       match vt with
       | Gtyp gt => m
       | Atyp ta na => CE.add br (cons (upd_vectyp vt t) (findr br m)) m
       | Btyp _ => CE.add br (cons (upd_name_ftype vt (v2var (get_field_name rs)) t) (findr br m)) m
       end
     | Esubaccess rs n =>
       let br := base_ref rs in
       let vt := type_of_cmpnttyp (fst (CE.vtyp br ce)) in
       match vt with
       | Gtyp gt => m
       | Atyp ta na => CE.add br (cons (upd_vectyp vt t) (finds br m)) m
       | Btyp Fnil => m
       | Btyp (Fflips v _ tf fs) =>
         CE.add br (cons (upd_name_ftype vt (v2var (get_field_name rs)) t) (finds br m)) m
       end
     end.

   Fixpoint inferReset_rmap ce (m : rmap) (ss : hfstmt_seq) : rmap :=
   match ss with
   | Qnil => m
   | Qcons s sss =>
     match s with
     | Snode v e => inferReset_rmap ce (CE.add v [::type_of_hfexpr e ce] m) sss
     | Swire v t => inferReset_rmap ce (if is_deftyp t then CE.add v [::t] m else m) sss
     | Sreg v _
     | Smem v _ => inferReset_rmap ce m sss
     | Sinst v1 v2 => inferReset_rmap ce (CE.add v1 [::type_of_ref (Eid v2) ce] m) sss
     | Sinvalid v => inferReset_rmap ce m sss
     | Sfcnct r e => inferReset_rmap ce (let te := type_of_hfexpr e ce in
                                         add_ref_rmap r te ce m) sss
     | Spcnct r e => inferReset_rmap ce (let te := type_of_hfexpr e ce in
                                         add_ref_rmap r te ce m) sss
     | Sskip
     (* | Sstop _ _ _*) => inferReset_rmap ce m sss
     | Swhen c s1 s2 => inferReset_rmap ce (inferReset_rmap ce (inferReset_rmap ce m s1) s2) sss
     end
   end.

   Definition is_uninfered_reset rs := is_deftyp (hd def_ftype rs).

   Fixpoint has_async rs :=
     match rs with
     | [::] => false
     | Gtyp Fasyncreset :: rt => true
     | _ :: rt => has_async rt
     end.

   Fixpoint has_sync rs {struct rs} :=
     match rs with
     | [::] => false
     | Gtyp (Fuint 1) :: rt => true
     | _ :: rt => has_sync rt
     end.

   Definition add_reset2cenv (m : option (list ftype)) (t : option (cmpnt_init_typs * fcomponent)) :=
     match t, m with
     | Some (Aggr_typ (Gtyp Freset), c), Some rs =>
       if (has_async rs && (negb (has_sync rs))) then Some (aggr_typ (Gtyp (Fuint 1)), c)
           else if has_sync rs && has_async rs then Some (aggr_typ def_ftype, c)
                else Some (aggr_typ (Gtyp (Fuint 1)), c)
     | _, _ => t
     end.

   Definition rmap_map2_cenv (r:rmap) ce : CE.env :=
     CE.map2 add_reset2cenv r ce.

   Definition inferReset_fun ss ce : CE.env :=
     rmap_map2_cenv (inferReset_rmap ce empty_rmap ss) ce.
