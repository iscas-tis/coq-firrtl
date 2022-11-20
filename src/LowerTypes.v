
   (** Pass LowerTypes *)
   (* lower ports
    * We lower ports in a separate pass in order to ensure that statements inside the module do not influence port names.*)
    (* Dependency(RemoveAccesses), // we require all SubAccess nodes to have been removed *)
    (* Dependency(CheckTypes), // we require all types to be correct *)
    (* Dependency(InferTypes), // we require instance types to be resolved (i.e., DefInstance.tpe != UnknownType) *)
    (* Dependency(ExpandConnects) // we require all PartialConnect nodes to have been expanded *)

   (* Parameter destructType_fun : var -> cenv -> dmap. *)

   Fixpoint len_of_ftype t :=
     match t with
     | Gtyp t => 1
     | Atyp t n => len_of_ftype t + n
     | Btyp bs => len_of_ffield bs
     end
   with len_of_ffield f :=
     match f with
     | Fnil => 0
     | Fflips v f t ff => len_of_ftype t + (len_of_ffield ff)
     end.

   (* Fixpoint new_vars_atyp r n t te : CE.env := *)
   (*   match n with *)
   (*   | 0 => te *)
   (*   | S m => new_vars_atyp r m t (CE.add (new_var r (N.of_nat n)) t te) *)
   (*   end. *)

   Fixpoint io_conv c :=
     match c with
     | In_port => Out_port
     | Out_port => In_port
     | c => c
     end.

   Fixpoint destructTypes_fun_aux r t c l {struct t} : list (var * fgtyp * fcomponent) :=
     match t with
     | Gtyp t => (r, t, c) :: l
     | Atyp t n =>
       match n with
       | 0 => l
       | S n => destructTypes_fun_aux (new_var r (N.of_nat n)) t c l
       end
     | Btyp bs => destructField_fun_aux r bs c l
     end
     with destructField_fun_aux r bs c l :=
            match bs with
            | Fnil => l
            | Fflips v f t ff =>
              match f with
              | Nflip =>
                destructTypes_fun_aux (new_var r v) t c l ++ destructField_fun_aux r ff c l
              | Flipped =>
                destructTypes_fun_aux (new_var r v) t (io_conv c) l ++ destructField_fun_aux r ff c l
              end
            end.

   Fixpoint destructTypes_fun (l : list (var * fgtyp * fcomponent)) d : dmap :=
     match l with
     | nil => d
     | (r, t, c) :: tl => destructTypes_fun tl (CE.add r (t, c) d)
     end.

   Definition lowerTypes_fport (p : hfport) dm : dmap :=
     match p with
     | Finput v t => destructTypes_fun (destructTypes_fun_aux v t In_port [::]) dm
     | Foutput v t => destructTypes_fun (destructTypes_fun_aux v t Out_port [::]) dm
     end.

   Definition lowerTypes_init_fstmt dm (s : hfstmt) : dmap :=
     match s with
     | Swire v t => destructTypes_fun (destructTypes_fun_aux v t Wire [::]) dm
     | Sreg v r => destructTypes_fun (destructTypes_fun_aux v (type r) Register [::]) dm
     | Smem v m => destructTypes_fun (destructTypes_fun_aux v (data_type m) Memory [::]) dm
     | _ => dm
     end.

   Definition lowerTypes_init_fstmts ss dm := fold_left lowerTypes_init_fstmt ss dm.

   Definition add_lowtype_2_cenv (lt : option (fgtyp * fcomponent)) (t : option (cmpnt_init_typs * fcomponent)) :=
     match lt, t with
     | None, t => t
     | Some (lt, c), None => Some (aggr_typ (Gtyp lt), c)
     | Some (lt, c), Some t => Some t
     end.

   Definition dmap_2_cenv lt ce : CE.env :=
     CE.map2 add_lowtype_2_cenv lt ce.

   Definition lowerTypes_fun ss ce : CE.env :=
     dmap_2_cenv (lowerTypes_init_fstmts ss empty_dmap) ce.
