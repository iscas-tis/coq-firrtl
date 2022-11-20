   (** Pass RemoveReset *)
   Definition is_async er ce :=
     let rt := type_of_hfexpr er ce in
     match rt with | Gtyp Fasyncreset => true | _ => false end.

   Parameter invalid_value : ftype.

   Definition RemoveReset_fun (st : hfstmt) ce ss :=
     match st with
     | Sreg v r => match (reset r) with
                   | Rst er (Eref (Eid ei)) =>
                     match (SV.acc ei ss) with
                     | R_default =>
                       (CE.add_fst v
                                   (Reg_typ (mk_freg (type r) (clock r) (Rst (econst (Fuint 1) [::b0]) (eref (eid v))))) ce, ss)
                     | _ => (ce, ss)
                     end
                   | Rst (Econst t [::b0]) ei =>
                     (CE.add_fst v
                            (Reg_typ (mk_freg (type r) (clock r) (Rst (econst (Fuint 1) [::b0]) (eref (eid v))))) ce, ss)
                   | Rst e1 ei => if is_async e1 ce then (ce, ss)
                                  else (CE.add_fst v (Reg_typ (mk_freg (type r) (clock r) (Rst (econst (Fuint 1) [::b0]) (eref (eid v))))) ce, ss)
                   | _ => (ce, ss)
                   end
     | Sfcnct (Eid rg) e =>
       let tr := fst (CE.vtyp rg ce) in
       match tr with
       | Reg_typ r => match (reset r) with
                      | Rst c ei => match type_of_hfexpr c ce with
                                    | Gtyp Freset => (ce, SV.upd rg (r_fexpr (emux c ei e)) ss)
                                    | Gtyp Fasyncreset => (ce, ss) (* TODO: check the scala code again *)
                                    | _ => (ce, ss)
                                    end
                      | _ => (ce, ss)
                      end
       | _ => (ce, ss)
       end
     | Sinvalid (Eid rg) =>
       let tr := fst (CE.vtyp rg ce) in
       match tr with
       | Reg_typ r => let ce_addnode := CE.add vtmp (aggr_typ (type r), Node) ce in
                      let sv_addinv := SV.upd vtmp (r_default) ss in
                      match (reset r) with
                      | Rst c ei => match type_of_hfexpr c ce with
                                    | Gtyp Freset => (ce_addnode, SV.upd rg (r_fexpr (emux c ei (eref (eid vtmp)))) sv_addinv)
                                    | _ => (ce, ss)
                                    end
                      | _ => (ce, ss)
                      end
       | _ => (ce, ss)
       end
     | _ => (ce, ss)
     end.

