From Coq Require Import ZArith FunInd OrderedType FMaps FMapAVL(* for Nat.eq_dec *).
From simplssrlib Require Import SsrOrder FMaps Var ZAriths Tactics Types FSets Store.
From nbits Require Import NBits.
From firrtl Require Import Env Firrtl HiEnv HiFirrtl ModuleGraph_simplified TopoSort. (* for hfmodule and its parts *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq fintype ssrint ssrfun.
Require Import Coq.micromega.Lia.

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

Fixpoint ft_find_sub (checkt : ftype) (num : N) : option ftype :=
  match checkt with
  | Gtyp gt => if num == N0 then Some checkt else None
  | Atyp atyp n => if num == N0 then Some checkt
                   else if (((N.to_nat num) - 1) >= (num_ref atyp) * n) then None
                   else if (((N.to_nat num) - 1) mod (num_ref atyp)) == 0 (* 对应标号是atyp，可能agg *)
                   then Some atyp
                   else (* 继续找atyp中的结构 *)
                    ft_find_sub atyp (N.of_nat (((N.to_nat num) - 1) mod (num_ref atyp)))
  | Btyp ff => if num == N0 then Some checkt
               else match ft_find_ff ff num with
              | Some newf => Some newf
              | None => None
              end
  end
with ft_find_ff (ff : ffield) (num : N) : option ftype :=
  match ff with
  | Fflips v0 _ ft ff' => if num == 1%num (* 找到被更新的标号, 所对应的field *)
                              then Some ft
                          else if (N.to_nat num) > (num_ref ft) (* 不在该field中, 找下一个field *)
                              then ft_find_ff ff' (N.of_nat ((N.to_nat num) - (num_ref ft)))
                           else (* 在field v0中 *)
                              ft_find_sub ft (N.sub num 1%num)
  | _ => None
  end.
  
Fixpoint list_gtyp (ft : ftype) : seq fgtyp :=
match ft with
   | Gtyp gt => [::gt]
   | Atyp atyp n => list_gtyp atyp
   | Btyp ff => list_gtyp_ff ff
   end
with list_gtyp_ff (ff : ffield) : seq fgtyp :=
   match ff with
   | Fnil => [::]
   | Fflips _ _ ft ff' => list_gtyp ft ++ list_gtyp_ff ff'
   end.

Fixpoint list_gtypref (v : ProdVarOrder.t) (ft : ftype) : seq ProdVarOrder.t :=
match ft with
   | Gtyp gt => [::v]
   | Atyp atyp n => list_gtypref (v.1, N.add v.2 1%num) atyp
   | Btyp ff => list_gtypref_ff v ff
   end
with list_gtypref_ff (v : ProdVarOrder.t) (ff : ffield) : seq ProdVarOrder.t :=
   match ff with
   | Fnil => [::]
   | Fflips _ _ ft ff' => list_gtypref (v.1, N.add v.2 1%num) ft ++ list_gtypref_ff (v.1, N.add v.2 (N.of_nat (num_ref ft + 1))) ff'
   end.

Fixpoint list_flip (ft : ftype) (fl : bool): seq bool :=
match ft with
   | Gtyp gt => [::fl]
   | Atyp atyp n => list_flip atyp fl
   | Btyp ff => list_flip_ff ff fl
   end
with list_flip_ff (ff : ffield) (fl : bool) : seq bool :=
   match ff with
   | Fnil => [::]
   | Fflips _ Nflip ft ff' => list_flip ft fl ++ list_flip_ff ff' fl
   | Fflips _ Flipped ft ff' => list_flip ft (~~fl) ++ list_flip_ff ff' fl
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

(* 只check gtyp的flip情况 *)
Fixpoint ft_check_flip (checkt : ftype) (num : N) (fl : bool) : option bool :=
  match checkt with
  | Gtyp gt => if num == N0 then Some fl else None
  | Atyp atyp n => if num == N0 then Some fl
                   else if (((N.to_nat num) - 1) >= (num_ref atyp) * n) then None
                   else 
                    ft_check_flip atyp (N.of_nat (((N.to_nat num) - 1) mod (num_ref atyp))) fl
  | Btyp ff => if num == N0 then Some fl
               else ft_check_flip_f ff num fl
  end
with ft_check_flip_f (ff : ffield) (num : N) (fl : bool) : option bool :=
  match ff with
  | Fflips v0 Flipped ft ff' => if (N.to_nat num) > (num_ref ft) (* 不在该field中, 找下一个field *)
                                  then ft_check_flip_f ff' (N.of_nat ((N.to_nat num) - (num_ref ft))) fl
                                else (* 在field v0中 *)
                                  ft_check_flip ft (N.sub num 1%num) (~~fl)
  | Fflips v0 Nflip ft ff' => if (N.to_nat num) > (num_ref ft) (* 不在该field中, 找下一个field *)
                                  then ft_check_flip_f ff' (N.of_nat ((N.to_nat num) - (num_ref ft))) fl
                              else (* 在field v0中 *)
                                  ft_check_flip ft (N.sub num 1%num) fl
  | _ => None
  end.

Definition type_ref (v : ProdVarOrder.t) (tmap : CEP.t ftype) : option ftype :=
  match CEP.find (fst v, N0) tmap with
  | Some checkt => ft_find_sub checkt (snd v)
  | None => None
  end.

(* type of mux expression *)
Definition mux_gtyp (t1 : fgtyp) (t2 : fgtyp) : option fgtyp :=
      match t1, t2 with
      | Fuint w1, Fuint w2 => Some (Fuint (maxn w1 w2))
      | Fuint w1, Fuint_implicit w2 => Some (Fuint (maxn w1 w2))
      | Fuint_implicit w1, Fuint w2 => Some (Fuint (maxn w1 w2))
      | Fuint_implicit w1, Fuint_implicit w2 => Some (Fuint (maxn w1 w2))
      | Fsint w1, Fsint w2 => Some (Fsint (maxn w1 w2))
      | Fsint w1, Fsint_implicit w2 => Some (Fsint (maxn w1 w2))
      | Fsint_implicit w1, Fsint w2 => Some (Fsint (maxn w1 w2))
      | Fsint_implicit w1, Fsint_implicit w2 => Some (Fsint (maxn w1 w2))
      | Fclock, Fclock => Some (Fclock)
      | Freset, Freset => Some (Freset)
      | Fasyncreset, Fasyncreset => Some (Fasyncreset)
      | _,_ => None
      end.

Fixpoint mux_types (t1 : ftype) (t2 : ftype) : option ftype :=
      match t1, t2 with
      | Gtyp gt1, Gtyp gt2 => match mux_gtyp gt1 gt2 with
                              | Some gt => Some (Gtyp gt)
                              | _ => None
                              end
      | Atyp t1' n1, Atyp t2' n2 => match n1 == n2, mux_types t1' t2' with
                                    | true, Some t => Some (Atyp t n1)
                                    | _, _ => None
                                    end
      | Btyp bs1, Btyp bs2 =>
          match mux_btyps bs1 bs2 with
          | Some ff => Some (Btyp ff)
          | None => None
          end
      | _, _ => None
      end
with mux_btyps (bs1 : ffield) (bs2 : ffield) : option ffield :=
      match bs1, bs2 with
      | Fnil, Fnil => Some Fnil
      | Fflips v1 Nflip t1 fs1, Fflips v2 Nflip t2 fs2 =>
          if v1 == v2 then match mux_types t1 t2, mux_btyps fs1 fs2 with
                           | Some t, Some fs => Some (Fflips v1 Nflip t fs)
                           | _, _ => None
                           end
                      else None
      (* mux types must be passive, so Flipped is not allowed *)
      | _, _ => None
    end.

Fixpoint type_of_hfexpr (e : HiFP.hfexpr) (ce : CEP.t ftype) : option ftype :=
match e with
| Econst t bs => match t with
               | Fuint_implicit w => Some (Gtyp (Fuint (Nat.max (size bs) w)))
               | Fsint_implicit w => Some (Gtyp (Fsint (Nat.max (size bs) w)))
               | t => Some (Gtyp t)
               end
| Eref (Eid r) => type_ref r ce
| Eref _ => None
| Ecast AsUInt e1 => match type_of_hfexpr e1 ce with
                     | Some (Gtyp (Fsint w)) | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint w))
                     | Some (Gtyp (Fsint_implicit w)) | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fuint_implicit w))
                     | Some (Gtyp Fclock) | Some (Gtyp Freset) | Some (Gtyp Fasyncreset) => Some (Gtyp (Fuint 1))
                     | _ => None
                     end
| Ecast AsSInt e1 => match type_of_hfexpr e1 ce with
                     | Some (Gtyp (Fsint w)) | Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint w))
                     | Some (Gtyp (Fsint_implicit w)) | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fsint_implicit w))
                     | Some (Gtyp Fclock) | Some (Gtyp Freset) | Some (Gtyp Fasyncreset) => Some (Gtyp (Fsint 1))
                     | _ => None
                     end
| Ecast AsClock e1 => match type_of_hfexpr e1 ce with
                      | Some (Gtyp _) => Some (Gtyp Fclock)
                      | _ => None
                      end
| Ecast AsReset e1 => match type_of_hfexpr e1 ce with
                      | Some (Gtyp _) => Some (Gtyp Freset)
                      | _ => None
                      end
(*| Ecast AsAsync e1 => match type_of_hfexpr e1 ce  with
                      | Some (Gtyp _) => Some (Gtyp Fasyncreset)
                      | _ => None
                      end*)
| Eprim_unop (Upad n) e1 => match type_of_hfexpr e1 ce with
                            | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (maxn w n)))
                            | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (maxn w n)))
                            | Some (Gtyp (Fsint_implicit w)) => Some (Gtyp (Fsint_implicit (maxn w n)))
                            | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fuint_implicit (maxn w n)))
                            | _ => None
                            end
| Eprim_unop (Ushl n) e1 => match type_of_hfexpr e1 ce with
                            | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (w + n)))
                            | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (w + n)))
                            | Some (Gtyp (Fsint_implicit w)) => Some (Gtyp (Fsint_implicit (w + n)))
                            | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fuint_implicit (w + n)))
                            | _ => None
                            end
| Eprim_unop (Ushr n) e1 => match type_of_hfexpr e1 ce with
                            | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (maxn (w - n) 1)))
                            | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (maxn (w - n) 1)))
                            | Some (Gtyp (Fsint_implicit w)) => Some (Gtyp (Fsint_implicit (maxn (w - n) 1)))
                            | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fuint_implicit (maxn (w - n) 1)))
                            | _ => None
                            end
| Eprim_unop Ucvt e1 => match type_of_hfexpr e1 ce with
                        | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint w))
                        | Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint (w + 1)))
                        | Some (Gtyp (Fsint_implicit w)) => Some (Gtyp (Fsint_implicit w))
                        | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fsint_implicit (w + 1)))
                        | _ => None
                        end
| Eprim_unop Uneg e1 => match type_of_hfexpr e1 ce with
                        | Some (Gtyp (Fsint w)) | Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint (w + 1)))
                        | Some (Gtyp (Fsint_implicit w)) | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fsint_implicit (w + 1)))
                        | _ => None
                        end
| Eprim_unop Unot e1 => match type_of_hfexpr e1 ce with
                        | Some (Gtyp (Fsint w)) | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint w))
                        | Some (Gtyp (Fsint_implicit w)) | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fuint_implicit w))
                        | _ => None
                        end
| Eprim_unop (Uextr n1 n2) e1 => match type_of_hfexpr e1 ce with
                                 | Some (Gtyp (Fsint w)) | Some (Gtyp (Fuint w))
                                 | Some (Gtyp (Fsint_implicit w)) | Some (Gtyp (Fuint_implicit w)) =>
                                      if (n2 <= n1) && (n1 < w) then Some (Gtyp (Fuint (n1 - n2 + 1)))
                                                                else None
                                 | _ => None
                                 end
| Eprim_unop (Uhead n) e1 => match type_of_hfexpr e1 ce with
                             | Some (Gtyp (Fsint w)) | Some (Gtyp (Fuint w))
                             | Some (Gtyp (Fsint_implicit w)) | Some (Gtyp (Fuint_implicit w)) =>
                                 if n <= w then Some (Gtyp (Fuint n))
                                           else None
                             | _ => None
                             end
| Eprim_unop (Utail n) e1 => match type_of_hfexpr e1 ce with
                             | Some (Gtyp (Fsint w)) | Some (Gtyp (Fuint w))
                             | Some (Gtyp (Fsint_implicit w)) | Some (Gtyp (Fuint_implicit w)) =>
                                 if n <= w then Some (Gtyp (Fuint (w - n)))
                                           else None
                             | _ => None
                             end
| Eprim_unop _ e1 => match type_of_hfexpr e1 ce with
                     | Some (Gtyp (Fsint _)) | Some (Gtyp (Fuint _))
                     | Some (Gtyp (Fsint_implicit _)) | Some (Gtyp (Fuint_implicit _)) => Some (Gtyp (Fuint 1))
                     | _ => None
                     end
| Eprim_binop (Bcomp _) e1 e2 => match type_of_hfexpr e1 ce, type_of_hfexpr e2 ce with
                                 | Some (Gtyp (Fsint _)), Some (Gtyp (Fsint _))
                                 | Some (Gtyp (Fsint _)), Some (Gtyp (Fsint_implicit _))
                                 | Some (Gtyp (Fsint_implicit _)), Some (Gtyp (Fsint _))
                                 | Some (Gtyp (Fsint_implicit _)), Some (Gtyp (Fsint_implicit _))
                                 | Some (Gtyp (Fuint _)), Some (Gtyp (Fuint _))
                                 | Some (Gtyp (Fuint _)), Some (Gtyp (Fuint_implicit _))
                                 | Some (Gtyp (Fuint_implicit _)), Some (Gtyp (Fuint _))
                                 | Some (Gtyp (Fuint_implicit _)), Some (Gtyp (Fuint_implicit _)) =>
                                     Some (Gtyp (Fuint 1))
                                 | _, _ => None
                                 end
| Eprim_binop Badd e1 e2
| Eprim_binop Bsub e1 e2 => match type_of_hfexpr e1 ce, type_of_hfexpr e2 ce with
                            | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (maxn w1 w2 + 1)))
                            | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit w2))
                            | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint w2))
                            | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2)) =>
                                Some (Gtyp (Fuint_implicit (maxn w1 w2 + 1)))
                            | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (maxn w1 w2 + 1)))
                            | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint_implicit w2))
                            | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint w2))
                            | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) =>
                                Some (Gtyp (Fsint_implicit (maxn w1 w2 + 1)))
                            | _, _ => None
                            end
| Eprim_binop Bmul e1 e2 => match type_of_hfexpr e1 ce, type_of_hfexpr e2 ce with
                            | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (w1 + w2)))
                            | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit w2))
                            | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint w2))
                            | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2)) =>
                                Some (Gtyp (Fuint_implicit (w1 + w2)))
                            | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (w1 + w2)))
                            | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint_implicit w2))
                            | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint w2))
                            | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) =>
                                Some (Gtyp (Fsint_implicit (w1 + w2)))
                            | _, _ => None
                            end
| Eprim_binop Bdiv e1 e2  => match type_of_hfexpr e1 ce, type_of_hfexpr e2 ce with
                             | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint _))
                             | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit _)) => Some (Gtyp (Fuint w1))
                             | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint _))
                             | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit _)) => Some (Gtyp (Fuint_implicit w1))
                             | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint _))
                             | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint_implicit _)) => Some (Gtyp (Fsint (w1 + 1)))
                             | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint _))
                             | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit _)) => Some (Gtyp (Fsint_implicit (w1 + 1)))
                             | _, _ => None
                             end
| Eprim_binop Brem e1 e2 => match type_of_hfexpr e1 ce, type_of_hfexpr e2 ce with
                            | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (minn w1 w2)))
                            | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit w2))
                            | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint w2))
                            | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2)) =>
                                Some (Gtyp (Fuint_implicit (minn w1 w2)))
                            | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (minn w1 w2)))
                            | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint_implicit w2))
                            | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint w2))
                            | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) =>
                                Some (Gtyp (Fsint_implicit (minn w1 w2)))
                            | _, _ => None
                            end
| Eprim_binop Bdshl e1 e2 => match type_of_hfexpr e1 ce, type_of_hfexpr e2 ce with
                             | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (w1 + 2 ^ w2 - 1)))
                             | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit w2))
                             | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint w2))
                             | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2)) => Some (Gtyp (Fuint_implicit (w1 + 2 ^ w2 - 1)))
                             | Some (Gtyp (Fsint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fsint (w1 + 2 ^ w2 - 1)))
                             | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint_implicit w2))
                             | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint w2))
                             | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) => Some (Gtyp (Fsint_implicit (w1 + 2 ^ w2 - 1)))
                             | _, _ => None
                             end
| Eprim_binop Bdshr e1 e2 => match type_of_hfexpr e1 ce, type_of_hfexpr e2 ce with
                             | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint _))
                             | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit _)) => Some (Gtyp (Fuint w1))
                             | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint _))
                             | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit _)) => Some (Gtyp (Fuint_implicit w1))
                             | Some (Gtyp (Fsint w1)), Some (Gtyp (Fuint _))
                             | Some (Gtyp (Fsint w1)), Some (Gtyp (Fuint_implicit _)) => Some (Gtyp (Fsint w1))
                             | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fuint _))
                             | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fuint_implicit _)) => Some (Gtyp (Fsint_implicit w1))
                             | _, _ => None
                             end
| Eprim_binop Bcat e1 e2 => match type_of_hfexpr e1 ce, type_of_hfexpr e2 ce with
                            | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2))
                            | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fuint (w1 + w2)))
                            | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit w2))
                            | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint w2))
                            | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2))
                            | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint_implicit w2))
                            | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint w2))
                            | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) =>
                                Some (Gtyp (Fuint_implicit (w1 + w2)))
                            | _, _ => None
                            end
| Eprim_binop Band e1 e2
| Eprim_binop Bor e1 e2
| Eprim_binop Bxor e1 e2 => match type_of_hfexpr e1 ce, type_of_hfexpr e2 ce with
                            | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2))
                            | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit w2))
                            | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint w2))
                            | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2))
                            | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2))
                            | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint_implicit w2))
                            | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint w2))
                            | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) => Some (Gtyp (Fuint (maxn w1 w2)))
                            | _, _ => None
                            end
| Emux c e1 e2 => match type_of_hfexpr c ce, type_of_hfexpr e1 ce, type_of_hfexpr e2 ce with
                  | Some (Gtyp (Fuint 1)), Some t1, Some t2 => mux_types t1 t2
                  | Some (Gtyp (Fuint_implicit 1)), Some t1, Some t2 =>
                      mux_types t1 t2
                  | _, _, _ => None
                  end
| Evalidif c e1 => match type_of_hfexpr c ce with
                   | Some (Gtyp (Fuint 1)) | Some (Gtyp (Fuint_implicit 1)) => type_of_hfexpr e1 ce
                   | _ => None
                   end
end.

Definition connect_fgtyp_compatible (t_tgt t_src : fgtyp) : bool :=
  if (not_implicit t_tgt) then true
  else (sizeof_fgtyp t_tgt >= sizeof_fgtyp t_src) && fgtyp_equiv t_tgt t_src.

Fixpoint check_connect_fgtyp_compatible (t_tgt t_src : seq fgtyp) : bool :=
  match t_tgt, t_src with
  | nil, nil => true
  | thd :: ttl, shd :: stl => connect_fgtyp_compatible thd shd && check_connect_fgtyp_compatible ttl stl
  | _, _ => false
  end.

Fixpoint check_connect_non_passive_fgtyp (t_tgt t_src : seq fgtyp) (bl : seq bool) : bool :=
  match t_tgt, t_src, bl with
  | nil, nil, nil => true
  | thd :: ttl, shd :: stl, false :: bl' => connect_fgtyp_compatible thd shd && check_connect_non_passive_fgtyp ttl stl bl'
  | thd :: ttl, shd :: stl, true :: bl' => connect_fgtyp_compatible shd thd && check_connect_non_passive_fgtyp ttl stl bl'
  | _, _, _ => false
  end.

Definition connect_non_passive_type (t_tgt : ftype) (t_src : ftype) : Prop :=
  ftype_equiv t_tgt t_src && check_connect_non_passive_fgtyp (list_gtyp t_tgt) (list_gtyp t_src) (list_flip t_tgt false).

Definition connect_type_compatible (t_tgt t_src : ftype) : bool :=
  ftype_equiv t_tgt t_src && check_connect_fgtyp_compatible (list_gtyp t_tgt) (list_gtyp t_src).

Definition port_tmap (tmap : CEP.t ftype) (p : HiFP.hfport) : CEP.t ftype :=
(* Extend a tmap with one port
   tmap_expli: pair (tmap, names of fully-explicit ports)
   p: port
   output: a pair (tmap with the variables for p added, names of fully-explicit ports (possibly including p))
   This function assumes implicitly that if there is a port identifier (v, n),
   there is no other port with identifier (v, n') that clashes with it (i.e. the difference |n - n'|
   is too small to accommodate the ground-type elements of one of them). *)
match p with
| Finput (v, n) t | Foutput (v, n) t =>
    CEP.add (v, n) t tmap
end.

Definition ports_tmap (ps : seq HiFP.hfport) : CEP.t ftype :=
(* create a tmap containing the variables for the ports in ps *)
seq.foldl port_tmap (CEP.empty ftype) ps.

Fixpoint split_expr (ref_src : ProdVarOrder.t) (t : ftype) : option (seq ProdVarOrder.t) :=
  match t with
  | Gtyp _ => Some [:: ref_src]
  | Atyp atyp _ => split_expr (fst ref_src, N.add (snd ref_src) 1%num) atyp
  | Btyp ff => split_expr_f ref_src ff 
  end
with split_expr_f (ref_src : ProdVarOrder.t) (ff : ffield) : option (seq ProdVarOrder.t) :=
  match ff with
  | Fnil => Some nil
  | Fflips v Nflip t ff' =>
    match split_expr_f (fst ref_src, N.add (snd ref_src) (N.of_nat (num_ref t))) ff', split_expr (fst ref_src, N.add (snd ref_src) 1%num) t with
    | Some ls, Some ls' => Some (ls' ++ ls)
    | _,_ => None
    end
  | Fflips v Flipped t ff' => None
  end.

Fixpoint split_expr_non_passive (ref_src : ProdVarOrder.t) (t : ftype) (fl : bool) : option (seq (ProdVarOrder.t * bool)) :=
  match t with
  | Gtyp _ => Some [:: (ref_src, fl)]
  | Atyp atyp _ => split_expr_non_passive (fst ref_src, N.add (snd ref_src) 1%num) atyp fl
  | Btyp ff => split_expr_non_passive_f ref_src ff fl
  end
with split_expr_non_passive_f (ref_src : ProdVarOrder.t) (ff : ffield) (fl : bool) : option (seq (ProdVarOrder.t * bool)) :=
  match ff with
  | Fnil => Some nil
  | Fflips v Nflip t ff' =>
    match split_expr_non_passive_f (fst ref_src, N.add (snd ref_src) (N.of_nat (num_ref t))) ff' fl, split_expr_non_passive (fst ref_src, N.add (snd ref_src) 1%num) t fl with
    | Some ls, Some ls' => Some (ls' ++ ls)
    | _,_ => None
    end
  | Fflips v Flipped t ff' => 
    match split_expr_non_passive_f (fst ref_src, N.add (snd ref_src) (N.of_nat (num_ref t))) ff' fl, split_expr_non_passive (fst ref_src, N.add (snd ref_src) 1%num) t (~~fl) with
    | Some ls, Some ls' => Some (ls' ++ ls)
    | _,_ => None
    end
  end.

Definition testaty0 := (Atyp (Gtyp (Fuint_implicit 0)) 2).
Definition testaty := (Atyp (Atyp (Gtyp (Fuint 4)) 2) 2).
Definition testbty0 := (Btyp (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 0)) 2) (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 0)) 2) Fnil))).
Definition testbty := (Btyp (Fflips (1%num) Nflip (Btyp (Fflips (1%num) Nflip (Gtyp (Fuint_implicit 0)) (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 0)) 2) Fnil))) (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 0)) 2) Fnil))).
Definition testgt := (Fuint 4).
Definition testbty1 := (Btyp (Fflips (1%num) Nflip (Gtyp (Fuint_implicit 0)) (Fflips (2%num) Nflip (Gtyp (Fuint_implicit 0)) Fnil))).
(*Compute (ft_find_sub testbty 4%num).*)
(*Compute (ft_set_sub testbty testgt 7%num).*)
(*Compute (ft_check_flip testbty 9%num false).*)
Compute (split_expr (N0, N0) testbty1).
Compute (split_expr_non_passive (N0, N0) testbty1 false).

Fixpoint combine_mux_expr (c : HiFP.hfexpr) (el1 el2 : seq HiFP.hfexpr) : option (seq HiFP.hfexpr) :=
  match el1, el2 with
  | nil, nil => Some nil
  | hd1 :: tl1, hd2 :: tl2 => match combine_mux_expr c tl1 tl2 with
                            | Some muxl => Some ((Emux c hd1 hd2) :: muxl)
                            | None => None
                            end
  | _, _ => None
  end.

Fixpoint split_expr_connect (expr_src : HiFP.hfexpr) (t : ftype) : option (seq HiFP.hfexpr) :=
  match expr_src with
  | Eref (Eid ref) => match split_expr ref t with
                | Some refl => Some (map (fun tref => (Eref (Eid tref))) refl)
                | None => None
                end
  | Eref _ => None
  | Emux c e1 e2 => match split_expr_connect e1 t, split_expr_connect e2 t with
                  | Some el1, Some el2 => combine_mux_expr c el1 el2
                  | _ ,_ => None
                  end
  | _ => Some [:: expr_src] 
  end.

Fixpoint add_expr_connect (vl : seq ProdVarOrder.t) (el : seq HiFP.hfexpr) (var2exprs : CEP.t (seq HiFP.hfexpr)) : option (CEP.t (seq HiFP.hfexpr)) :=
  match vl, el with
  | nil, nil => Some var2exprs
  | vhd :: vtl, hd :: tl => match CEP.find vhd var2exprs with
                          | Some ls => add_expr_connect vtl tl (CEP.add vhd (hd :: ls) var2exprs)
                          | None => add_expr_connect vtl tl (CEP.add vhd [::hd] var2exprs)
                          end
  | _, _ => None
  end.

Fixpoint add_nil_expr (vl : seq ProdVarOrder.t) (var2exprs : CEP.t (seq HiFP.hfexpr)) : (CEP.t (seq HiFP.hfexpr)) :=
  match vl with
  | nil => var2exprs
  | vhd :: vtl => match CEP.find vhd var2exprs with
                  | Some ls => add_nil_expr vtl var2exprs
                  | None => add_nil_expr vtl (CEP.add vhd [::] var2exprs)
                  end
  end.

Fixpoint add_expr_connect_non_passive (el1 el2 : seq (ProdVarOrder.t * bool)) (var2exprs : CEP.t (seq HiFP.hfexpr)) : option (CEP.t (seq HiFP.hfexpr)) :=
  match el1, el2 with
  | nil, nil => Some var2exprs
  | (ref1, false) :: tl1, (ref2, false) :: tl2 => 
                match CEP.find ref1 var2exprs with
                | Some ls => add_expr_connect_non_passive tl1 tl2 (CEP.add ref1 ((Eref (Eid ref2)) :: ls) var2exprs)
                | None => add_expr_connect_non_passive tl1 tl2 (CEP.add ref1 [::(Eref (Eid ref2))] var2exprs)
                end
  | (ref1, true) :: tl1, (ref2, _) :: tl2 => 
                match CEP.find ref2 var2exprs with
                | Some ls => add_expr_connect_non_passive tl1 tl2 (CEP.add ref2 ((Eref (Eid ref1)) :: ls) var2exprs)
                | None => add_expr_connect_non_passive tl1 tl2 (CEP.add ref2 [::(Eref (Eid ref1))] var2exprs)
                end
  | (ref1, _) :: tl1, (ref2, true) :: tl2 => 
                match CEP.find ref2 var2exprs with
                | Some ls => add_expr_connect_non_passive tl1 tl2 (CEP.add ref2 ((Eref (Eid ref1)) :: ls) var2exprs)
                | None => add_expr_connect_non_passive tl1 tl2 (CEP.add ref2 [::(Eref (Eid ref1))] var2exprs)
                end
  | _, _ => None
  end.

Fixpoint stmt_tmap (t_v : CEP.t ftype * CEP.t (seq HiFP.hfexpr)) (s: HiFP.hfstmt) : option (CEP.t ftype * CEP.t (seq HiFP.hfexpr)) :=
(* t_v is a pair: tmap of components defined before statement s;
                  map that indicates all expressions assigned to a certain ground-type part of a component.
   s is a statement.
   the result is the pair t_v expanded with the information from s *)
match s with
| Sskip => Some t_v
| Swire v t => if CEP.find v (fst t_v) is None
               then Some (CEP.add v t (fst t_v), (snd t_v))
               else None
| Sreg v r => match CEP.find v (fst t_v), reset r with
              | Some _, _ => None
              | None, Rst _ rst_val => match rst_val with
                                      | Eref (Eid rv) => if (v == rv) then Some (CEP.add v (type r) (fst t_v), snd t_v)
                                                          else match split_expr_connect rst_val (type r), split_expr v (type r) with
                                                          | Some rstl, Some vl => match add_expr_connect vl rstl (snd t_v) with
                                                                                  | Some nt_v => Some (CEP.add v (type r) (fst t_v), nt_v)
                                                                                  | _ => None
                                                                                  end
                                                          | _, _ => None
                                                          end
                                      | _ => match split_expr_connect rst_val (type r), split_expr v (type r) with
                                            | Some rstl, Some vl => match add_expr_connect vl rstl (snd t_v) with
                                                                    | Some nt_v => Some (CEP.add v (type r) (fst t_v), nt_v)
                                                                    | _ => None
                                                                    end
                                            | _, _ => None
                                            end
                                      end
              | None, NRst => Some (CEP.add v (type r) (fst t_v), (snd t_v))
              end
| Smem v m => (* TBD *) None
| Sinst v inst => (* TBD *) None
| Snode v e =>
    match CEP.find v (fst t_v), type_of_hfexpr e (fst t_v) with
    | None, Some t => match split_expr_connect e t, split_expr v t with
                    | Some rstl, Some vl => match add_expr_connect vl rstl (snd t_v) with
                                            | Some nt_v => Some (CEP.add v t (fst t_v), nt_v)
                                            | _ => None
                                            end
                    | _, _ => None
                    end
    | _, _ => None
    end
| Sfcnct (Eid ref_tgt) (Eref (Eid ref_src)) =>
    match type_ref ref_tgt (fst t_v), type_ref ref_src (fst t_v) with
    | Some t_tgt, Some t_src =>
      match split_expr_non_passive ref_tgt t_tgt false, split_expr_non_passive ref_src t_src false with
      | Some lhsl, Some rhsl => match add_expr_connect_non_passive lhsl rhsl (snd t_v) with
                                | Some newv2e => Some ((fst t_v), newv2e)
                                | None => None
                                end
      | _, _ => None
      end
    | _, _ => None
    end
| Sfcnct (Eid ref_tgt) (Eref _) => None
| Sfcnct (Eid ref_tgt) expr_src =>
    match type_ref ref_tgt (fst t_v), type_of_hfexpr expr_src (fst t_v) with
    | Some t_tgt, Some t_src =>
        match split_expr_connect expr_src t_src, split_expr ref_tgt t_tgt with
        | Some rstl, Some vl => match add_expr_connect vl rstl (snd t_v) with
                                | Some nt_v => Some ((fst t_v), nt_v)
                                | None => None
                                end
        | _, _ => None
        end
    | _,_ => None
    end
| Sfcnct _ _ => None
| Sinvalid (Eid ref_tgt) => match type_ref ref_tgt (fst t_v) with 
    | Some t_tgt => match split_expr ref_tgt t_tgt with
        | Some vl => Some((fst t_v), add_nil_expr vl (snd t_v))
        | None => None
        end
    | None => None
    end
| Sinvalid _ => None
| Swhen c ss_t ss_f =>
    match stmts_tmap t_v ss_t with
    | Some t_v' => stmts_tmap t_v' ss_f
    | None => None
    end
end
with stmts_tmap (t_v : CEP.t ftype * CEP.t (seq HiFP.hfexpr)) (ss: HiFP.hfstmt_seq) : option (CEP.t ftype * CEP.t (seq HiFP.hfexpr)) :=
match ss with
| Qnil => Some t_v
| Qcons s ss' =>
    match stmt_tmap t_v s with
    | Some t_v' => stmts_tmap t_v' ss'
    | None => None
    end
end.

Definition r1 := Sreg (0%num, 0%num) (mk_freg (Gtyp (Fuint 8)) (Eref (Eid (1%num, 0%num))) (Rst (Eref (Eid (2%num, 0%num))) (Econst ProdVarOrder.T (Fuint 1) [::b0]))).
Compute (match stmt_tmap (CEP.add (2%num, 0%num) (Gtyp Freset)(CEP.add (1%num, 0%num) (Gtyp Fclock) (CEP.empty ftype)), CEP.empty (seq HiFP.hfexpr)) r1 with
        | Some (tmap, var2exprs) => CEP.find (0%num, 0%num) tmap
        | _ => None
        end).

Fixpoint expr2varlist (expr : HiFP.hfexpr) : option (seq ProdVarOrder.t) :=
   (* Prepends to ls the list of variable/component identifiers accessed by the expression expr.
      DNJ: I think parameter ls is superfluous, it seems to be never used.  It could be replaced by [::]. *)
  match expr with
  | Econst _ _ => Some nil
  | Eref (Eid ref) => Some [:: ref] (* 根据var2expr，只包含gtyp element *)
  | Eref _ => None
  | Eprim_unop _ e1 => expr2varlist e1 
  | Eprim_binop _ e1 e2 => match expr2varlist e1, expr2varlist e2 with
                          | Some ls', Some ls'' => Some (ls' ++ ls'')
                          | _,_ => None
                          end
  | Emux e1 e2 e3 => match expr2varlist e1, expr2varlist e2, expr2varlist e3 with
                    | Some ls', Some ls'', Some ls''' => Some (ls' ++ ls'' ++ ls''')
                    | _,_,_ => None
                    end
  | Evalidif e1 e2 => match expr2varlist e1, expr2varlist e2 with
                      | Some ls', Some ls'' => Some (ls' ++ ls'')
                      | _,_ => None
                      end
  | Ecast _ e => expr2varlist e
   end.

Definition updg (key : ProdVarOrder.t) (v : seq ProdVarOrder.t) (map : ProdVarOrder.t -> seq ProdVarOrder.t) : ProdVarOrder.t -> seq ProdVarOrder.t :=
    fun (y : ProdVarOrder.t) => if y == key then v else map y.

Fixpoint drawel (v : ProdVarOrder.t) (el : seq HiFP.hfexpr) (newg : ProdVarOrder.t -> seq ProdVarOrder.t) (vertices : seq ProdVarOrder.t) : option ((ProdVarOrder.t -> seq ProdVarOrder.t) * (seq ProdVarOrder.t)) :=
   (* recursively draw dependencies in el for element v *)
   (* v: vertex in the dependency graph that is updated
      el: list of expressions that need to be considered for adding dependency edges
      tmap: map of (known) types of components
      newg: current edges in the dependency graph
      vertices: current vertices in the dependency graph
      Return value: a pair (edges in the dependency graph, vertices in the dependency graph)
      containing additionally the dependencies from el *)
   match el with
   | nil => Some (newg, vertices)
   | e :: etl => let vl := expr2varlist e in
                 match vl with (* all elements appearing in e *)
                 | Some ls => let g' := List.fold_left (fun tempg tempv => updg tempv (cons v (tempg tempv)) tempg) ls newg in
                              drawel v etl g' (vertices ++ ls)
                 | None => None
                 end
   end.

Fixpoint drawg depandencyls (expli_reg : seq ProdVarOrder.t) (newg : ProdVarOrder.t -> seq ProdVarOrder.t) (vertices : seq ProdVarOrder.t) : option ((ProdVarOrder.t -> seq ProdVarOrder.t) * (seq ProdVarOrder.t)) :=
   (* construct the dependency graph:
      depandencyls: list of pairs (vertex in the module graph, list of expressions)
      expli_reg: list of completely explicit-width components; they can be ignored
      newg: current edges in the dependency graph (will be extended by drawel)
      vertices: current vertices in the dependency graph (will be extended by drawel)
      Return value: a pair (edges in the dependency graph, vertices in the dependency graph)
      *)
   match depandencyls with
   (* list of all pairs (element as key, its connections as value) *)
   | nil => Some (newg, vertices)
  | (v, el) :: vtl => if ((fst v, N0) \in expli_reg) then drawg vtl expli_reg newg vertices
                      else match drawel v el newg vertices with (* for a certain element v, draw dependencies in the el to newg *)
                      | Some (g', vertices') => drawg vtl expli_reg g' (v :: vertices')
                      | None => None
                      end
  end.

Fixpoint drawreg (lsreg : seq ProdVarOrder.t) (var2exprs : CEP.t (seq HiFP.hfexpr)) (newg : ProdVarOrder.t -> seq ProdVarOrder.t) (vertices : seq ProdVarOrder.t) : option ((ProdVarOrder.t -> seq ProdVarOrder.t) * (seq ProdVarOrder.t)) :=
  match lsreg with
  | nil => Some (newg, vertices)
  | hd :: tl => match CEP.find hd var2exprs with
                | Some el => match drawel hd el newg vertices with
                            | Some (g', vertices') => drawreg tl var2exprs g' (hd :: vertices')
                            | None => None
                            end
                | _ => None
                end
  end.
(*Fixpoint list_expligref (tl : seq fgtyp) (vl : seq ProdVarOrder.t) : option (seq ProdVarOrder.t) := 
  match tl, vl with
  | nil, nil => Some nil
  | thd :: ttl, vhd :: vtl => match list_expligref ttl vtl with
                | Some ls => if not_implicit thd then Some (vhd :: ls) else Some ls
                | _ => None
                end
  | _, _ => None
  end.

Fixpoint explireg_stmt (st : HiFP.hfstmt) : option (seq ProdVarOrder.t) :=
  match st with
  | Sskip => Some nil 
  | Swire v t => Some nil
  | Sreg v r => list_expligref (list_gtyp (type r)) (list_gtypref v (type r))
  | Smem v m => (*TBD*) Some nil
  | Sinst v inst => (*TBD*) Some nil
  | Snode v e => Some nil
  | Sfcnct v e => Some nil
  | Sinvalid _ => Some nil
  | Swhen _ s1 s2 => match explireg_stmts s1 , explireg_stmts s2 with
                    | Some ls, Some ls' => Some (ls ++ ls')
                    | _,_ => None
                    end
  end
with explireg_stmts (sts : HiFP.hfstmt_seq) :=
  match sts with
  | Qnil => Some nil
  | Qcons s ss => match explireg_stmt s, explireg_stmts ss with
                  | Some ls, Some ls' => Some (ls ++ ls')
                  | _,_ => None
                  end
  end.*)

Fixpoint lsreg_stmt (st : HiFP.hfstmt) : option (seq ProdVarOrder.t) :=
  match st with
  | Sskip => Some nil 
  | Swire v t => Some nil
  | Sreg v r => Some (list_gtypref v (type r))
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

Definition emptyg : (ProdVarOrder.t -> seq ProdVarOrder.t) := (fun _ => [::]).

(************** InferWidths Implementation ********************)

(* return a fgtyp with the larger width for gtyp ft2 *)
Definition max_fgtyp (ft1 : fgtyp) (ft2 : fgtyp) : option fgtyp :=
  match ft1, ft2 with
  | Fuint w1, Fuint_implicit w2 => Some (Fuint_implicit (max w1 w2))
  | Fsint w1, Fsint_implicit w2 => Some (Fsint_implicit (max w1 w2))
  | Fuint_implicit w1, Fuint_implicit w2 => Some (Fuint_implicit (max w1 w2))
  | Fsint_implicit w1, Fsint_implicit w2 => Some (Fsint_implicit (max w1 w2))
  | _,_ => None
  end.

(* init 应该是implicit，l中无所谓 *)
Fixpoint max_ftlist (l : seq fgtyp) (init : fgtyp): option fgtyp :=
  match l with
  | nil => Some init
  | t :: tl => match max_ftlist tl init with
              | Some t' => max_fgtyp t t'
              | None => None
              end
  end.
  
Fixpoint fil_ftlist (l : seq (option ftype)) : option (seq fgtyp) :=
  match l with
  | nil => Some [::]
  | (Some (Gtyp gt)) :: tl => match fil_ftlist tl with
                      | Some tl' => Some (gt :: tl')
                      | None => None
                      end
  | _ :: tl => None
  end.

Definition InferWidth_fun (v : ProdVarOrder.t) (el : seq HiFP.hfexpr) (tmap : CEP.t ftype) : option (CEP.t ftype) :=
(* updates the width of v in tmap so that it is at least the width of the expressions in list el. *)
  match fil_ftlist (map (fun e => type_of_hfexpr e tmap) el) with
  | Some eftl => match CEP.find (fst v, N0) tmap with
                | Some init => match ft_find_sub init (snd v) with
                              | Some (Gtyp initt) => if not_implicit initt then Some tmap
                                                       else match max_ftlist eftl initt with
                                                        | Some nt => match ft_set_sub init nt (snd v) with
                                                                    | Some nt0 => Some (CEP.add (fst v, N0) nt0 tmap)
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
  
Fixpoint InferWidths_fun (od : seq ProdVarOrder.t) (var2exprs : CEP.t (seq HiFP.hfexpr)) (tmap : CEP.t ftype) : option (CEP.t ftype) :=
(* od contains the (implicit-width) ground-type subcomponents in topological order.
   (It is ok if od contains other components, but it is not necessary.)
   var2exprs is a map that maps every ground-type subcomponent to a list of expressions (namely expressions that the (sub)component is connected from).
   tmap is the map of types for every component that has been defined (but there are no separate entries for subcomponents);
   the result is a modified tmap, which ensures that the width of every implicit-width component is large enough. *)
  match od with
  | nil => Some tmap
  | vhd :: vtl => match CEP.find vhd var2exprs with 
                  | Some el => match InferWidth_fun vhd el tmap with
                          | Some tm => InferWidths_fun vtl var2exprs tm
                          | None => None
                          end
                  | None => InferWidths_fun vtl var2exprs tmap
                  end
  end.

Definition InferWidths_stage1 (F : HiFP.hfmodule) : option (CEP.t ftype) :=
(* infer widths of implicit-width components among the ports and statements in F.
   A full version would not work on one module alone but on all modules in a circuit together,
   but the principle remains the same. Therefore, let’s just run the algorithm on a single module for now. *)
match F with
| FExmod _ _ _ => None
| FInmod v ps ss =>
    match stmts_tmap (ports_tmap ps, CEP.empty (seq HiFP.hfexpr)) ss, lsreg_stmts ss with
    | Some (tmap', var2exprs), Some lsreg => (* tmap' : all the expli/uninferred impli aggr&gtyp are stored here
                                            var2exprs : every connected elements are stored *)
           match drawg (CEP.elements var2exprs) lsreg emptyg nil, drawreg lsreg var2exprs emptyg nil with
           | Some (theg, vertices), Some (regg, regvs) => (* theg : new drawn graph
                                         vertices : set for topo sort to start with *)
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
           | _, _ => None
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

Definition InferWidths_transp (p : HiFP.hfport) (tmap : CEP.t ftype) : option HiFP.hfport :=
  (* changes the type in one port declaration, depending on the information in tmap, to an explicit-width type *)
  match p with
  | Finput v t => if (ftype_not_implicit t) then Some p
                  else (match CEP.find v tmap with
                  | Some ft => (* if t has implicit width, update the hfport with ft and change it to explicit width *)
                                Some (Finput v (expli_ftype ft))
                  | _ => None
                  end)
  | Foutput v t => if (ftype_not_implicit t) then Some p
                  else (match CEP.find v tmap with
                  | Some ft => (* if t has implicit width, update the hfport with ft and change it to explicit width *)
                                Some (Foutput v (expli_ftype ft))
                  | _ => None
                  end)
  end.

Fixpoint InferWidths_transps (ps : seq HiFP.hfport) (tmap : CEP.t ftype) : option (seq HiFP.hfport) :=
  (* changes the types in a sequence of port declarations, depending on the information in tmap, to explicit-width types *)
  match ps with
  | nil => Some nil
  | p :: tl => match InferWidths_transp p tmap, InferWidths_transps tl tmap with
                  | Some n, Some nss => Some (n :: nss)
                  | _, _ => None
                  end
  end.

Fixpoint InferWidths_transs (s : HiFP.hfstmt) (tmap : CEP.t ftype) : option HiFP.hfstmt :=
(* with infered tmap, transform the ports and declarations *)
  match s with
  | Sskip => Some s
  | Swire v t => if (ftype_not_implicit t) then Some s
                  else (match CEP.find v tmap with
                  | Some ft => (* if t has implicit width, update the hfstmt with ft and change it to explicit width *)
                                Some (Swire v (expli_ftype ft))
                  | _ => None
                  end)
  | Sreg v r => if (ftype_not_implicit (type r)) then Some s
                else (match CEP.find v tmap with
                | Some ft => (* if t has implicit width, update the hfstmt with ft and change it to explicit width *)
                              Some (Sreg v (mk_freg (expli_ftype ft) (clock r) (reset r)))
                | _ => None
                end)
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
with InferWidths_transss (sts : HiFP.hfstmt_seq) (tmap : CEP.t ftype) : option HiFP.hfstmt_seq :=
  match sts with
  | Qnil => Some (Qnil ProdVarOrder.T)
  | Qcons s ss => match InferWidths_transs s tmap, InferWidths_transss ss tmap with
                  | Some n, Some nss => Some (Qcons n nss)
                  | _, _ => None
                  end
  end.

Definition InferWidths_stage2 (F : HiFP.hfmodule) (tmap : CEP.t ftype) : option HiFP.hfmodule :=
match F with
  | FExmod _ _ _ => None
  | FInmod v ps ss => match InferWidths_transps ps tmap, InferWidths_transss ss tmap with
                      | Some nps, Some nss => Some (FInmod v nps nss)
                      | _, _ => None
                      end
  end.

(************** InferWidths Proof ********************)

Lemma num_ref_eq : forall checkt nt0, ftype_equiv checkt nt0 -> num_ref checkt = num_ref nt0
with num_ref_eq_f : forall checkf nf0, fbtyp_equiv checkf nf0 -> num_ff checkf = num_ff nf0.
Proof.
  clear num_ref_eq.
  elim.
  intros gt nt0 Heq.
  case Hnt0 : nt0 => [gt0||]; rewrite Hnt0 in Heq; try discriminate.
  simpl; done.

  intros f H n nt0 Heq.
  case Hnt0 : nt0 => [|atyp na|]; rewrite Hnt0 in Heq; try discriminate.
  intros; simpl in Heq; simpl.
  move /andP : Heq => [H0 Heq].
  move /eqP : H0 => H0; rewrite H0.
  apply H in Heq; rewrite Heq; done.

  intros f nt0 Heq. 
  case Hnt0 : nt0 => [||btyp]; rewrite Hnt0 in Heq; try discriminate.
  simpl; simpl in Heq.
  apply num_ref_eq_f in Heq; rewrite Heq; done.

  clear num_ref_eq_f.
  elim.
  intros.
  simpl in H.
  case Hnf0 : nf0; rewrite Hnf0 in H; try discriminate; try done.
  intros v fl ft ff H nf0 Heq.
  case Hnf0 :  nf0 => [|v' fl' ft' ff']; rewrite Hnf0 in Heq; simpl in Heq; case Hf : fl; rewrite Hf in Heq; try discriminate.
  case Hf' : fl'; rewrite Hf' in Heq; try discriminate.
  move /andP : Heq => [Heq0 Heq1].
  move /andP : Heq0 => [_ Heq2].
  apply num_ref_eq in Heq2.
  apply H in Heq1.
  simpl; rewrite Heq1 Heq2; done.
  case Hf' : fl'; rewrite Hf' in Heq; try discriminate.
  move /andP : Heq => [Heq0 Heq1].
  move /andP : Heq0 => [_ Heq2].
  apply num_ref_eq in Heq2.
  apply H in Heq1.
  simpl; rewrite Heq1 Heq2; done.
Qed.

Lemma set_find_sub : forall checkt nt nt0 n, ft_set_sub checkt nt n = Some nt0 -> ftype_equiv checkt nt0 -> ft_find_sub nt0 n = Some (Gtyp nt)
with set_find_sub_f : forall checkf nf nf0 n, ft_set_sub_f checkf nf n = Some nf0 -> fbtyp_equiv checkf nf0 -> ft_find_ff nf0 n = Some (Gtyp nf).
Proof.
  clear set_find_sub.
  elim.
  intros f nt nt0 n Hset Heq.
  simpl in Heq.
  simpl in Hset.
  case Ha : (n == 0%num); rewrite Ha in Hset; try discriminate.
  inversion Hset; clear Hset H0.
  case Hnt0 : (nt0) => [f0||]; rewrite Hnt0 in Heq; try discriminate.
  simpl; rewrite Ha; done.

  intros f H fn nt nt0 n Hset Heq.
  simpl in Hset.
  case Ha0 : (n == 0%num); rewrite Ha0 in Hset.
  inversion Hset; clear Hset.
  case Ht : nt0 => [|atyp na|]; rewrite Ht in Heq; simpl in Heq; try discriminate.
  simpl; rewrite Ha0.
  move /andP : Heq => [Heq0 Heq1].
  generalize Heq1.
  apply num_ref_eq in Heq1; move /eqP : Heq0 => Heq0; rewrite -Heq0 -Heq1.
  move => Heq1'.
  case Ha1 : (num_ref f * fn <= N.to_nat n - 1); rewrite Ha1 in Hset; try discriminate.
  case Ha : ((N.to_nat n - 1) mod num_ref f == 0).
  move /eqP : Ha => Ha; rewrite Ha in Hset.
  case Hset' : (ft_set_sub f nt (N.of_nat 0)) => [natyp|]; rewrite Hset' in Hset; try discriminate.
  case Hf : f => [gt||]; rewrite Hf in Hset'; simpl in Hset'; try discriminate.
  inversion Hset'; inversion Hset; clear Hset' Hset.
  rewrite -H2 -H1 in Ht.
  inversion Ht; done.
  apply H; try done. 
  case Hset' : (ft_set_sub f nt (N.of_nat ((N.to_nat n - 1) mod num_ref f))) => [natyp|]; 
    rewrite Hset' in Hset; try discriminate.
  rewrite Ht in Hset.
  inversion Hset; clear Hset; done.

  intros f nt nt0 n Hset Heq.
  simpl in Hset.
  case Ha : (n == 0%num); rewrite Ha in Hset; try discriminate.
  case Hset' : (ft_set_sub_f f nt n) => [newf|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  simpl.
  rewrite Ha.
  apply set_find_sub_f in Hset'.
  rewrite Hset'; done.
  rewrite -H0 in Heq.
  simpl in Heq; done.

  clear set_find_sub_f.
  intros checkf.
  induction checkf.
  intros nf nf0 n Hset Heq.
  simpl in Hset; discriminate.

  intros nf nf0 n Hset Heq.
  simpl in Hset.
  case Hnf0 :  nf0 => [|v' fl' ft' ff']; rewrite Hnf0 in Heq; simpl in Heq; case Hf : f; rewrite Hf in Heq; try discriminate.
  case Hf' : fl'; rewrite Hf' in Heq; try discriminate.
  simpl.
  case Hn : (n == 1%num).
  move /eqP : Hn => Hn; rewrite Hn in Hset.
  assert ((num_ref f0 < N.to_nat 1) = false).
  admit.
  rewrite H in Hset.
  rewrite N.sub_diag in Hset.
  case Hset' : (ft_set_sub f0 nf 0) => [newt'|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset; rewrite Hnf0 in H1.
  inversion H1; clear H1.
  rewrite -H4 -Hset'.
  case Hf0 : f0 => [gt||]; rewrite Hf0 in Hset'; simpl in Hset'; try discriminate.
  simpl; done.
  move /andP : Heq => [Heq0 Heq1].
  move /andP : Heq0 => [_ Heq2].
  generalize Heq2.
  apply num_ref_eq in Heq2; rewrite -Heq2.
  move => Heq2'.
  case Ha : (num_ref f0 < N.to_nat n); rewrite Ha in Hset.
  case Hset' : (ft_set_sub_f checkf nf (N.of_nat (N.to_nat n - num_ref f0))) => [newf|]; rewrite Hset' in Hset; try discriminate.
  rewrite Hnf0 in Hset.
  inversion Hset; clear Hset.
  rewrite H3 in Hset'; rewrite -Heq2.
  move : Hset' Heq1.
  apply IHcheckf.
  case Hset' : (ft_set_sub f0 nf (n - 1)) => [newt'|]; rewrite Hset' in Hset; try discriminate.
  rewrite Hnf0 in Hset; inversion Hset; clear Hset.
  rewrite H2 in Hset'.
  move : Hset' Heq2'.
  apply set_find_sub.
    (* same case *)
    case Hf' : fl'; rewrite Hf' in Heq; try discriminate.
    simpl.
    case Hn : (n == 1%num).
    move /eqP : Hn => Hn; rewrite Hn in Hset.
    assert ((num_ref f0 < N.to_nat 1) = false).
    admit.
    rewrite H in Hset.
    rewrite N.sub_diag in Hset.
    case Hset' : (ft_set_sub f0 nf 0) => [newt'|]; rewrite Hset' in Hset; try discriminate.
    inversion Hset; clear Hset; rewrite Hnf0 in H1.
    inversion H1; clear H1.
    rewrite -H4 -Hset'.
    case Hf0 : f0 => [gt||]; rewrite Hf0 in Hset'; simpl in Hset'; try discriminate.
    simpl; done.
    move /andP : Heq => [Heq0 Heq1].
    move /andP : Heq0 => [_ Heq2].
    generalize Heq2.
    apply num_ref_eq in Heq2; rewrite -Heq2.
    move => Heq2'.
    case Ha : (num_ref f0 < N.to_nat n); rewrite Ha in Hset.
    case Hset' : (ft_set_sub_f checkf nf (N.of_nat (N.to_nat n - num_ref f0))) => [newf|]; rewrite Hset' in Hset; try discriminate.
    rewrite Hnf0 in Hset.
    inversion Hset; clear Hset.
    rewrite H3 in Hset'; rewrite -Heq2.
    move : Hset' Heq1.
    apply IHcheckf.
    case Hset' : (ft_set_sub f0 nf (n - 1)) => [newt'|]; rewrite Hset' in Hset; try discriminate.
    rewrite Hnf0 in Hset; inversion Hset; clear Hset.
    rewrite H2 in Hset'.
    move : Hset' Heq2'.
    apply set_find_sub.
Admitted.

Lemma ft_set_sub_eq : forall checkt nt' nt0 n init, ft_find_sub checkt n = Some init -> ftype_equiv init (Gtyp nt') -> ft_set_sub checkt nt' n = Some nt0 -> ftype_equiv checkt nt0
with ft_set_sub_eq_f : forall checkf nf' nf0 n init, ft_find_ff checkf n = Some init -> ftype_equiv init (Gtyp nf') -> ft_set_sub_f checkf nf' n = Some nf0 -> fbtyp_equiv checkf nf0.
Proof.
  clear ft_set_sub_eq.
  elim.
  intros f nt nt0 n init Hfind Heq Hset.
  simpl in Hset.
  case Hn : (n == 0%num); rewrite Hn in Hset; try discriminate.
  inversion Hset; simpl.
  move /eqP : Hn => Hn; rewrite Hn in Hfind; simpl in Hfind; inversion Hfind; clear Hfind.
  rewrite -H1 in Heq; simpl in Heq; done.

  (* set aggt *)
  intros f H n0 nt nt0 n init Hfind Heq Hset.
  simpl in Hset.
  simpl in Hfind.
  case Ha0 : (n == 0%num); rewrite Ha0 in Hset Hfind; try discriminate.
  case Hn : (num_ref f * n0 <= N.to_nat n - 1); rewrite Hn in Hset Hfind; try discriminate.

  case Ha : ((N.to_nat n - 1) mod num_ref f == 0); rewrite Ha in Hfind.
  move /eqP : Ha => Ha; rewrite Ha in Hset.
  case Hset' : (ft_set_sub f nt (N.of_nat 0)) => [natyp|]; rewrite Hset' in Hset; try discriminate.
  case Hf : f => [gt||]; rewrite Hf in Hset'; simpl in Hset'; try discriminate.
  inversion Hset'; inversion Hset; inversion Hfind; clear Hset' Hset Hfind.
  rewrite -Hf H3 -H1; simpl; rewrite eq_refl Heq //.
  case Hset' : (ft_set_sub f nt (N.of_nat ((N.to_nat n - 1) mod num_ref f))) => [natyp|]; 
    rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  simpl; rewrite eq_refl.
  apply H with (init := init) in Hset'; try done.

  (* set btyp *)
  intros f nt nt0 cnt init Hfind Heq Hset.
  simpl in Hfind.
  simpl in Hset.
  case Ha : (cnt == 0%num); rewrite Ha in Hfind Hset; try discriminate.
  case Hfind' : (ft_find_ff f cnt) => [newf|]; rewrite Hfind' in Hfind; try discriminate.
  case Hset' : (ft_set_sub_f f nt cnt) => [nf|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  simpl.
  inversion Hfind; clear Hfind.
  rewrite H1 in Hfind'.
  apply ft_set_sub_eq_f with (nf' := nt) (n := cnt) (init := init); try done.
  
  (* field *)
  clear ft_set_sub_eq_f.
  induction checkf.
  intros.
  simpl in H; discriminate.
  intros nt nf0 cnt init Hfind Heq Hset.
  simpl in Hfind.
  simpl in Hset.
  case Ha : (cnt == 1%num); rewrite Ha in Hfind.
  move /eqP : Ha => Ha; rewrite Ha in Hset. 
  assert ((num_ref f0 < N.to_nat 1) = false).
  admit.
  rewrite H in Hset.
  rewrite N.sub_diag in Hset.
  case Hset' : (ft_set_sub f0 nt 0) => [newt'|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset; simpl.
  case Hf0 : f0 => [gt0||]; rewrite Hf0 in Hset'; try discriminate.
  simpl in Hset'; inversion Hset'; simpl.
  inversion Hfind; clear Hfind; rewrite -H3 Hf0 in Heq; simpl in Heq.
  case Hf: f; rewrite eq_refl fbtyp_equiv_refl Heq; done.
  case Hn : (num_ref f0 < N.to_nat cnt); rewrite Hn in Hset Hfind.
  case Hset' : (ft_set_sub_f checkf nt (N.of_nat (N.to_nat cnt - num_ref f0))) => [newf|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  apply IHcheckf with (init := init) in Hset'; try done.
  simpl.
  case Hf : f; rewrite eq_refl ftype_equiv_refl Hset'; done.
  case Hset' : (ft_set_sub f0 nt (cnt - 1)) => [newt'|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  simpl.
  apply ft_set_sub_eq with (init := init) in Hset'; try done.
  case Hf: f; rewrite eq_refl fbtyp_equiv_refl Hset'; done.
Admitted.

Lemma infer_compatible : forall te otype nt, max_fgtyp te otype = Some nt -> connect_fgtyp_compatible nt otype /\ connect_fgtyp_compatible nt te.
Proof.
  intros.
  (* ground match ground *)
  case Hgt : te => [w'|w'|w'|w'|||]; rewrite Hgt in H.
  (* te = Gtyp (uint w') *)
  - case Hogt : otype => [ow'|ow'|ow'|ow'|||]; rewrite Hogt in H; simpl in H; try discriminate.
    (* otype = Gtyp (uint ow') *)
    inversion H; clear H. 
    rewrite /connect_fgtyp_compatible.
    simpl.
    rewrite Nat.max_comm.
    split.
    apply rwP with (P := (ow' <= Nat.max ow' w') /\ true).
    apply andP.
    split; try done. 
    apply Nats.le_leq; apply Nat.le_max_l.
    apply rwP with (P := (w' <= Nat.max ow' w') /\ true).
    apply andP.
    split; try done. 
    apply Nats.le_leq; apply Nat.le_max_r.
  - case Hogt : otype => [ow'|ow'|ow'|ow'|||]; rewrite Hogt in H; simpl in H; try discriminate.
    (* otype = Gtyp (uint ow') *)
    inversion H; clear H. 
    rewrite /connect_fgtyp_compatible.
    simpl.
    rewrite Nat.max_comm.
    split.
    apply rwP with (P := (ow' <= Nat.max ow' w') /\ true).
    apply andP.
    split; try done. 
    apply Nats.le_leq; apply Nat.le_max_l.
    apply rwP with (P := (w' <= Nat.max ow' w') /\ true).
    apply andP.
    split; try done. 
    apply Nats.le_leq; apply Nat.le_max_r.
  - case Hogt : otype => [ow'|ow'|ow'|ow'|||]; rewrite Hogt in H; simpl in H; try discriminate.
    (* otype = Gtyp (uint ow') *)
    inversion H; clear H. 
    rewrite /connect_fgtyp_compatible.
    simpl.
    rewrite Nat.max_comm.
    split.
    apply rwP with (P := (ow' <= Nat.max ow' w') /\ true).
    apply andP.
    split; try done. 
    apply Nats.le_leq; apply Nat.le_max_l.
    apply rwP with (P := (w' <= Nat.max ow' w') /\ true).
    apply andP.
    split; try done. 
    apply Nats.le_leq; apply Nat.le_max_r.
  - case Hogt : otype => [ow'|ow'|ow'|ow'|||]; rewrite Hogt in H; simpl in H; try discriminate.
    (* otype = Gtyp (uint ow') *)
    inversion H; clear H. 
    rewrite /connect_fgtyp_compatible.
    simpl.
    rewrite Nat.max_comm.
    split.
    apply rwP with (P := (ow' <= Nat.max ow' w') /\ true).
    apply andP.
    split; try done. 
    apply Nats.le_leq; apply Nat.le_max_l.
    apply rwP with (P := (w' <= Nat.max ow' w') /\ true).
    apply andP.
    split; try done. 
    apply Nats.le_leq; apply Nat.le_max_r.
  - case Hogt : otype => [ow'|ow'|ow'|ow'|||]; rewrite Hogt in H; simpl in H; try discriminate.
  - case Hogt : otype => [ow'|ow'|ow'|ow'|||]; rewrite Hogt in H; simpl in H; try discriminate.
  - case Hogt : otype => [ow'|ow'|ow'|ow'|||]; rewrite Hogt in H; simpl in H; try discriminate.
Qed.

Lemma max_compatible' : forall gte gt tmax, max_fgtyp gte gt = Some tmax -> (sizeof_fgtyp gte <= sizeof_fgtyp tmax) && fgtyp_equiv tmax gte && fgtyp_equiv tmax gt && (sizeof_fgtyp gt <= sizeof_fgtyp tmax).
Proof.
  intros.
  case Hgte : gte => [w'|w'|w'|w'|||]; rewrite Hgte in H.
  (* gte = Gtyp (uint w') *)
  - case Hgt : gt => [ow'|ow'|ow'|ow'|||]; rewrite Hgt in H; simpl in Hgt; simpl in H; try discriminate.
    inversion H; clear H.
    simpl.
    rewrite Nat.max_comm.
    apply rwP with (P := (w' <= Nat.max ow' w') && true && true /\ (ow' <= Nat.max ow' w')).
    apply andP.
    split; try apply Nats.le_leq; try apply Nat.le_max_l.
    apply rwP with (P := (w' <= Nat.max ow' w') && true /\ true).
    apply andP.
    split; try done.
    apply rwP with (P := (w' <= Nat.max ow' w') /\ true).
    apply andP.
    split; try done; try apply Nats.le_leq; try apply Nat.le_max_r.
  - case Hgt : gt => [ow'|ow'|ow'|ow'|||]; rewrite Hgt in H; simpl in Hgt; simpl in H; try discriminate.
    inversion H; clear H.
    simpl.
    rewrite Nat.max_comm.
    apply rwP with (P := (w' <= Nat.max ow' w') && true && true /\ (ow' <= Nat.max ow' w')).
    apply andP.
    split; try apply Nats.le_leq; try apply Nat.le_max_l.
    apply rwP with (P := (w' <= Nat.max ow' w') && true /\ true).
    apply andP.
    split; try done.
    apply rwP with (P := (w' <= Nat.max ow' w') /\ true).
    apply andP.
    split; try done; try apply Nats.le_leq; try apply Nat.le_max_r.
  - case Hgt : gt => [ow'|ow'|ow'|ow'|||]; rewrite Hgt in H; simpl in Hgt; simpl in H; try discriminate.
    inversion H; clear H.
    simpl.
    rewrite Nat.max_comm.
    apply rwP with (P := (w' <= Nat.max ow' w') && true && true /\ (ow' <= Nat.max ow' w')).
    apply andP.
    split; try apply Nats.le_leq; try apply Nat.le_max_l.
    apply rwP with (P := (w' <= Nat.max ow' w') && true /\ true).
    apply andP.
    split; try done.
    apply rwP with (P := (w' <= Nat.max ow' w') /\ true).
    apply andP.
    split; try done; try apply Nats.le_leq; try apply Nat.le_max_r.
  - case Hgt : gt => [ow'|ow'|ow'|ow'|||]; rewrite Hgt in H; simpl in Hgt; simpl in H; try discriminate.
    inversion H; clear H.
    simpl.
    rewrite Nat.max_comm.
    apply rwP with (P := (w' <= Nat.max ow' w') && true && true /\ (ow' <= Nat.max ow' w')).
    apply andP.
    split; try apply Nats.le_leq; try apply Nat.le_max_l.
    apply rwP with (P := (w' <= Nat.max ow' w') && true /\ true).
    apply andP.
    split; try done.
    apply rwP with (P := (w' <= Nat.max ow' w') /\ true).
    apply andP.
    split; try done; try apply Nats.le_leq; try apply Nat.le_max_r.
  - case Hgt : gt => [ow'|ow'|ow'|ow'|||]; rewrite Hgt in H; simpl in Hgt; simpl in H; try discriminate.
  - case Hgt : gt => [ow'|ow'|ow'|ow'|||]; rewrite Hgt in H; simpl in Hgt; simpl in H; try discriminate.
  - case Hgt : gt => [ow'|ow'|ow'|ow'|||]; rewrite Hgt in H; simpl in Hgt; simpl in H; try discriminate.
Qed.

Lemma max_compatible : forall el tmap eftl initt tmax, fil_ftlist (map (fun e => type_of_hfexpr e tmap) el) = Some eftl -> forall expr gte, expr \in el -> type_of_hfexpr expr tmap = Some (Gtyp gte) -> max_ftlist eftl initt = Some tmax -> (sizeof_fgtyp gte <= sizeof_fgtyp tmax) && fgtyp_equiv tmax gte.
Proof.
  elim.
  intros.
  rewrite in_nil in H0; discriminate.
  intros hd tl IH tmap eftl initt tmax Hfil expr gte Hin Hgte Hmax.
  rewrite in_cons in Hin.
  case Heq : (expr == hd).
  (* case1 *)
  move /eqP : Heq => Heq.
  rewrite Heq in Hgte.
  simpl in Hfil. 
  rewrite Hgte in Hfil. 
  case Hfil' : (fil_ftlist [seq type_of_hfexpr e tmap | e <- tl]) => [eftl'|]; rewrite Hfil' in Hfil; try discriminate.
  inversion Hfil; clear Hfil.
  rewrite -H0 in Hmax.
  simpl in Hmax.
  case Hmax' : (max_ftlist eftl' initt) => [tmax'|]; rewrite Hmax' in Hmax; try discriminate.
  specialize max_compatible' with (gte := gte) (gt := tmax') (tmax := tmax); intro.
  apply H in Hmax; clear H.
  move /andP : Hmax => [H1 _].
  move /andP : H1 => [H1 _]; done.
  (* case2 *)
  rewrite Heq in Hin.
  rewrite orb_false_l in Hin; clear Heq.
  simpl in Hfil.
  case Hhd : (type_of_hfexpr hd tmap) => [t|]; rewrite Hhd in Hfil;  try discriminate.
  case Hgt : t =>[gt||]; rewrite Hgt in Hfil; try discriminate.
  case Hfil' : (fil_ftlist [seq type_of_hfexpr e tmap | e <- tl]) => [eftl'|]; rewrite Hfil' in Hfil; try discriminate.
  inversion Hfil; clear Hfil.
  rewrite -H0 in Hmax.
  simpl in Hmax.
  case Hmax' : (max_ftlist eftl' initt) => [tmax'|]; rewrite Hmax' in Hmax; try discriminate.
  apply IH with (initt := initt) (tmax := tmax') (expr := expr) (gte := gte) in Hfil'; try done.
  move /andP : Hfil' => [H1 H2].
  apply rwP with (P := (sizeof_fgtyp gte <= sizeof_fgtyp tmax) /\ fgtyp_equiv tmax gte).
  apply andP.
  split.
  specialize max_compatible' with (gte := gt) (gt := tmax') (tmax := tmax); intro H.
  apply H in Hmax; clear H.
  move /andP : Hmax => [_ H3].
  move : H1 H3.
  apply leq_trans.
  specialize max_compatible' with (gte := gt) (gt := tmax') (tmax := tmax); intro H.
  apply H in Hmax; clear H.
  move /andP : Hmax => [Hmax _].
  move /andP : Hmax => [_ H3].
  move : H3 H2.
  apply fgtyp_equiv_dlvr.
Qed.

Lemma set_find_sub_neq : forall (a1 v1 : N) ft nt nt0, (a1 == v1) = false -> ft_set_sub ft nt v1 = Some nt0 -> ft_find_sub ft a1 = ft_find_sub nt0 a1.
Proof.
  
Admitted.

Lemma inferwidths_a : forall a v expr_seq tmap tmap', InferWidth_fun v expr_seq tmap = Some tmap' -> 
  if (a != v) then 
  match CEP.find (fst a, N0) tmap, CEP.find (fst a, N0) tmap' with
        | Some ft, Some ft' => ft_find_sub ft (snd a) = ft_find_sub ft' (snd a)
        | _, _ => True
        end
  else True.
Proof.
  intros.
  destruct a as [a0 a1]; destruct v as [v0 v1].
  case Heq : (a0 == v0).
  case Heq' : (a1 == v1).
  move /eqP : Heq => Heq; move /eqP : Heq' => Heq'.
  rewrite Heq Heq'; simpl.
  admit.
  assert ((a0, a1) != (v0, v1)).
  admit.
  rewrite H0; clear H0; simpl.
  case Ha : (CEP.find (a0, 0%num) tmap) => [ft|]; try done.
  case Ha' : (CEP.find (a0, 0%num) tmap') => [ft'|]; try done.
  rewrite /InferWidth_fun in H.
  case Hel : (fil_ftlist [seq type_of_hfexpr e tmap | e <- expr_seq]) => [eftl|]; rewrite Hel in H; try discriminate.
  simpl in H; move /eqP : Heq => Heq; rewrite -Heq Ha in H.
  case Hsub : (ft_find_sub ft v1) => [initt|]; rewrite Hsub in H; try discriminate.
  case Hinitt : initt => [initt'||]; rewrite Hinitt in H; try discriminate.
  case Himpli : (not_implicit initt'); rewrite Himpli in H.
  (* case1 *)
  inversion H; clear H.
  rewrite H1 in Ha.
  rewrite Ha in Ha'.
  inversion Ha'; done.
  (* case2 *)
  case Hmax : (max_ftlist eftl initt') => [nt|]; rewrite Hmax in H; try discriminate.
  case Hinfer : (ft_set_sub ft nt v1) => [nt0|]; rewrite Hinfer in H; try discriminate.
  inversion H; clear H.
  rewrite -H1 in Ha'.
  rewrite HiFP.PCELemmas.OP.P.F.add_eq_o in Ha'; try apply CEP.SE.eq_refl.
  inversion Ha'; clear Ha'; rewrite -H0.
  move : Heq' Hinfer.
  apply set_find_sub_neq.
  
  assert ((a0, a1) != (v0, v1)).
  admit.
  rewrite H0; clear H0; simpl.
  case Ha : (CEP.find (a0, 0%num) tmap) => [ft|]; try done.
  case Ha' : (CEP.find (a0, 0%num) tmap') => [ft'|]; try done.
  rewrite /InferWidth_fun in H.
  case Hel : (fil_ftlist [seq type_of_hfexpr e tmap | e <- expr_seq]) => [eftl|]; rewrite Hel in H; try discriminate.
  case Hfindv0 : (CEP.find (v0, 0%num) tmap) => [init|]; rewrite Hfindv0 in H; try discriminate.
  case Hsub : (ft_find_sub init v1) => [initt|]; rewrite Hsub in H; try discriminate.
  case Hinitt : initt => [initt'||]; rewrite Hinitt in H; try discriminate.
  case Himpli : (not_implicit initt'); rewrite Himpli in H.
  (* case1 *)
  inversion H; clear H.
  rewrite H1 in Ha.
  rewrite Ha in Ha'.
  inversion Ha'; done.
  (* case2 *)
  case Hmax : (max_ftlist eftl initt') => [nt|]; rewrite Hmax in H; try discriminate.
  case Hinfer : (ft_set_sub init nt v1) => [nt0|]; rewrite Hinfer in H; try discriminate.
  inversion H; clear H.
  rewrite -H1 in Ha'.
  rewrite HiFP.PCELemmas.OP.P.F.add_neq_o in Ha'.
  rewrite Ha' in Ha. 
  inversion Ha; done.
Admitted.

Lemma inferwidths_ls : forall el a var2exprs tmap tmap' checkt checkt', InferWidths_fun el var2exprs tmap = Some tmap' -> 
  ~~(a \in el) -> CEP.find (fst a, N0) tmap' = Some checkt' -> CEP.find (fst a, N0) tmap = Some checkt -> ft_find_sub checkt (snd a) = ft_find_sub checkt' (snd a).
Proof.
  elim.
  intros.
  simpl in H. 
  inversion H; clear H. 
  rewrite H4 in H2.
  rewrite H2 in H1.
  inversion H1; done.
  intros hd tl IH a var2exprs tmap tmap' checkt checkt' Hinfer Hin Hcheckt' Hcheckt.
  rewrite in_cons in Hin.
  rewrite negb_or in Hin.
  move /andP : Hin => [H H1].
  simpl in Hinfer.
  case Hel : (CEP.find hd var2exprs) => [el|]; rewrite Hel in Hinfer; try discriminate.
  case Hinfer' : (InferWidth_fun hd el tmap) => [newtm|]; rewrite Hinfer' in Hinfer; try discriminate.
  specialize inferwidths_a with (v := hd) (a := a) (expr_seq := el) (tmap := tmap) (tmap' := newtm); intro.
  apply H0 in Hinfer'; clear H0.
  rewrite H Hcheckt in Hinfer'.
  case Hnewtm : (CEP.find (a.1, 0%num) newtm) => [newt|]; rewrite Hnewtm in Hinfer'.
  apply IH with (a:= a) (checkt := newt) (checkt' := checkt') in Hinfer; try done.
  rewrite Hinfer' -Hinfer; done.
  admit. (* Hnewtm 不是None *)
Admitted.

Lemma max_ftlist_correct : forall eftl initt tmax, max_ftlist eftl initt = Some tmax -> (not_implicit initt = false -> not_implicit tmax = false) /\ fgtyp_equiv initt tmax.
Proof.
  elim.
  intros.
  split.
  intros.
  simpl in H. 
  inversion H.
  rewrite -H2; done.
  simpl in H. 
  inversion H.
  apply fgtyp_equiv_refl.

  intros hd tl H init nt Hl.
  split.
  intro Himpli.
  simpl in Hl. 
  case Htl : (max_ftlist tl init) => [nt'|]; rewrite Htl in Hl; try discriminate.
  apply H in Htl; try done.
  rewrite /max_fgtyp in Hl.
  case Hhd : hd; rewrite Hhd in Hl; try discriminate.
  case Hnt' : nt'; rewrite Hnt' in Hl Htl; try discriminate; inversion Hl; simpl; try done.
  case Hnt' : nt'; rewrite Hnt' in Hl Htl; try discriminate; inversion Hl; simpl; try done.
  case Hnt' : nt'; rewrite Hnt' in Hl Htl; try discriminate; inversion Hl; simpl; try done.
  case Hnt' : nt'; rewrite Hnt' in Hl Htl; try discriminate; inversion Hl; simpl; try done.

  simpl in Hl. 
  case Htl : (max_ftlist tl init) => [nt'|]; rewrite Htl in Hl; try discriminate.
  apply H in Htl; try done.
  move : Htl => [_ Htl].
  specialize max_compatible' with (gte := hd) (gt := nt') (tmax := nt); intro.
  apply H0 in Hl; clear H0.
  move /andP : Hl => [H1 _].
  move /andP : H1 => [_ H1].
  assert (fgtyp_equiv nt' nt).
  apply fgtyp_equiv_comm; done.
  move : Htl H0.
  apply fgtyp_equiv_dlvr.
Qed.

(* modulegraph_simplified type_of_expr_submap *)
Lemma type_of_hfexpr_eq : forall (expr : HiFP.hfexpr) (pv : ProdVarOrder.t) (nt0 : ftype) (tmap : CEP.t ftype), type_of_hfexpr expr (CEP.add (pv.1, 0%num) nt0 tmap) = type_of_hfexpr expr tmap.
Proof.
Admitted.

Lemma InferWidth_fun_correct : forall pv el tmap newtm, InferWidth_fun pv el tmap = Some newtm -> forall expr, expr \in el -> 
      match CEP.find (fst pv, N0) newtm with
      | Some checkt => match ft_find_sub checkt pv.2, type_of_hfexpr expr newtm with
                              | Some (Gtyp nt), Some (Gtyp te) => fgtyp_equiv nt te -> connect_fgtyp_compatible nt te
                              | _,_ => true
                              end
      | _ => true
      end.
Proof.
  intros pv el tmap newtm Hinfer expr Hin.
  rewrite /InferWidth_fun in Hinfer.
  case Hel : (fil_ftlist [seq type_of_hfexpr e tmap | e <- el]) => [eftl|]; rewrite Hel in Hinfer; try discriminate.
  case Hinit : (CEP.find (pv.1, 0%num) tmap) => [init|]; rewrite Hinit in Hinfer; try discriminate.
  case Hinitt : (ft_find_sub init pv.2) => [initt|]; rewrite Hinitt in Hinfer; try discriminate.
  case Hcheckt : (CEP.find (pv.1, 0%num) newtm) => [checkt|]; try done.
  case Hnt : (ft_find_sub checkt pv.2) => [nt|]; try done.
  case Hinitt' : nt => [initt'||]; try done.
  case Hinitt'' : initt => [initt''||]; rewrite Hinitt'' in Hinfer; try discriminate.
  case Hte : (type_of_hfexpr expr newtm) => [te|]; try done.
  case Hgte : te => [gte||]; rewrite Hgte in Hte; try done.
  intro Heq.
  case Himpli' : (not_implicit initt''); rewrite Himpli' in Hinfer.
  inversion Hinfer.
  rewrite H0 in Hinit; rewrite Hinit in Hcheckt; inversion Hcheckt; rewrite H1 in Hinitt; rewrite Hinitt in Hnt; inversion Hnt; rewrite Hinitt'' Hinitt' in H2.
  inversion H2; rewrite H3 in Himpli'.
  rewrite /connect_fgtyp_compatible Himpli'; done.
  (* case2 *)
  case Hmax : (max_ftlist eftl initt'') => [tmax|]; rewrite Hmax in Hinfer; try discriminate.
  case Hset : (ft_set_sub init tmax pv.2) => [nt0|]; rewrite Hset in Hinfer; try discriminate.
  inversion Hinfer; clear Hinfer.
  rewrite -H0 in Hte Hcheckt; clear H0.
  rewrite HiFP.PCELemmas.OP.P.F.add_eq_o in Hcheckt; try apply CEP.SE.eq_refl.
  inversion Hcheckt; clear Hcheckt.
  rewrite -H0 in Hnt; clear H0.
  apply set_find_sub in Hset; try done.
  rewrite Hset in Hnt; clear Hset.
  inversion Hnt; clear Hnt.
  rewrite Hinitt' in H0; inversion H0; rewrite H1 in Hmax; clear H0 H1 tmax Hinitt' nt.
  generalize Hmax.
  apply max_ftlist_correct in Hmax; move : Hmax => [Hmax _]; apply Hmax in Himpli'; clear Hmax.
  move => Hmax.
  rewrite /connect_type_compatible.
  simpl.
  rewrite /connect_fgtyp_compatible.
  rewrite Himpli'.
  rewrite type_of_hfexpr_eq in Hte; try done.
  apply max_compatible with (el := el) (tmap := tmap) (eftl := eftl) (initt := initt'') (expr := expr); try done.
  apply ft_set_sub_eq with (nt' := tmax) (n := pv.2) (init := initt); try done.
  rewrite Hinitt''; simpl.
  apply max_ftlist_correct with (eftl := eftl) (initt := initt'') (tmax := tmax); done.
Qed.

Lemma ft_check_flip_rev : forall ft n b b0, ft_check_flip ft n b0 = Some b -> ft_check_flip ft n (~~b0) = Some (~~b)
with ft_check_flip_rev_f : forall ft n b b0, ft_check_flip_f ft n b0 = Some b -> ft_check_flip_f ft n (~~b0) = Some (~~b).
Proof.
  elim.
  intros.
  simpl; simpl in H.
  case Hn : n; rewrite Hn in H.
  rewrite eq_refl.
  rewrite eq_refl in H.
  inversion H; done.
  discriminate.

  intros.
  simpl; simpl in H0.
  case Hn : (n0 == 0%num); rewrite Hn in H0; try discriminate.
  inversion H0; done.
  case Hn' : (num_ref f * n <= N.to_nat n0 - 1); rewrite Hn' in H0; try discriminate.
  apply H in H0; done.

  clear ft_check_flip_rev.
  intros.
  simpl; simpl in H.
  case Hn : (n == 0%num); rewrite Hn in H; try discriminate.
  inversion H; done.
  apply ft_check_flip_rev_f in H; done.

  clear ft_check_flip_rev_f.
  elim.
  intros.
  simpl in H; discriminate.
  intros.
  simpl; simpl in H0.
  case Hf : f; rewrite Hf in H0.
  case Hn : (num_ref f0 < N.to_nat n); rewrite Hn in H0.
  apply H in H0; done.
  apply ft_check_flip_rev in H0; done.
  case Hn : (num_ref f0 < N.to_nat n); rewrite Hn in H0.
  apply H in H0; done.
  apply ft_check_flip_rev in H0; done.
Qed.

Lemma ft_check_flip0 : forall ft b, ft_check_flip ft 0 b = Some b.
Proof.
  intro ft.
  case : ft; simpl; done.
Qed.

Lemma ftype_eq_find_some : forall t1 t2 n te, ftype_equiv t1 t2 -> ft_find_sub t1 n = Some te -> 
  exists b, ft_check_flip t1 n false = Some b /\ exists te', ft_find_sub t2 n = Some te'
with fbtyp_eq_find_some : forall t1 t2 n te, fbtyp_equiv t1 t2 -> ft_find_ff t1 n = Some te -> 
  exists b, ft_check_flip_f t1 n false = Some b /\ exists te', ft_find_ff t2 n = Some te'.
Proof.
  elim.
  intros.
  exists false.
  split.
  simpl.
  simpl in H0.
  case Hn : n; rewrite Hn in H0.
  rewrite eq_refl; done.
  discriminate.
  case Ht2 : t2 => [gt||]; rewrite Ht2 in H; simpl in H; try discriminate.
  simpl in H0.
  case Hn : (n == 0%num); rewrite Hn in H0; try discriminate.
  simpl; rewrite Hn.
  exists (Gtyp gt); done.

  intros.
  case Ht2 : t2 => [|atyp na|]; rewrite Ht2 in H0; simpl in H0; try discriminate.
  move /andP : H0 => [H0 H2].
  simpl in H1; simpl.
  case Hn : (n0 == 0%num); rewrite Hn in H1.
  exists false.
  split; try done.
  exists (Atyp atyp na); done.
  case Hn' : (num_ref f * n <= N.to_nat n0 - 1); rewrite Hn' in H1; try discriminate.
  generalize H2.
  apply num_ref_eq in H2; rewrite -H2.
  move => H2'.
  case Ha : ((N.to_nat n0 - 1) mod num_ref f == 0); rewrite Ha in H1.
  exists false.
  split.
  admit.
  exists atyp.
  admit.
  move /eqP : H0 => H0; rewrite -H0 Hn'.
  move : H1; apply H; try done.
  
  clear ftype_eq_find_some.
  intros.
  case Ht2 : t2 => [||btyp]; rewrite Ht2 in H; simpl in H; try discriminate.
  simpl in H0.
  generalize H.
  apply num_ref_eq_f in H.
  move => H'.
  case Hn : (n == 0%num); rewrite Hn in H0.
  move /eqP : Hn => Hn; rewrite Hn; simpl.
  exists false.
  split; try done.
  exists (Btyp btyp); done.
  case Hfind : (ft_find_ff f n) => [newf|]; rewrite Hfind in H0; try done.
  simpl; rewrite Hn.
  inversion H0; clear H0; rewrite H2 in Hfind.
  apply fbtyp_eq_find_some with (n := n) (te := te) in H'; try done.
  destruct H' as [b [H' [te' H'']]].
  exists b.
  split; try done.
  exists te'; rewrite H''; done.

  clear fbtyp_eq_find_some.
  elim.
  intros.
  simpl in H0; discriminate.
  intros.
  case Ht2 : t2 => [|v' f' f0' f1']; rewrite Ht2 in H0; simpl in H0.
  case Hf : f; rewrite Hf in H0; try discriminate.
  case Hf : f; rewrite Hf in H0; case Hf' : f'; rewrite Hf' in H0; try discriminate.
  move /andP : H0 => [H0 H2].
  move /andP : H0 => [H0 H3].
  simpl in H1.
  generalize H3.
  apply num_ref_eq in H3.
  move => H3'.
  simpl.
  case Hn : (n == 1%num); rewrite Hn in H1.
  move /eqP : Hn => Hn; rewrite Hn.
  assert ((num_ref f0 < N.to_nat 1) = false).
  admit.
  rewrite H4 N.sub_diag; clear H4.
  exists true.
  split; try apply ft_check_flip0; try exists f0'; done.
  rewrite -H3.
  case Hn' : (num_ref f0 < N.to_nat n); rewrite Hn' in H1.
  move : H1; apply H; try done.
  apply ftype_eq_find_some with (n := N.sub n 1) (te := te) in H3'; try done.
  destruct H3' as [b [H3' H4]].
  exists (~~b).
  split; try done.
  apply ft_check_flip_rev in H3'.
  assert (~~ false = true).
  simpl; done.
  rewrite H5 in H3'; clear H5; done.

  move /andP : H0 => [H0 H2].
  move /andP : H0 => [H0 H3].
  simpl in H1; simpl.
  generalize H3.
  apply num_ref_eq in H3.
  move => H3'.
  case Hn : (n == 1%num); rewrite Hn in H1.
  move /eqP : Hn => Hn; rewrite Hn.
  assert ((num_ref f0 < N.to_nat 1) = false).
  admit.
  rewrite H4 N.sub_diag; clear H4.
  exists false.
  split; try apply ft_check_flip0; try exists f0'; done.
  rewrite -H3.
  case Hn' : (num_ref f0 < N.to_nat n); rewrite Hn' in H1.
  move : H1; apply H; try done.
  move : H1; apply ftype_eq_find_some; try done.
Admitted.

Lemma ftype_eq_check_flip : forall t1 t2 n, ftype_equiv t1 t2 -> ft_check_flip t1 n = ft_check_flip t2 n
with fbtyp_eq_check_flip : forall t1 t2 n, fbtyp_equiv t1 t2 -> ft_check_flip_f t1 n = ft_check_flip_f t2 n. 
Proof.
  elim.
  intros.
  case Ht2 : t2 => [gt||]; rewrite Ht2 in H; simpl in H; try discriminate.
  simpl; done.

  intros.
  case Ht2 : t2 => [|atyp na|]; rewrite Ht2 in H0; simpl in H0; try discriminate.
  move /andP : H0 => [H0 H1].
  simpl.
  case Hn : (n0 == 0%num); try done.
  move /eqP : H0 => H0.
  generalize H1.
  apply num_ref_eq in H1.
  move => H1'.
  rewrite H0 H1.
  case Hn' : (num_ref atyp * na <= N.to_nat n0 - 1); try done.
  apply H with (n := (N.of_nat ((N.to_nat n0 - 1) mod num_ref atyp))) in H1'; rewrite H1'; done.

  clear ftype_eq_check_flip.
  intros.
  case Ht2 : t2 => [||btyp]; rewrite Ht2 in H; try discriminate.
  simpl in H; simpl.
  case Hn : (n == 0%num); try done.
  apply fbtyp_eq_check_flip with (n := n) in H; rewrite H; done.

  clear fbtyp_eq_check_flip.
  elim.
  intros.
  case Ht2 : t2; rewrite Ht2 in H; simpl in H; try discriminate; done.
  intros.
  case Ht2 : t2 => [|v' f' f0' f1']; rewrite Ht2 in H0; simpl in H0; case Hf : f; rewrite Hf in H0; try discriminate.
  case Hf' : f'; rewrite Hf' in H0; try discriminate.
  simpl.
  move /andP : H0 => [H0 H1].
  move /andP : H0 => [H0 H2].
  generalize H1.
  apply num_ref_eq_f in H1.
  move => H1'.
  generalize H2.
  apply num_ref_eq in H2.
  move => H2'.
  rewrite -H2.
  case Hn : (num_ref f0 < N.to_nat n).
  apply H with (n := (N.of_nat (N.to_nat n - num_ref f0))) in H1'; done.
  apply ftype_eq_check_flip with (n:= N.sub n 1%num) in H2'.
  rewrite H2'; done.
  case Hf' : f'; rewrite Hf' in H0; try discriminate.
  simpl.
  move /andP : H0 => [H0 H1].
  move /andP : H0 => [H0 H2].
  generalize H1.
  apply num_ref_eq_f in H1.
  move => H1'.
  generalize H2.
  apply num_ref_eq in H2.
  move => H2'.
  rewrite -H2.
  case Hn : (num_ref f0 < N.to_nat n).
  apply H with (n := (N.of_nat (N.to_nat n - num_ref f0))) in H1'; done.
  apply ftype_eq_check_flip with (n:= N.sub n 1%num) in H2'.
  rewrite H2'; done.
Qed.

Lemma infer_cons_order : forall order1 order2 var2exprs tmap tmap' newtm, InferWidths_fun (order1 ++ order2) var2exprs tmap = Some newtm -> InferWidths_fun order1 var2exprs tmap = Some tmap' ->
  InferWidths_fun order2 var2exprs tmap' = Some newtm.
Proof.
  (*elim. 
  intros.
  simpl in H0.
  inversion H0; clear H0.
  rewrite H2 in H.
  simpl in H; done.
  intros hd tl IH order2 var2exprs tmap tmap' newtm H H0.
  simpl in H; simpl in H0.
  case Hhd : (CEP.find hd var2exprs) => [el|]; rewrite Hhd in H H0; try discriminate.
  case Hinfer : (InferWidth_fun hd el tmap) => [tm|]; rewrite Hinfer in H H0; try discriminate.
  move : H H0.
  apply IH.
Qed.*)
(* TBD!! *)
Admitted.

Lemma mux_types_eq : forall t1 t2 t, mux_types t1 t2 = Some t -> ftype_equiv t1 t2 /\ ftype_equiv t2 t
with mux_btyps_eq : forall t1 t2 t, mux_btyps t1 t2 = Some t -> fbtyp_equiv t1 t2 /\ fbtyp_equiv t2 t.
Proof.
  elim.
  intros.
  case Ht2 : t2 => [gt||]; rewrite Ht2 in H; simpl in H; try discriminate.
  case Hmux : (mux_gtyp f gt) => [gte|]; rewrite Hmux in H; try discriminate.
  inversion H. 
  case Hf : f => [w|w|w|w|||]; rewrite Hf in Hmux.
  case Hgt : gt => [w'|w'|w'|w'|||]; rewrite Hgt in Hmux; simpl in Hmux; try discriminate; inversion Hmux; simpl; done.
  case Hgt : gt => [w'|w'|w'|w'|||]; rewrite Hgt in Hmux; simpl in Hmux; try discriminate; inversion Hmux; simpl; done.
  case Hgt : gt => [w'|w'|w'|w'|||]; rewrite Hgt in Hmux; simpl in Hmux; try discriminate; inversion Hmux; simpl; done.
  case Hgt : gt => [w'|w'|w'|w'|||]; rewrite Hgt in Hmux; simpl in Hmux; try discriminate; inversion Hmux; simpl; done.
  case Hgt : gt => [w'|w'|w'|w'|||]; rewrite Hgt in Hmux; simpl in Hmux; try discriminate; inversion Hmux; simpl; done.
  case Hgt : gt => [w'|w'|w'|w'|||]; rewrite Hgt in Hmux; simpl in Hmux; try discriminate; inversion Hmux; simpl; done.
  case Hgt : gt => [w'|w'|w'|w'|||]; rewrite Hgt in Hmux; simpl in Hmux; try discriminate; inversion Hmux; simpl; done.
  
  intros.
  case Ht2 : t2 => [|atyp na|]; rewrite Ht2 in H0; simpl in H0; try discriminate.
  case Hn : (n == na); rewrite Hn in H0; try discriminate.
  case Hmux : (mux_types f atyp) => [gte|]; rewrite Hmux in H0; try discriminate; inversion H0; clear H0.
  move /eqP : Hn => Hn.
  simpl.
  rewrite Hn eq_refl.
  apply H in Hmux.
  move : Hmux => [Hmux Hmux'].
  rewrite Hmux Hmux'; done.

  clear mux_types_eq.
  intros.
  case Ht2 : t2 => [||btyp]; rewrite Ht2 in H; simpl in H; try discriminate.
  case Hmux : (mux_btyps f btyp) => [ff|]; rewrite Hmux in H; try discriminate; inversion H; clear H.
  simpl.
  apply mux_btyps_eq in Hmux; done.

  clear mux_btyps_eq.
  elim.
  intros.
  case Ht2 : t2; rewrite Ht2 in H; simpl in H; try discriminate.
  inversion H.
  simpl; done.
  intros.
  case Ht2 : t2 => [|v' f' f0' f1']; rewrite Ht2 in H0; simpl in H0; case Hf : f; rewrite Hf in H0; try discriminate.
  case Hf' : f'; rewrite Hf' in H0; try discriminate.
  case Hv : (v == v'); rewrite Hv in H0; try discriminate.
  case Hmux : (mux_types f0 f0') => [nt|]; rewrite Hmux in H0; try discriminate.
  case Hmux' : (mux_btyps f1 f1') => [nf|]; rewrite Hmux' in H0; try discriminate.
  inversion H0; clear H0.
  move /eqP : Hv => Hv.
  simpl.
  rewrite Hv eq_refl.
  apply mux_types_eq in Hmux.
  move : Hmux => [Hmux H0].
  rewrite Hmux H0.
  apply H in Hmux'.
  move : Hmux' => [Hmux' H3].
  rewrite Hmux' H3; done.
Qed.

(*Lemma find_mux_types_n : forall t1 t2 t_expr tt1 tt2 n tt, mux_types t1 t2 = Some t_expr -> ft_find_sub t1 n = Some (Gtyp tt1) -> 
  ft_find_sub t2 n = Some (Gtyp tt2) -> mux_gtyp tt1 tt2 = Some tt -> ft_find_sub t_expr n = Some (Gtyp tt)
with find_mux_types_n_f : forall t1 t2 t_expr tt1 tt2 n tt, mux_btyps t1 t2 = Some t_expr -> ft_find_ff t1 n = Some (Gtyp tt1) -> 
ft_find_ff t2 n = Some (Gtyp tt2) -> mux_gtyp tt1 tt2 = Some tt -> ft_find_ff t_expr n = Some (Gtyp tt).
Proof.
Admitted.*)

Lemma combine_mux_expr_n : forall el1 el2 rhs_expr_ls n e1 e2 c, combine_mux_expr c el1 el2 = Some rhs_expr_ls -> 
  nth_error el1 n = Some e1 -> nth_error el2 n = Some e2 -> nth_error rhs_expr_ls n = Some (Emux c e1 e2).
Proof.
  elim.
  intros.
  apply nth_error_In in H0.
  apply List.in_nil in H0; done.
  intros hd tl IH.
  elim.
  intros.
  apply nth_error_In in H1.
  apply List.in_nil in H1; done.
  intros hd0 tl0 H; clear H.
  intros.
  simpl in H. 
  case Hcombine : (combine_mux_expr c tl tl0) => [muxl|]; rewrite Hcombine in H; try discriminate.
  inversion H; clear H.
  case Hn : n => [|n']; rewrite Hn in H0 H1; simpl in H0; simpl in H1.
  inversion H0; inversion H1.
  simpl; done.
  assert (Emux c hd hd0 :: muxl = [::Emux c hd hd0] ++ muxl).
  simpl; done.
  rewrite H; clear H.
  apply IH with (n := n') (e1 := e1) (e2 := e2) in Hcombine; try done.
Qed.

Lemma ftype_equiv_split_ref_eq : forall (t1 t2 : ftype) ref0, ftype_equiv t1 t2 -> split_expr ref0 t1 = split_expr ref0 t2
with fbtyp_equiv_split_ref_eq : forall t1 t2 ref0, fbtyp_equiv t1 t2 -> split_expr_f ref0 t1 = split_expr_f ref0 t2.
Proof.
Admitted.

Lemma ftype_equiv_split_eq : forall s t1 t2, ftype_equiv t1 t2 -> split_expr_connect s t1 = split_expr_connect s t2.
Proof.
Admitted.

Lemma mux_expr_type_equiv : forall c s1 s2 tmap te te1 te2, type_of_hfexpr (Emux c s1 s2) tmap = Some te -> type_of_hfexpr s1 tmap = Some te1 -> 
  type_of_hfexpr s2 tmap = Some te2 -> ftype_equiv te te1 /\ ftype_equiv te te2.
Proof.
  intros.
  simpl in H.
  case Hc : (type_of_hfexpr c tmap) => [f|]; rewrite Hc in H; try discriminate.
  case Hf : f => [gt||]; rewrite Hf in H; try discriminate.
  case Hgt : gt => [w|w|w|w|||]; rewrite Hgt in H; try discriminate.
  case Hw : w => [|n0]; rewrite Hw in H; try discriminate.
  case Hn0 : n0; rewrite Hn0 in H; try discriminate.
  rewrite H0 H1 in H.
  apply mux_types_eq in H.
  move : H => [H H2].
  apply ftype_equiv_dlvr with (t1 := te1) (t2 := te2) (t3 := te) in H; try done.
  split; try apply ftype_equiv_comm; try done.
  case Hw : w => [|n0]; rewrite Hw in H; try discriminate.
  case Hn0 : n0; rewrite Hn0 in H; try discriminate.
  rewrite H0 H1 in H.
  apply mux_types_eq in H.
  move : H => [H H2].
  apply ftype_equiv_dlvr with (t1 := te1) (t2 := te2) (t3 := te) in H; try done.
  split; try apply ftype_equiv_comm; try done.
Qed.

Lemma check_connect_fgtyp_compatible4n : forall ft te, (forall n,
  match nth_error ft n, nth_error te n with
  | Some gt, Some gte => connect_fgtyp_compatible gt gte
  | None, None => true
  | _, _ => false
  end) -> check_connect_fgtyp_compatible ft te.
Proof.
  elim. 
  elim.
  simpl; done.
  intros.
  admit.
  intros hd tl H. 
  elim. 
  intro.
  admit.
  intros hd' tl' H0 IH; clear H0.
  specialize H with (te := tl').
  simpl. 
  apply rwP with (P := connect_fgtyp_compatible hd hd' /\ check_connect_fgtyp_compatible tl tl').
  apply andP. split.
  specialize IH with (n := 0); simpl in IH; done.
  apply H.
  intro.
  specialize IH with (n := n+1).
  assert (hd :: tl = [::hd] ++ tl).
  simpl; done.
  assert (nth_error (hd :: tl) (n + 1) = nth_error tl n).
  rewrite H0.
  admit.
  assert (nth_error (hd' :: tl') (n + 1) = nth_error tl' n).
  admit.
  rewrite H1 H2 in IH; done.
Admitted.

Lemma check_connect_non_passive_fgtyp4n : forall fl ft te, (forall n, 
  match nth_error fl n, nth_error ft n, nth_error te n with
  | Some true, Some gt, Some gte => connect_fgtyp_compatible gte gt
  | Some false, Some gt, Some gte => connect_fgtyp_compatible gt gte
  | None, None, None => true
  | _, _, _ => false
  end) -> check_connect_non_passive_fgtyp ft te fl.
Proof.
  elim.
  intros.
  admit.
  intros fhd ftl H0.
  elim.
  intros. 
  admit.
  intros hd tl H1; clear H1.
  elim.
  intros.
  admit.
  intros hd' tl' H2 IH; clear H2.
  simpl.
  case Hf : (fhd).
  (* flip *)
  admit.
  (* nflip *)
  specialize H0 with (ft := tl) (te := tl').
  apply rwP with (P := connect_fgtyp_compatible hd hd' /\ check_connect_non_passive_fgtyp tl tl' ftl).
  apply andP. split.
  specialize IH with (n := 0); simpl in IH; rewrite Hf in IH; try done.
  apply H0; clear H0.
  intro n.
  specialize IH with (n := n+1).
  assert (nth_error (fhd :: ftl) (n + 1) = nth_error ftl n).
  admit.
  assert (nth_error (hd :: tl) (n + 1) = nth_error tl n).
  admit.
  assert (nth_error (hd' :: tl') (n + 1) = nth_error tl' n).
  admit.
  rewrite H H0 H1 in IH; done.
Admitted.

Lemma find_mux_types_n : forall t1 t2 t_expr tt1 tt2 n, mux_types t1 t2 = Some t_expr -> nth_error (list_gtyp t1) n = Some tt1 -> 
  nth_error (list_gtyp t2) n = Some tt2 -> mux_gtyp tt1 tt2 = nth_error (list_gtyp t_expr) n
with find_mux_types_n_f : forall t1 t2 t_expr tt1 tt2 n, mux_btyps t1 t2 = Some t_expr -> nth_error (list_gtyp_ff t1) n = Some tt1 -> 
  nth_error (list_gtyp_ff t2) n = Some tt2 -> mux_gtyp tt1 tt2 = nth_error (list_gtyp_ff t_expr) n.
Proof.
  clear find_mux_types_n.
  elim.
  intros.
  case Ht2 : t2 => [gt||]; rewrite Ht2 in H H1; simpl in H; try discriminate.
  case Hmux : (mux_gtyp f gt) => [gte|]; rewrite Hmux in H; try discriminate.
  inversion H. 
  simpl in H0; simpl in H1; simpl.
  case Hn : n; rewrite Hn in H0 H1.
  simpl in H0; simpl in H1.
  inversion H0; clear H0.
  inversion H1; clear H1.
  rewrite -H2 -H4 Hmux.
  simpl; done.
  admit. (* H0 H1 为None *)

  intros.
  case Ht2 : t2 => [|atyp na|]; rewrite Ht2 in H0 H2; simpl in H0; try discriminate.
  case Hn : (n == na); rewrite Hn in H0; try discriminate.
  case Hmux : (mux_types f atyp) => [natyp|]; rewrite Hmux in H0; try discriminate.
  inversion H0; clear H0.
  simpl in H1; simpl in H2; simpl.
  apply H with (tt1 := tt1) (tt2 := tt2) (n :=n0) in Hmux; try done.

  intros.
  case Ht2 : t2 => [||btyp]; rewrite Ht2 in H H1; simpl in H; try discriminate.
  case Hmux : (mux_btyps f btyp) => [ff|]; rewrite Hmux in H; try discriminate.
  inversion H; clear H H3. 
  simpl in H0; simpl in H1; simpl.
  move : Hmux H0 H1.
  apply find_mux_types_n_f.

  clear find_mux_types_n_f.
  elim.
  intros.
  case Ht2 : t2; rewrite Ht2 in H; simpl in H; try discriminate.
  simpl in H0.
  apply nth_error_In in H0.
  apply List.in_nil in H0; done.
  intros.
  case Ht2 : t2 => [|v' f' f0' f1']; rewrite Ht2 in H0 H2; simpl in H0; case Hf : f ;rewrite Hf in H0; try discriminate.
  case Hf' : f'; rewrite Hf' in H0; try discriminate.
  case Hv : (v == v'); rewrite Hv in H0; try discriminate.
  case Hmux : (mux_types f0 f0') => [nt|]; rewrite Hmux in H0; try discriminate.
  case Hmux' : (mux_btyps f1 f1') => [nf|]; rewrite Hmux' in H0; try discriminate.
  simpl in H1; simpl in H2.
  inversion H0; clear H0 H4.
  simpl.
  case Hn : (n < length (list_gtyp nt)).
  assert (nth_error (list_gtyp nt ++ list_gtyp_ff nf) n = nth_error (list_gtyp nt) n).
  admit. (* nth_error_app1 *)
  assert (nth_error (list_gtyp f0 ++ list_gtyp_ff f1) n = nth_error (list_gtyp f0) n).
  admit. (* nth_error_app1 *)
  assert (nth_error (list_gtyp f0' ++ list_gtyp_ff f1') n = nth_error (list_gtyp f0') n).
  admit. (* nth_error_app1 *)
  rewrite H0; rewrite H3 in H1; rewrite H4 in H2.
  move : Hmux H1 H2.
  apply find_mux_types_n.
  assert (nth_error (list_gtyp nt ++ list_gtyp_ff nf) n = nth_error (list_gtyp_ff nf) (n - (length (list_gtyp nt)))).
  admit. (* nth_error_app2 *)
  assert (nth_error (list_gtyp f0 ++ list_gtyp_ff f1) n = nth_error (list_gtyp_ff f1) (n - (length (list_gtyp nt)))).
  admit. (* nth_error_app2 *)
  assert (nth_error (list_gtyp f0' ++ list_gtyp_ff f1') n = nth_error (list_gtyp_ff f1') (n - (length (list_gtyp nt)))).
  admit. (* nth_error_app2 *)
  rewrite H0; rewrite H3 in H1; rewrite H4 in H2.
  move : Hmux' H1 H2.
  apply H.
Admitted.

Lemma type_ref_atyp : forall e tmap f n, type_ref e tmap = Some (Atyp f n) -> type_ref (e.1, N.add e.2 1%num) tmap = Some (f).
Proof.
  intros.
  rewrite /type_ref; rewrite /type_ref in H; simpl.
  case Hfind : (CEP.find (e.1, 0%num) tmap) => [checkt|]; rewrite Hfind in H; try discriminate.
  case Ht : checkt => [gt|atyp na|btyp]; rewrite Ht in H.
  simpl in H.
  case He : (e.2 == 0%num); rewrite He in H; discriminate.
Admitted.

(*Lemma type_ref_btyp : forall e tmap v f f0 f1, type_ref e tmap = Some (Btyp (Fflips v f f0 f1)) -> type_ref (e.1, N.add e.2 1%num) tmap = Some (f0).
Proof.
Admitted.*)

Lemma split_ref_correct : forall ft e refl n e1 gt tmap, type_ref e tmap = Some ft -> split_expr e ft = Some refl -> nth_error [seq Eref (Eid (var:=ProdVarOrder.T) tref) | tref <- refl] n = Some e1 -> nth_error (list_gtyp ft) n = Some gt -> type_of_hfexpr e1 tmap = Some (Gtyp gt)
(*with split_ref_correct_f : forall ft e btyp tn refl n e1 gt tmap, CEP.find (e.1, tn) tmap = Some (Btyp btyp) -> ft_find_ff btyp (e.2 - tn) = Some ft -> split_expr_f e ft = Some refl -> nth_error [seq Eref (Eid (var:=ProdVarOrder.T) tref) | tref <- refl] n = Some e1 ->  nth_error (list_gtyp_ff ft) n = Some gt -> type_of_hfexpr e1 tmap = Some (Gtyp gt)*).
Proof.
  elim.
  intros.
  simpl in H0.
  inversion H0; clear H0.
  rewrite -H4 in H1.
  simpl in H1.
  case Hn : n => [|n']; rewrite Hn in H1 H2; try discriminate.
  simpl in H1; simpl in H2.
  inversion H1; clear H1.
  inversion H2; clear H2.
  simpl.
  rewrite H H1; done.
  simpl in H1; simpl in H2.
  apply nth_error_In in H1.
  apply List.in_nil in H1; done.

  intros.
  simpl in H1; simpl in H3.
  apply type_ref_atyp in H0.
  apply H with (n := n0) (e1 := e1) (gt := gt) (tmap := tmap) in H1; try done.

  intros.
  simpl in H0; simpl in H2. (*
  apply split_ref_correct_f with (refl := refl) (n := n) (e1 := e1) (gt := gt) in H; try done.

  clear split_ref_correct_f. *)
  (*elim. 不能elim，因为bundle里面的ffield，不是以bundle类型存，前提用不上 TBD
  intros.
  simpl in H0.
  inversion H0; clear H0.
  rewrite -H4 in H1; simpl in H1.
  apply nth_error_In in H1.
  apply List.in_nil in H1; done.

  intros.
  simpl in H1; simpl in H3.
  case Hf : f; rewrite Hf in H1; try discriminate.
  case Hsplit : (split_expr_f (e.1, (e.2 + N.of_nat (num_ref f0))%num) f1) => [ls|]; rewrite Hsplit in H1; try discriminate.
  case Hsplit1 : (split_expr (e.1, (e.2 + 1)%num) f0) => [ls'|]; rewrite Hsplit1 in H1; try discriminate.
  inversion H1; clear H1.
  rewrite -H5 in H2.
  case Hn : (n < length ls'). 
  assert (nth_error (list_gtyp f0 ++ list_gtyp_ff f1) n = nth_error (list_gtyp f0) n).
  admit.
  assert (nth_error [seq Eref (Eid (var:=ProdVarOrder.T) tref)| tref <- ls' ++ ls] n = nth_error [seq Eref (Eid (var:=ProdVarOrder.T) tref)| tref <- ls'] n).
  admit.
  rewrite H1 in H3; rewrite H4 in H2; clear H4 H1.
  apply type_ref_btyp in H0.
  
  ; rewrite Hn in H3.
  apply H with (n := n - (tmap_type_size f0)) (e1 := e1) (gt := gt) (tmap := tmap) (v := v0) in Hsplit; try done.
  admit. (* 重要！！归纳方法有点问题 *)
  admit.
  admit.
  apply split_ref_correct with (n := n) (e := (Esubfield e v)) (refl := ls') (e1 := e1) (tmap := tmap) (v := v0) in H3; try done.
  simpl.
  rewrite H0.
  simpl.
  rewrite eq_refl; done.
  admit.*)
Admitted.

Lemma split_expr_type_correct : forall expr rhs_expr_ls t_expr newtm, type_of_hfexpr expr newtm = Some t_expr -> split_expr_connect expr t_expr = Some rhs_expr_ls ->  (* 这里可以加bool list用来判断flip *)
  forall n, match nth_error (list_gtyp t_expr) n, List.nth_error rhs_expr_ls n with
            | Some gt, Some texpr => type_of_hfexpr texpr newtm = Some (Gtyp gt)
            | _, _ => true
            end.
Proof.
  elim.
  intros.
  simpl in H0.
  inversion H0; clear H0.
  assert (exists gt_expr, t_expr = Gtyp gt_expr).
  admit.
  destruct H0 as [gt_expr H0]; rewrite H0; simpl.
  induction n as [|n]; simpl.
  simpl in H; rewrite H0 in H; done. 
  admit. (* 空集中取元素一定为None *)

  (* 其他expr case *)
  admit.
  admit.
  admit.

  (* mux case *)
  intros c Hc s1 Hs1 s2 Hs2.
  intros rhs_expr_ls t_expr tmap Hte Hsplit.
  simpl in Hsplit.
  case Hsplit1 : (split_expr_connect s1 t_expr) => [el1|]; rewrite Hsplit1 in Hsplit; try discriminate.
  case Hsplit2 : (split_expr_connect s2 t_expr) => [el2|]; rewrite Hsplit2 in Hsplit; try discriminate.

  generalize Hte.
  simpl in Hte.
  move => Hte'. 
  case Hce : (type_of_hfexpr c tmap) => [f|]; rewrite Hce in Hte; try discriminate.
  case Hcf : f => [cgt||]; rewrite Hcf in Hte; try discriminate.
  case Hcgt : cgt => [w|w|w||||]; rewrite Hcgt in Hcf Hte; try discriminate.
  - (* case1 : c 为 uint1 *)
    case Hw : w => [|n0]; rewrite Hw in Hte; try discriminate.
    case Hw' : n0; rewrite Hw' in Hte Hw; try discriminate.
    rewrite Hw in Hcf; clear Hw Hw' Hcgt w n0 cgt.
    case Hs1e : (type_of_hfexpr s1 tmap) => [t1|]; rewrite Hs1e in Hte; try discriminate.
    case Hs2e : (type_of_hfexpr s2 tmap) => [t2|]; rewrite Hs2e in Hte; try discriminate.
    intro n. 
    case Hten : (nth_error (list_gtyp t_expr) n) => [gte|]; try done.
    case Hrhsn : (nth_error rhs_expr_ls n) => [texpr|]; try done.
    generalize Hs1e.
    apply Hs1 with (rhs_expr_ls := el1) (n:= n) in Hs1e; try done.
    move => Hs1e'.
    apply Hs2 with (rhs_expr_ls := el2) (n:= n) in Hs2e; try done.
    case Hs1n : (nth_error (list_gtyp t1) n) => [tt1|]; rewrite Hs1n in Hs1e.
    case Hs2n : (nth_error (list_gtyp t2) n) => [tt2|]; rewrite Hs2n in Hs2e.
    apply find_mux_types_n with (n := n) (tt1 := tt1) (tt2 := tt2) in Hte; try done.
    rewrite Hten in Hte; clear Hten.
    assert (exists e1, nth_error el1 n = Some e1).
    admit. (* t_expr 和 t1 满足ftype_equiv，由Hs1n 和 Hsplit1知el1的长度小于n *)
    destruct H as [e1 He1].
    assert (exists e2, nth_error el2 n = Some e2).
    admit.
    destruct H as [e2 He2].
    rewrite He1 in Hs1e; rewrite He2 in Hs2e.
    apply combine_mux_expr_n with (n := n) (el1 := el1) (el2 := el2) (e1 := e1) (e2 := e2) in Hsplit; try done.
    rewrite Hsplit in Hrhsn; clear Hsplit.
    inversion Hrhsn; clear Hrhsn H0.
    simpl.
    rewrite Hce Hcf Hs1e Hs2e.
    simpl; rewrite Hte; done.
    admit. (* not None *)
    admit. (* not None *)
    specialize ftype_equiv_split_eq with (s := s2) (t1 := t_expr) (t2 := t2); intro.
    rewrite H in Hsplit2.
    done.
    apply mux_expr_type_equiv with (c := c) (s1 := s1) (s2 := s2) (te := t_expr) (te1 := t1) (te2 := t2) in Hte'; try done.
    move : Hte' => [_ Hte']; done.
    specialize ftype_equiv_split_eq with (s := s1) (t1 := t_expr) (t2 := t1); intro.
    rewrite H in Hsplit1.
    done.
    apply mux_expr_type_equiv with (c := c) (s1 := s1) (s2 := s2) (te := t_expr) (te1 := t1) (te2 := t2) in Hte'; try done.
    move : Hte' => [Hte' _]; done.
  - (* case1 : c 为 uint_implicit1 *)
    case Hw : w => [|n0]; rewrite Hw in Hte; try discriminate.
    case Hw' : n0; rewrite Hw' in Hte Hw; try discriminate.
    rewrite Hw in Hcf; clear Hw Hw' Hcgt w n0 cgt.
    case Hs1e : (type_of_hfexpr s1 tmap) => [t1|]; rewrite Hs1e in Hte; try discriminate.
    case Hs2e : (type_of_hfexpr s2 tmap) => [t2|]; rewrite Hs2e in Hte; try discriminate.
    intro n. 
    case Hten : (nth_error (list_gtyp t_expr) n) => [gte|]; try done.
    case Hrhsn : (nth_error rhs_expr_ls n) => [texpr|]; try done.
    generalize Hs1e.
    apply Hs1 with (rhs_expr_ls := el1) (n:= n) in Hs1e; try done.
    move => Hs1e'.
    apply Hs2 with (rhs_expr_ls := el2) (n:= n) in Hs2e; try done.
    case Hs1n : (nth_error (list_gtyp t1) n) => [tt1|]; rewrite Hs1n in Hs1e.
    case Hs2n : (nth_error (list_gtyp t2) n) => [tt2|]; rewrite Hs2n in Hs2e.
    apply find_mux_types_n with (n := n) (tt1 := tt1) (tt2 := tt2) in Hte; try done.
    rewrite Hten in Hte; clear Hten.
    assert (exists e1, nth_error el1 n = Some e1).
    admit. (* t_expr 和 t1 满足ftype_equiv，由Hs1n 和 Hsplit1知el1的长度小于n *)
    destruct H as [e1 He1].
    assert (exists e2, nth_error el2 n = Some e2).
    admit.
    destruct H as [e2 He2].
    rewrite He1 in Hs1e; rewrite He2 in Hs2e.
    apply combine_mux_expr_n with (n := n) (el1 := el1) (el2 := el2) (e1 := e1) (e2 := e2) in Hsplit; try done.
    rewrite Hsplit in Hrhsn; clear Hsplit.
    inversion Hrhsn; clear Hrhsn H0.
    simpl.
    rewrite Hce Hcf Hs1e Hs2e.
    simpl; rewrite Hte; done.
    admit. (* not None *)
    admit. (* not None *)
    specialize ftype_equiv_split_eq with (s := s2) (t1 := t_expr) (t2 := t2); intro.
    rewrite H in Hsplit2.
    done.
    apply mux_expr_type_equiv with (c := c) (s1 := s1) (s2 := s2) (te := t_expr) (te1 := t1) (te2 := t2) in Hte'; try done.
    move : Hte' => [_ Hte']; done.
    specialize ftype_equiv_split_eq with (s := s1) (t1 := t_expr) (t2 := t1); intro.
    rewrite H in Hsplit1.
    done.
    apply mux_expr_type_equiv with (c := c) (s1 := s1) (s2 := s2) (te := t_expr) (te1 := t1) (te2 := t2) in Hte'; try done.
    move : Hte' => [Hte' _]; done.

  (* validif *)
  admit. (* validif *)

  (* ref *)
  intros ref.
  intros rhs_expr_ls t_expr tmap Hte Hsplit.
  simpl in Hsplit.
  case Href : ref => [r|||]; rewrite Href in Hsplit; try discriminate.
  case Hsplit1 : (split_expr r t_expr) => [refl|]; rewrite Hsplit1 in Hsplit; try discriminate.
  inversion Hsplit; clear Hsplit H0.
  simpl in Hte; rewrite Href in Hte. 
  intros n.
  case Hfind : (nth_error (list_gtyp t_expr) n) => [gt|]; try done.
  case Hnth : (nth_error [seq Eref (Eid (var:=ProdVarOrder.T) tref) | tref <- refl] n) => [texpr|]; try done.
  move : Hte Hsplit1 Hnth Hfind.
  apply split_ref_correct.
Admitted.

Fixpoint find_sub_expr' (pv : ProdVarOrder.t) (lhsl : seq ProdVarOrder.t) (rstl : seq HiFP.hfexpr) : option (seq HiFP.hfexpr) :=
  match lhsl, rstl with
  | nil, nil => Some nil
  | hd :: tl, hde :: tle => if (hd == pv) then Some [:: hde]
                              else find_sub_expr' pv tl tle
  | _, _ => None
  end.

Fixpoint find_sub_expr'0 (pv : ProdVarOrder.t) (lhsl rhsl : seq (ProdVarOrder.t * bool)) : option (seq HiFP.hfexpr) :=
  match lhsl, rhsl with
  | nil, nil => Some nil
  | (hd, true) :: tl, (hde, true) :: tle => if (hde == pv) then Some [:: (Eref (Eid hd))]
                                                            else find_sub_expr'0 pv tl tle
  | (hd, false) :: tl, (hde, false) :: tle => if (hd == pv) then Some [:: (Eref (Eid hde))]
                                                            else find_sub_expr'0 pv tl tle
  | _, _ => None
  end.

Fixpoint find_sub_expr (pv : ProdVarOrder.t) (s : HiFP.hfstmt) (tmap : CEP.t ftype) : option (seq HiFP.hfexpr) :=
  match s with
  | Sreg v r => match reset r with
                | NRst => Some nil
                | Rst _ rst_val => match split_expr_connect rst_val (type r), split_expr v (type r) with
                                  | Some rstl, Some lhsl => find_sub_expr' pv lhsl rstl
                                  | _, _ => None
                                  end
                end
  | Snode v e => match type_of_hfexpr e tmap with
                | Some t => match split_expr_connect e t, split_expr v t with
                            | Some rstl, Some lhsl => find_sub_expr' pv lhsl rstl
                            | _, _ => None
                            end
                | _ => None
                end
  | Sfcnct (Eid ref_tgt) (Eref (Eid ref_src)) =>
                match type_ref ref_tgt tmap, type_ref ref_src tmap with
                | Some t_tgt, Some t_src =>
                            match split_expr_non_passive ref_tgt t_tgt false, split_expr_non_passive ref_src t_src false with
                            | Some lhsl, Some rhsl => find_sub_expr'0 pv lhsl rhsl
                            | _, _ => None
                            end
                | _, _ => None
                end
  | Sfcnct (Eid ref_tgt) (Eref _) => None
  | Sfcnct (Eid ref_tgt) expr_src =>
                match type_ref ref_tgt tmap, type_of_hfexpr expr_src tmap with
                | Some t_tgt, Some t_src =>
                      match split_expr_connect expr_src t_src, split_expr ref_tgt t_tgt with
                      | Some rstl, Some lhsl => find_sub_expr' pv lhsl rstl
                      | _, _ => None
                      end
                | _, _ => None
                end
  | Swhen _ s1 s2 => match find_sub_exprs pv s1 tmap, find_sub_exprs pv s2 tmap with
                    | Some e1, Some e2 => Some (e1 ++ e2)
                    | _,_ => None
                    end
  | _ => Some nil
  end
with find_sub_exprs (v : ProdVarOrder.t) (ss : HiFP.hfstmt_seq) (tmap : CEP.t ftype) : option (seq HiFP.hfexpr) :=
  match ss with
  | Qnil => Some nil
  | Qcons s ss' => match find_sub_expr v s tmap, find_sub_exprs v ss' tmap with
                  | Some e, Some el => Some (e ++ el)
                  | _, _ => None
                  end
  end.

Lemma find_sub_expr_in : forall lhsl rhsl n tgt texpr, nth_error lhsl n = Some tgt -> nth_error rhsl n = Some texpr -> find_sub_expr' tgt lhsl rhsl = Some [:: texpr].
Proof.
  elim. 
  intros.
  apply nth_error_In in H.
  apply List.in_nil in H; done.
  intros hd tl H.
  elim. 
  intros.
  apply nth_error_In in H1.
  apply List.in_nil in H1; done.
  intros hd0 tl0 H0; clear H0.
  intros.
  simpl.
  induction n as [|n'].
  simpl in H0; simpl in H1.
  inversion H0; inversion H1; clear H0 H1.
  rewrite eq_refl //.
  assert ((hd == tgt) = false).
  admit.
  rewrite H2; clear H2 IHn'.
  assert (nth_error (hd :: tl) n'.+1 = nth_error tl n').
  (*apply nth_error_app1*)
  admit.
  assert (nth_error (hd0 :: tl0) n'.+1 = nth_error tl0 n').
  admit.
  rewrite H2 in H0; rewrite H3 in H1.
  move : H0 H1.
  apply H. 
Admitted.

Lemma find_sub_expr0_in : forall lhsl rhsl n, match nth_error lhsl n, nth_error rhsl n with
  | Some (ref1, true), Some (ref2, true) => find_sub_expr'0 ref2 lhsl rhsl = Some [:: (Eref (Eid ref1))]
  | Some (ref1, false), Some (ref2, false) => find_sub_expr'0 ref1 lhsl rhsl = Some [:: (Eref (Eid ref2))]
  | _, _ => True
  end.
Proof.
  elim.
  admit.
  intros llhd lltl IH.
  elim.
  admit.
  intros rlhd rltl H0 n; clear H0.
  induction n as [|n'].
  simpl.
  case : llhd => [ref1 b1].
  case : rlhd => [ref2 b2].
  rewrite eq_refl.
  case Hb1 : b1; try done.
  case Hb2 : b2; try done.
  rewrite eq_refl.
  case Hb2 : b2; try done.
  clear IHn'.
  specialize IH with (rhsl := rltl) (n := n').
  assert (nth_error (llhd :: lltl) n'.+1 = nth_error lltl n').
  admit.
  assert (nth_error (rlhd :: rltl) n'.+1 = nth_error rltl n').
  admit.
  rewrite H H0; clear H H0.
  case Hlltl : (nth_error lltl n') => [[ref1 b1]|]; rewrite Hlltl in IH; try done.
  case Hb1 : b1; rewrite Hb1 in IH; try done.
  - (* flip *)
    case Hrltl : (nth_error rltl n') => [[ref2 b2]|]; rewrite Hrltl in IH; try done.
    case Hb2 : b2; rewrite Hb2 in IH; try done.
    simpl. 
    case Hlhd : llhd => [hd b].
    case Hrhd : rlhd => [hd' b'].
    assert ((hd' == ref2) = false).
    admit. (* rhsl 应没有重复的元素，有第n个是ref2，从而hd'不是re2 *)
    assert ((hd == ref2) = false).
    admit. 
    rewrite H H0.
    assert (b' = b).
    admit.
    case Hb : b; try done.
    rewrite H1 Hb IH //.
    rewrite H1 Hb IH //.
  - (* nflip *)
    case Hrltl : (nth_error rltl n') => [[ref2 b2]|]; rewrite Hrltl in IH; try done.
    case Hb2 : b2; rewrite Hb2 in IH; try done.
    simpl. 
    case Hlhd : llhd => [hd b].
    case Hrhd : rlhd => [hd' b'].
    assert ((hd' == ref1) = false).
    admit. (* rhsl 应没有重复的元素，有第n个是ref2，从而hd'不是re2 *)
    assert ((hd == ref1) = false).
    admit. 
    rewrite H H0.
    assert (b' = b).
    admit.
    case Hb : b; try done.
    rewrite H1 Hb IH //.
    rewrite H1 Hb IH //.
Admitted.

Lemma find_sub_expr_notin : forall lhsl rhsl v, ~ v \in lhsl -> length lhsl = length rhsl -> find_sub_expr' v lhsl rhsl = Some nil.
Proof.
  elim.
  intros.
  simpl; simpl in H0.
  symmetry in H0.
  apply length_zero_iff_nil in H0; rewrite H0 //.
  intros hd tl IH.
  elim.
  intros.
  simpl in H0.
  discriminate.
  intros hd0  tl0 H0; clear H0.
  intros.
  simpl in H0; simpl.
  apply eq_add_S in H0.
  rewrite in_cons in H.
  case H1 : ((v == hd)); rewrite H1 in H. 
  rewrite orb_true_l in H.
  try done.
  rewrite orb_false_l in H.
  rewrite eq_sym H1.
  move : H H0.
  apply IH.
Qed.

Lemma find_sub_expr0_notin : forall lhsl rhsl v, ~ (v \in (List.split lhsl).1) -> ~ (v \in (List.split rhsl).1) -> length lhsl = length rhsl -> find_sub_expr'0 v lhsl rhsl = Some nil.
Proof.
  elim.
  intros.
  simpl; simpl in H1.
  symmetry in H1.
  apply length_zero_iff_nil in H1; rewrite H1 //.
  intros hd tl IH.
  elim.
  intros.
  simpl in H0.
  discriminate.
  intros hd0 tl0 H0; clear H0.
  intros.
  simpl in H1; simpl.
  apply eq_add_S in H1.
  case Hhd : hd => [hd1 b].
  case Hhd0 : hd0 => [hde b0].
  assert (b = b0).
  admit.
  case Hb : b; rewrite Hb in Hhd; rewrite -H2 Hb; rewrite -H2 Hb in Hhd0; clear H2 Hb b b0.
Admitted.

Lemma find_sub_expr0_notin' : forall lhsl rhsl, length lhsl = length rhsl -> (forall v, ~((v \in (List.split lhsl).1) && (v \in (List.split rhsl).1))) ->
  forall n, match nth_error lhsl n, nth_error rhsl n with
          | Some (ref1, true), Some (ref2, true) => find_sub_expr'0 ref1 lhsl rhsl = Some nil
          | Some (ref1, false), Some (ref2, false) => find_sub_expr'0 ref2 lhsl rhsl = Some nil
          | _, _ => True
          end.
Proof.
  elim.
  admit.
  intros [ref1 b1] ltl IH.
  elim.
  admit.
  intros [ref2 b2] rtl H0 Hlength Hin n; clear H0.
  induction n as [|n'].
  simpl. 
  clear IH.
  case Hb1 : b1; try done.
  - (* flip *)
    case Hb2 : b2; try done.
    specialize Hin with (v := ref2).
    assert ((ref1 == ref2) = false).
    admit. (* Hin *)
    rewrite eq_sym H.
    apply find_sub_expr0_notin.
    admit.
    admit.
    simpl in Hlength; apply eq_add_S in Hlength; done.
  - (* nflip *)
    case Hb2 : b2; try done.
    specialize Hin with (v := ref2).
    assert ((ref1 == ref2) = false).
    admit. (* Hin *)
    rewrite H.
    apply find_sub_expr0_notin.
    admit.
    admit.
    simpl in Hlength; apply eq_add_S in Hlength; done.
  clear IHn'.
  simpl in Hlength; apply eq_add_S in Hlength.
  apply IH with (rhsl := rtl) (n := n') in Hlength; clear IH.
  assert (nth_error ((ref1, b1) :: ltl) n'.+1 = nth_error ltl n').
  admit. 
  assert (nth_error ((ref2, b2) :: rtl) n'.+1 = nth_error rtl n').
  admit.
  rewrite H H0; clear H H0.
  case Hlv : (nth_error ltl n') => [[ref0 b]|]; rewrite Hlv in Hlength; try done.
  case Hrv : (nth_error rtl n') => [[ref3 b0]|]; rewrite Hrv in Hlength; try done.
Admitted.

Lemma add_expr_connect_notin : forall v lhsl rhsl var2exprs0 var2exprs, add_expr_connect lhsl rhsl var2exprs0 = Some var2exprs -> ~ (v \in lhsl) -> CEP.find v var2exprs0 = CEP.find v var2exprs.
Proof.
Admitted.

Lemma add_expr_non_passive_notin : forall v lhsl rhsl var2exprs0 var2exprs, add_expr_connect_non_passive lhsl rhsl var2exprs0 = Some var2exprs -> ~ (v \in (List.split lhsl).1) -> ~ (v \in (List.split rhsl).1) -> CEP.find v var2exprs0 = CEP.find v var2exprs.
Proof.
Admitted.

Lemma add_expr_non_passive_notin' : forall lhsl rhsl var2exprs0 var2exprs, add_expr_connect_non_passive lhsl rhsl var2exprs0 = Some var2exprs ->
  forall n, match nth_error lhsl n, nth_error rhsl n with
          | Some (ref1, true), Some (ref2, true) => CEP.find ref1 var2exprs0 = CEP.find ref1 var2exprs
          | Some (ref1, false), Some (ref2, false) => CEP.find ref2 var2exprs0 = CEP.find ref2 var2exprs
          | _, _ => True
          end.
Proof.
Admitted.

Lemma split_exprs_connect_correct : forall ss ref_tgt expr texpr t_expr rhsl newtm n el tgt, 
  Qin (Sfcnct (Eid ref_tgt) expr) ss -> type_of_hfexpr expr newtm = Some t_expr -> split_expr_connect expr t_expr = Some rhsl -> 
  nth_error rhsl n = Some texpr -> nth_error (list_gtypref ref_tgt t_expr) n = Some tgt -> find_sub_exprs tgt ss newtm = Some el -> texpr \in el
with split_expr_connect_correct : forall ref_tgt expr texpr t_expr rhsl newtm n el tgt, 
  type_of_hfexpr expr newtm = Some t_expr -> split_expr_connect expr t_expr = Some rhsl -> 
  nth_error rhsl n = Some texpr -> nth_error (list_gtypref ref_tgt t_expr) n = Some tgt -> find_sub_expr tgt (Sfcnct (Eid ref_tgt) expr) newtm = Some el -> texpr \in el.
Proof.
  (*admit.

  clear.
  intros.
  simpl in H3.
  case He : expr => [ct c| c e1 | u e1 | op e1 e2 | c e1 e2 | c e1 | ref0 ]; rewrite He in H3.
  (* 一般expr *)
  rewrite -He in H3.
  rewrite H in H3.
  assert (tgt.1 == ref_tgt.1).
  admit. (* 由H2 *)
  rewrite H4 in H3; clear H4.
  rewrite H0 in H3.
  specialize find_sub_expr_in with (n := n) (texpr := texpr); intro.
  rewrite H4 in H3; try done.
  inversion H3.
  rewrite mem_seq1 eq_refl //.
  - (* 一般expr *)
    rewrite -He in H3.
    rewrite H in H3.
    assert (tgt.1 == ref_tgt.1).
    admit. (* 由H2 *)
    rewrite H4 in H3; clear H4.
    rewrite H0 in H3.
    specialize find_sub_expr_in with (n := n) (texpr := texpr); intro.
    rewrite H4 in H3; try done.
    inversion H3.
    rewrite mem_seq1 eq_refl //.
  - (* 一般expr *)
    rewrite -He in H3.
    rewrite H in H3.
    assert (tgt.1 == ref_tgt.1).
    admit. (* 由H2 *)
    rewrite H4 in H3; clear H4.
    rewrite H0 in H3.
    specialize find_sub_expr_in with (n := n) (texpr := texpr); intro.
    rewrite H4 in H3; try done.
    inversion H3.
    rewrite mem_seq1 eq_refl //.
  - (* 一般expr *)
    rewrite -He in H3.
    rewrite H in H3.
    assert (tgt.1 == ref_tgt.1).
    admit. (* 由H2 *)
    rewrite H4 in H3; clear H4.
    rewrite H0 in H3.
    specialize find_sub_expr_in with (n := n) (texpr := texpr); intro.
    rewrite H4 in H3; try done.
    inversion H3.
    rewrite mem_seq1 eq_refl //.
  - (* 一般expr *)
    rewrite -He in H3.
    rewrite H in H3.
    assert (tgt.1 == ref_tgt.1).
    admit. (* 由H2 *)
    rewrite H4 in H3; clear H4.
    rewrite H0 in H3.
    specialize find_sub_expr_in with (n := n) (texpr := texpr); intro.
    rewrite H4 in H3; try done.
    inversion H3.
    rewrite mem_seq1 eq_refl //.
  - (* 一般expr *)
    rewrite -He in H3.
    rewrite H in H3.
    assert (tgt.1 == ref_tgt.1).
    admit. (* 由H2 *)
    rewrite H4 in H3; clear H4.
    rewrite H0 in H3.
    specialize find_sub_expr_in with (n := n) (texpr := texpr); intro.
    rewrite H4 in H3; try done.
    inversion H3.
    rewrite mem_seq1 eq_refl //.
  - (* ref <= ref *)
    case Href : ref0 => [ref_src|||]; rewrite Href in H3.
    - (* ref = Eid *)
      rewrite Href in He; rewrite He in H. 
      simpl in H; rewrite H in H3.
      case Htgt : (type_ref ref_tgt newtm) => [t_tgt|]; rewrite Htgt in H3; try discriminate.
      clear He Href ref0.
      assert (tgt.1 == ref_tgt.1).
      admit. (* 由H2 *)
      rewrite H4 in H3; clear H4.
      admit.
    - (* 一般expr *)
      rewrite Href in He; rewrite -He in H3.
      rewrite H in H3.
      assert (tgt.1 == ref_tgt.1).
      admit. (* 由H2 *)
      rewrite H4 in H3; clear H4.
      rewrite H0 in H3.
      specialize find_sub_expr_in with (n := n) (texpr := texpr); intro.
      rewrite H4 in H3; try done.
      inversion H3.
      rewrite mem_seq1 eq_refl //.
    - (* 一般expr *)
      rewrite Href in He; rewrite -He in H3.
      rewrite H in H3.
      assert (tgt.1 == ref_tgt.1).
      admit. (* 由H2 *)
      rewrite H4 in H3; clear H4.
      rewrite H0 in H3.
      specialize find_sub_expr_in with (n := n) (texpr := texpr); intro.
      rewrite H4 in H3; try done.
      inversion H3.
      rewrite mem_seq1 eq_refl //.
    - (* 一般expr *)
      rewrite Href in He; rewrite -He in H3.
      rewrite H in H3.
      assert (tgt.1 == ref_tgt.1).
      admit. (* 由H2 *)
      rewrite H4 in H3; clear H4.
      rewrite H0 in H3.
      specialize find_sub_expr_in with (n := n) (texpr := texpr); intro.
      rewrite H4 in H3; try done.
      inversion H3.
      rewrite mem_seq1 eq_refl //.*)
Admitted.

Lemma add_expr_connect_findn : forall vl rstl (var2exprs0 : CEP.t (seq HiFP.hfexpr)), 
  forall n, length vl = length rstl -> match nth_error vl n, nth_error rstl n, add_expr_connect vl rstl var2exprs0 with
  | Some v, Some e, Some var2exprs => match CEP.find v var2exprs0 with
                                    | Some el0 => CEP.find v var2exprs = Some (e :: el0)
                                    | None => CEP.find v var2exprs = Some [:: e]
                                    end
  | None, None, Some var2exprs => True
  | _, _, _ => False
  end.
Proof.
  elim.
  intros.
  simpl in H.
  symmetry in H.
  apply length_zero_iff_nil in H; rewrite H.
  (*rewrite nth_error_None.*)
  admit.

  intros vhd vtl IH.
  elim.
  intros.
  simpl in H; discriminate.
  intros rhd rtl H0 var2exprs0 n Hlength; clear H0.
  induction n as [|n'].
  simpl. 
  clear IH.
  simpl in Hlength; apply eq_add_S in Hlength.
  case Hfind : (CEP.find vhd var2exprs0) => [ls|].
  - (* 之前被连接过 *)
    assert (exists var2exprs, add_expr_connect vtl rtl (CEP.add vhd (rhd :: ls) var2exprs0) = Some var2exprs).
    admit. (* 若vl 与 rstl长度相同，则存在结果 *)
    destruct H as [var2exprs H]; rewrite H.
    apply add_expr_connect_notin with (v := vhd) in H.
    rewrite -H CEP.Lemmas.find_add_eq //.
    apply PVS.SE.eq_refl.
    admit.
  - (* 第一次被连接 *)
    assert (exists var2exprs, add_expr_connect vtl rtl (CEP.add vhd [::rhd] var2exprs0) = Some var2exprs).
    admit. (* 若vl 与 rstl长度相同，则存在结果 *)
    destruct H as [var2exprs H]; rewrite H.
    apply add_expr_connect_notin with (v := vhd) in H.
    rewrite -H CEP.Lemmas.find_add_eq //.
    apply PVS.SE.eq_refl.
    admit.

  clear IHn'.
  simpl in Hlength; apply eq_add_S in Hlength.
  specialize IH with (rstl := rtl) (n := n').
  assert (nth_error (vhd :: vtl) n'.+1 = nth_error vtl n').
  admit.
  assert (nth_error (rhd :: rtl) n'.+1 = nth_error rtl n').
  admit.
  rewrite H H0; clear H H0.
  case Hvtl : (nth_error vtl n') => [v|]; rewrite Hvtl in IH.
  simpl. 
  case Hhd : (CEP.find vhd var2exprs0) => [ls|].
  - (* hd之前被连接过 *)
    specialize IH with (var2exprs0 := CEP.add vhd (rhd :: ls) var2exprs0).
    case Hrtl : (nth_error rtl n') => [e|]; rewrite Hrtl in IH; try done.
    case Hadd : (add_expr_connect vtl rtl (CEP.add vhd (rhd :: ls) var2exprs0)) => [var2exprs|]; rewrite Hadd in IH; try done.
    rewrite CEP.Lemmas.find_add_neq in IH.
    case Hfind : (CEP.find v var2exprs0) => [el0|]; rewrite Hfind in IH; apply IH in Hlength; try done.
    admit.
  - (* hd第一次被连接 *)
    specialize IH with (var2exprs0 := CEP.add vhd [::rhd] var2exprs0).
    case Hrtl : (nth_error rtl n') => [e|]; rewrite Hrtl in IH; try done.
    case Hadd : (add_expr_connect vtl rtl (CEP.add vhd [::rhd] var2exprs0)) => [var2exprs|]; rewrite Hadd in IH; try done.
    rewrite CEP.Lemmas.find_add_neq in IH.
    case Hfind : (CEP.find v var2exprs0) => [el0|]; rewrite Hfind in IH; apply IH in Hlength; try done.
    admit.
  admit.
Admitted.

Lemma add_expr_non_passive_findn : forall lhsl rhsl (var2exprs0 : CEP.t (seq HiFP.hfexpr)), 
  forall n, length lhsl = length rhsl -> match nth_error lhsl n, nth_error rhsl n, add_expr_connect_non_passive lhsl rhsl var2exprs0 with
  | Some (ref1, true), Some (ref2, true), Some var2exprs => 
                                    match CEP.find ref2 var2exprs0 with
                                    | Some el0 => CEP.find ref2 var2exprs = Some ((Eref (Eid ref1)) :: el0)
                                    | None => CEP.find ref2 var2exprs = Some [:: (Eref (Eid ref1))]
                                    end
  | Some (ref1, false), Some (ref2, false), Some var2exprs => 
                                    match CEP.find ref1 var2exprs0 with
                                    | Some el0 => CEP.find ref1 var2exprs = Some ((Eref (Eid ref2)) :: el0)
                                    | None => CEP.find ref1 var2exprs = Some [:: (Eref (Eid ref2))]
                                    end
  | None, None, Some var2exprs => True
  | _, _, _ => False
  end.
Proof.
  elim.
  intros.
  simpl in H.
  symmetry in H.
  apply length_zero_iff_nil in H; rewrite H.
  (*rewrite nth_error_None.*)
  admit.

  intros vhd vtl IH.
  elim.
  intros.
  simpl in H; discriminate.
  intros rhd rtl H0 var2exprs0 n Hlength; clear H0.
  induction n as [|n'].
  simpl. 
  clear IH.
  simpl in Hlength; apply eq_add_S in Hlength.
  case Hvhd : vhd => [ref1 b1].
  case Hrhd : rhd => [ref2 b2].
  assert (b2 = b1).
  admit.
  case Hb1 : b1; rewrite Hb1 in Hvhd.
  rewrite H Hb1; rewrite H Hb1 in Hrhd; clear Hb1 b1 H b2.
  (* flip *)
  case Hfind : (CEP.find ref2 var2exprs0) => [ls|].
  - (* 之前被连接过 *)
    assert (exists var2exprs, add_expr_connect_non_passive vtl rtl (CEP.add ref2 ((Eref (Eid ref1)) :: ls) var2exprs0) = Some var2exprs).
    admit. (* 若vl 与 rstl长度相同，则存在结果 *)
    destruct H as [var2exprs H]; rewrite H.
    apply add_expr_non_passive_notin with (v := ref2) in H.
    rewrite -H CEP.Lemmas.find_add_eq //.
    apply PVS.SE.eq_refl.
    admit.
    admit.
  - (* 第一次被连接 *)
    assert (exists var2exprs, add_expr_connect_non_passive vtl rtl (CEP.add ref2 [:: Eref (Eid ref1)] var2exprs0) = Some var2exprs).
    admit. (* 若vl 与 rstl长度相同，则存在结果 *)
    destruct H as [var2exprs H]; rewrite H.
    apply add_expr_non_passive_notin with (v := ref2) in H.
    rewrite -H CEP.Lemmas.find_add_eq //.
    apply PVS.SE.eq_refl.
    admit.
    admit.
  rewrite H Hb1; rewrite H Hb1 in Hrhd; clear Hb1 b1 H b2.
  (* nflip *)
  case Hfind : (CEP.find ref1 var2exprs0) => [ls|].
  - (* 之前被连接过 *)
    assert (exists var2exprs, add_expr_connect_non_passive vtl rtl (CEP.add ref1 ((Eref (Eid ref2)) :: ls) var2exprs0) = Some var2exprs).
    admit. (* 若vl 与 rstl长度相同，则存在结果 *)
    destruct H as [var2exprs H]; rewrite H.
    apply add_expr_non_passive_notin with (v := ref1) in H.
    rewrite -H CEP.Lemmas.find_add_eq //.
    apply PVS.SE.eq_refl.
    admit.
    admit.
  - (* 第一次被连接 *)
    assert (exists var2exprs, add_expr_connect_non_passive vtl rtl (CEP.add ref1 [:: Eref (Eid ref2)] var2exprs0) = Some var2exprs).
    admit. (* 若vl 与 rstl长度相同，则存在结果 *)
    destruct H as [var2exprs H]; rewrite H.
    apply add_expr_non_passive_notin with (v := ref1) in H.
    rewrite -H CEP.Lemmas.find_add_eq //.
    apply PVS.SE.eq_refl.
    admit.
    admit.

  clear IHn'.
  simpl in Hlength; apply eq_add_S in Hlength.
  specialize IH with (rhsl := rtl) (n := n').
  assert (nth_error (vhd :: vtl) n'.+1 = nth_error vtl n').
  admit.
  assert (nth_error (rhd :: rtl) n'.+1 = nth_error rtl n').
  admit.
  rewrite H H0; clear H H0.
  case Hvtl : (nth_error vtl n') => [[ref1 b1]|]; rewrite Hvtl in IH.
  case Hb1 : b1; rewrite Hb1 in IH Hvtl.
  - (* flip *)
    case Hrtl : (nth_error rtl n') => [[ref2 b2]|]; rewrite Hrtl in IH; try done.
    simpl. 
    assert (b2 = b1).
    admit.
    rewrite H Hb1; rewrite H Hb1 in IH; rewrite H Hb1 in Hrtl; clear H Hb1 b1 b2.
    case Hvhd : vhd => [ref0 b].
    case Hrhd : rhd => [ref3 b0].
    assert (b = b0).
    admit.
    (*case Hb : b; rewrite Hb in Hvhd; rewrite -H Hb; rewrite -H Hb in Hrhd; clear H Hb b b0.
    (* flip *)
    case Hhd : (CEP.find ref3 var2exprs0) => [ls|].
    - (* hd之前被连接过 *)
      apply IH with (var2exprs0 := CEP.add ref3 (Eref (Eid ref0) :: ls) var2exprs0) in Hlength; clear IH.
      case Hadd : (add_expr_connect_non_passive vtl rtl (CEP.add ref3 ((Eref (Eid ref0)) :: ls) var2exprs0)) => [var2exprs|]; rewrite Hadd in Hlength; try done.
      rewrite CEP.Lemmas.find_add_neq in Hlength.
      case Hfind : (CEP.find ref2 var2exprs0) => [el0|]; rewrite Hfind in Hlength; try done.
      admit.
    - (* hd第一次被连接 *)
      apply IH with (var2exprs0 := CEP.add ref3 [:: Eref (Eid ref0)] var2exprs0) in Hlength; clear IH.
      case Hadd : (add_expr_connect_non_passive vtl rtl (CEP.add ref3 [:: Eref (Eid ref0)] var2exprs0)) => [var2exprs|]; rewrite Hadd in Hlength; try done.
      rewrite CEP.Lemmas.find_add_neq in Hlength.
      case Hfind : (CEP.find ref2 var2exprs0) => [el0|]; rewrite Hfind in Hlength; try done.
      admit.
    (* nflip *)
    case Hhd : (CEP.find ref0 var2exprs0) => [ls|].
    - (* hd之前被连接过 *)
      apply IH with (var2exprs0 := CEP.add ref0 (Eref (Eid ref3) :: ls) var2exprs0) in Hlength; clear IH.
      case Hadd : (add_expr_connect_non_passive vtl rtl (CEP.add ref0 ((Eref (Eid ref3)) :: ls) var2exprs0)) => [var2exprs|]; rewrite Hadd in Hlength; try done.
      rewrite CEP.Lemmas.find_add_neq in Hlength.
      case Hfind : (CEP.find ref2 var2exprs0) => [el0|]; rewrite Hfind in Hlength; try done.
      admit.
    - (* hd第一次被连接 *)
      apply IH with (var2exprs0 := CEP.add ref0 [:: Eref (Eid ref3)] var2exprs0) in Hlength; clear IH.
      case Hadd : (add_expr_connect_non_passive vtl rtl (CEP.add ref0 [:: Eref (Eid ref3)] var2exprs0)) => [var2exprs|]; rewrite Hadd in Hlength; try done.
      rewrite CEP.Lemmas.find_add_neq in Hlength.
      case Hfind : (CEP.find ref2 var2exprs0) => [el0|]; rewrite Hfind in Hlength; try done.
      admit.
    apply IH in Hlength; try done.
  - (* nflip *)
    case Hrtl : (nth_error rtl n') => [[ref2 b2]|]; rewrite Hrtl in IH; try done.
    simpl. 
    assert (b2 = b1).
    admit.
    rewrite H Hb1; rewrite H Hb1 in IH; rewrite H Hb1 in Hrtl; clear H Hb1 b1 b2.
    case Hvhd : vhd => [ref0 b].
    case Hrhd : rhd => [ref3 b0].
    assert (b = b0).
    admit.
    case Hb : b; rewrite Hb in Hvhd; rewrite -H Hb; rewrite -H Hb in Hrhd; clear H Hb b b0.
    (* flip *)
    case Hhd : (CEP.find ref3 var2exprs0) => [ls|].
    - (* hd之前被连接过 *)
      apply IH with (var2exprs0 := CEP.add ref3 (Eref (Eid ref0) :: ls) var2exprs0) in Hlength; clear IH.
      case Hadd : (add_expr_connect_non_passive vtl rtl (CEP.add ref3 ((Eref (Eid ref0)) :: ls) var2exprs0)) => [var2exprs|]; rewrite Hadd in Hlength; try done.
      rewrite CEP.Lemmas.find_add_neq in Hlength.
      case Hfind : (CEP.find ref1 var2exprs0) => [el0|]; rewrite Hfind in Hlength; try done.
      admit.
    - (* hd第一次被连接 *)
      apply IH with (var2exprs0 := CEP.add ref3 [:: Eref (Eid ref0)] var2exprs0) in Hlength; clear IH.
      case Hadd : (add_expr_connect_non_passive vtl rtl (CEP.add ref3 [:: Eref (Eid ref0)] var2exprs0)) => [var2exprs|]; rewrite Hadd in Hlength; try done.
      rewrite CEP.Lemmas.find_add_neq in Hlength.
      case Hfind : (CEP.find ref1 var2exprs0) => [el0|]; rewrite Hfind in Hlength; try done.
      admit.
    (* nflip *)
    case Hhd : (CEP.find ref0 var2exprs0) => [ls|].
    - (* hd之前被连接过 *)
      apply IH with (var2exprs0 := CEP.add ref0 (Eref (Eid ref3) :: ls) var2exprs0) in Hlength; clear IH.
      case Hadd : (add_expr_connect_non_passive vtl rtl (CEP.add ref0 ((Eref (Eid ref3)) :: ls) var2exprs0)) => [var2exprs|]; rewrite Hadd in Hlength; try done.
      rewrite CEP.Lemmas.find_add_neq in Hlength.
      case Hfind : (CEP.find ref1 var2exprs0) => [el0|]; rewrite Hfind in Hlength; try done.
      admit.
    - (* hd第一次被连接 *)
      apply IH with (var2exprs0 := CEP.add ref0 [:: Eref (Eid ref3)] var2exprs0) in Hlength; clear IH.
      case Hadd : (add_expr_connect_non_passive vtl rtl (CEP.add ref0 [:: Eref (Eid ref3)] var2exprs0)) => [var2exprs|]; rewrite Hadd in Hlength; try done.
      rewrite CEP.Lemmas.find_add_neq in Hlength.
      case Hfind : (CEP.find ref1 var2exprs0) => [el0|]; rewrite Hfind in Hlength; try done.
      admit.
    apply IH in Hlength; try done.
  admit.*)
Admitted.

Lemma cons_cat_eq : forall [T : Type] (hd : T) (tl : seq T), hd :: tl = [:: hd] ++ tl.
Proof.
  simpl; done.
Qed.

Lemma find_sub_expr_eq : forall s tmap0 tmap var2exprs0 var2exprs, stmt_tmap (tmap0, var2exprs0) s = Some (tmap, var2exprs) ->
  forall (v : ProdVarOrder.t), match CEP.find v var2exprs0, find_sub_expr v s tmap, CEP.find v var2exprs with
  | Some el0, Some el', Some el => TopoSort.subset el (el' ++ el0) /\ TopoSort.subset (el' ++ el0) el
  | None, Some el', Some el => TopoSort.subset el el' /\ TopoSort.subset el' el
  | None, Some nil, None => True
  | _,_, _ => False
  end
with find_sub_exprs_eq : forall ss tmap0 tmap var2exprs0 var2exprs, stmts_tmap (tmap0, var2exprs0) ss = Some (tmap, var2exprs) ->
  forall (v : ProdVarOrder.t), match CEP.find v var2exprs0, find_sub_exprs v ss tmap, CEP.find v var2exprs with
  | Some el0, Some el', Some el => TopoSort.subset el (el' ++ el0) /\ TopoSort.subset (el' ++ el0) el
  | None, Some el', Some el => TopoSort.subset el el' /\ TopoSort.subset el' el
  | None, Some nil, None => True
  | _,_, _ => False
  end.
  Proof.
  clear find_sub_expr_eq.
  intros.
  case Hs : s => [|r t|r reg|||r e|r e|r|c s1 s2]; rewrite Hs in H; simpl in H; simpl.
  - (* skip *)
    inversion H. 
    case Hfind : (CEP.find v var2exprs) => [el0|]; try done.
    split; apply TopoSort.subset_refl.
  - (* wire *)
    case Hr : (CEP.find r tmap0); rewrite Hr in H; try discriminate.
    inversion H.
    case Hfind : (CEP.find v var2exprs) => [el0|]; try done.
    split; apply TopoSort.subset_refl.
  - (* reg *)
    clear find_sub_exprs_eq.
    case Hr : (CEP.find r tmap0); rewrite Hr in H; try discriminate.
    case Hrst : (reset reg) => [|rst_sig rst_val]; rewrite Hrst in H.
    inversion H.
    case Hfind : (CEP.find v var2exprs) => [el0|]; try done.
    split; apply TopoSort.subset_refl.
    case Hsplit : (split_expr_connect rst_val (type reg)) => [rstl|]; rewrite Hsplit in H; try discriminate.
    case Hsplit' : (split_expr r (type reg)) => [vl|]; rewrite Hsplit' in H; try discriminate.
    assert (Hlength : length vl = length rstl).
    admit.
    case Hadd : (add_expr_connect vl rstl var2exprs0) => [nt_v|]; rewrite Hadd in H; try discriminate.
    inversion H; clear H. 
    (*rewrite H2 in Hadd; clear H2 nt_v.
    case Hfind0 : (CEP.find v var2exprs0) => [el0|].
    - (* 有其他连接 *)
      clear H1 tmap Hr tmap0.
      case Hin : (v \in vl).
      specialize add_expr_connect_findn with (vl := vl) (rstl := rstl) (var2exprs0 := var2exprs0); intro.
      assert (exists n, nth_error vl n = Some v).
      admit. (* 由Hin *)
      destruct H0 as [n H0]; clear Hin.
      specialize H with (n := n); rewrite H0 in H.
      assert (exists e, nth_error rstl n = Some e).
      admit. (* 由vl rstl长度相等 *)
      destruct H1 as [e H1]; rewrite H1 Hadd Hfind0 in H.
      rewrite H.
      apply find_sub_expr_in with (tgt := v) (lhsl := vl) (rhsl := rstl) (texpr := e) (n := n) in H0; try done.
      rewrite H0.
      assert ((e :: el0) = ([:: e] ++ el0)).
      simpl; done.
      rewrite H2.
      split; rewrite TopoSort.subset_refl; done.
      done.
      apply add_expr_connect_notin with (v := v) in Hadd; try done.
      rewrite find_sub_expr_notin. 
      rewrite -Hadd Hfind0.
      simpl; split; apply TopoSort.subset_refl.
      1,3 : rewrite Hin //.
      done.
    - (* 第一次连接 *)
      clear H1 tmap Hr tmap0.
      case Hin : (v \in vl).
      specialize add_expr_connect_findn with (vl := vl) (rstl := rstl) (var2exprs0 := var2exprs0); intro.
      assert (exists n, nth_error vl n = Some v).
      admit. (* 由Hin *)
      destruct H0 as [n H0]; clear Hin.
      specialize H with (n := n); rewrite H0 in H.
      assert (exists e, nth_error rstl n = Some e).
      admit. (* 由vl rstl长度相等 *)
      destruct H1 as [e H1]; rewrite H1 Hadd Hfind0 in H.
      rewrite H.
      apply find_sub_expr_in with (tgt := v) (lhsl := vl) (rhsl := rstl) (texpr := e) (n := n) in H0; try done.
      rewrite H0; split; apply TopoSort.subset_refl.
      done.
      apply add_expr_connect_notin with (v := v) in Hadd; try done.
      rewrite find_sub_expr_notin. 
      rewrite -Hadd Hfind0 //.
      1,3 : rewrite Hin //.
      done.
  discriminate.
  discriminate.
  - (* node *)
    clear find_sub_exprs_eq.
    case Hr : (CEP.find r tmap0); rewrite Hr in H; try discriminate.
    case Hte : (type_of_hfexpr e tmap0) => [te|]; rewrite Hte in H; try discriminate.
    case Hsplit : (split_expr_connect e te) => [rstl|]; rewrite Hsplit in H; try discriminate.
    case Hsplit' : (split_expr r te) => [vl|]; rewrite Hsplit' in H; try discriminate.
    assert (Hlength : length vl = length rstl).
    admit.
    case Hadd : (add_expr_connect vl rstl var2exprs0) => [nt_v|]; rewrite Hadd in H; try discriminate.
    inversion H; clear H. 
    rewrite H2 in Hadd; clear H2 nt_v.
    assert (type_of_hfexpr e (CEP.add r te tmap0) = type_of_hfexpr e tmap0).
    admit.
    rewrite H Hte Hsplit Hsplit'; clear H.
    case Hfind0 : (CEP.find v var2exprs0) => [el0|].
    - (* 有其他连接 *)
      clear H1 tmap Hr Hte.
      case Hin : (v \in vl).
      specialize add_expr_connect_findn with (vl := vl) (rstl := rstl) (var2exprs0 := var2exprs0); intro.
      assert (exists n, nth_error vl n = Some v).
      admit. (* 由Hin *)
      destruct H0 as [n H0]; clear Hin.
      specialize H with (n := n); rewrite H0 in H.
      assert (exists e, nth_error rstl n = Some e).
      admit. (* 由vl rstl长度相等 *)
      destruct H1 as [en H1]; rewrite H1 Hadd Hfind0 in H.
      rewrite H.
      apply find_sub_expr_in with (tgt := v) (lhsl := vl) (rhsl := rstl) (texpr := en) (n := n) in H0; try done.
      rewrite H0.
      assert ((en :: el0) = ([:: en] ++ el0)).
      simpl; done.
      rewrite H2.
      split; rewrite TopoSort.subset_refl; done.
      done.
      apply add_expr_connect_notin with (v := v) in Hadd; try done.
      rewrite find_sub_expr_notin. 
      rewrite -Hadd Hfind0.
      simpl; split; apply TopoSort.subset_refl.
      1,3 : rewrite Hin //.
      done.
    - (* 第一次连接 *)
      clear H1 tmap Hr Hte.
      case Hin : (v \in vl).
      specialize add_expr_connect_findn with (vl := vl) (rstl := rstl) (var2exprs0 := var2exprs0); intro.
      assert (exists n, nth_error vl n = Some v).
      admit. (* 由Hin *)
      destruct H0 as [n H0]; clear Hin.
      specialize H with (n := n); rewrite H0 in H.
      assert (exists en, nth_error rstl n = Some en).
      admit. (* 由vl rstl长度相等 *)
      destruct H1 as [en H1]; rewrite H1 Hadd Hfind0 in H.
      rewrite H.
      apply find_sub_expr_in with (tgt := v) (lhsl := vl) (rhsl := rstl) (texpr := en) (n := n) in H0; try done.
      rewrite H0; split; apply TopoSort.subset_refl.
      done.
      apply add_expr_connect_notin with (v := v) in Hadd; try done.
      rewrite find_sub_expr_notin. 
      rewrite -Hadd Hfind0 //.
      1,3 : rewrite Hin //.
      done.
  - (* fcnct *)
    clear find_sub_exprs_eq.
    case He : e =>[t c| c e1 | u e1 | op e1 e2 | c e1 e2 | c e1 | r2 ]; rewrite He in H; try done.
    - (* 一般connection *)
    rewrite -He; rewrite -He in H.
    case Hr : r => [ref_tgt|||]; rewrite Hr in H Hs; try discriminate; clear Hr r.
    case Hbase : (type_ref ref_tgt tmap0) => [t_tgt|]; rewrite Hbase in H; try discriminate.
    case Hte : (type_of_hfexpr e tmap0) => [t_src|]; rewrite Hte in H; try discriminate.
    case Hsplit : (split_expr_connect e t_src) => [rstl|]; rewrite Hsplit in H; try discriminate.
    case Hsplit' : (split_expr ref_tgt t_tgt) => [vl|]; rewrite Hsplit' in H; try discriminate.
    assert (Hlength : length vl = length rstl).
    admit.
    case Hadd : (add_expr_connect vl rstl var2exprs0) => [nt_v|]; rewrite Hadd in H; try discriminate.
    inversion H; clear H.
    rewrite H2 in Hadd; rewrite H1 in Hbase Hte; clear H2 nt_v H1 tmap0.
    rewrite Hbase Hte Hsplit Hsplit'.
    case Hfind0 : (CEP.find v var2exprs0) => [el0|].
    - (* 有其他连接 *)
      case Hin : (v \in vl).
      specialize add_expr_connect_findn with (vl := vl) (rstl := rstl) (var2exprs0 := var2exprs0); intro.
      assert (exists n, nth_error vl n = Some v).
      admit. (* 由Hin *)
      destruct H0 as [n H0]; clear Hin.
      specialize H with (n := n); rewrite H0 in H.
      assert (exists e, nth_error rstl n = Some e).
      admit. (* 由vl rstl长度相等 *)
      destruct H1 as [en H1]; rewrite H1 Hadd Hfind0 in H.
      rewrite H.
      apply find_sub_expr_in with (tgt := v) (lhsl := vl) (rhsl := rstl) (texpr := en) (n := n) in H0; try done.
      rewrite H0.
      assert ((en :: el0) = ([:: en] ++ el0)).
      simpl; done.
      rewrite H2.
      split; rewrite TopoSort.subset_refl; done.
      done.
      apply add_expr_connect_notin with (v := v) in Hadd; try done.
      rewrite find_sub_expr_notin. 
      rewrite -Hadd Hfind0.
      simpl; split; apply TopoSort.subset_refl.
      1,3 : rewrite Hin //.
      done.
    - (* 第一次连接 *)
      case Hin : (v \in vl).
      specialize add_expr_connect_findn with (vl := vl) (rstl := rstl) (var2exprs0 := var2exprs0); intro.
      assert (exists n, nth_error vl n = Some v).
      admit. (* 由Hin *)
      destruct H0 as [n H0]; clear Hin.
      specialize H with (n := n); rewrite H0 in H.
      assert (exists en, nth_error rstl n = Some en).
      admit. (* 由vl rstl长度相等 *)
      destruct H1 as [en H1]; rewrite H1 Hadd Hfind0 in H.
      rewrite H.
      apply find_sub_expr_in with (tgt := v) (lhsl := vl) (rhsl := rstl) (texpr := en) (n := n) in H0; try done.
      rewrite H0; split; apply TopoSort.subset_refl.
      done.
      apply add_expr_connect_notin with (v := v) in Hadd; try done.
      rewrite find_sub_expr_notin. 
      rewrite -Hadd Hfind0 //.
      1,3 : rewrite Hin //.
      done.
    (* 同上的connection case *)
    admit.
    admit.
    admit.
    admit.
    admit.
    (* Eref connection *)
    case Hr : r => [ref_tgt|||]; rewrite Hr in H Hs; try discriminate; clear Hr r.
    case Hr2 : r2 => [ref_src|||]; rewrite Hr2 in H He; try discriminate; rewrite He in Hs; clear Hr2 r2 He e.
    case Hbase : (type_ref ref_tgt tmap0) => [t_tgt|]; rewrite Hbase in H; try discriminate.
    case Hbase2 : (type_ref ref_src tmap0) => [t_src|]; rewrite Hbase2 in H; try discriminate.
    case Hsplit : (split_expr_non_passive ref_tgt t_tgt false) => [lhsl|]; rewrite Hsplit in H; try discriminate.
    case Hsplit2 : (split_expr_non_passive ref_src t_src false) => [rhsl|]; rewrite Hsplit2 in H; try discriminate.
    assert (Hlength : length lhsl = length rhsl).
    admit.
    case Hadd : (add_expr_connect_non_passive lhsl rhsl var2exprs0) => [newv2e|]; rewrite Hadd in H; try discriminate.
    inversion H; clear H.
    rewrite H2 in Hadd; clear H2 newv2e.
    rewrite -H1 Hbase Hbase2 Hsplit2 Hsplit.
    rewrite H1 in Hbase Hbase2; clear H1 tmap0.
    case Hfind0 : (CEP.find v var2exprs0) => [el0|].
    - (* 有其他连接 *)
      - (* Nflip *)
      case Hinl : (v \in (List.split lhsl).1).
      specialize add_expr_non_passive_findn with (lhsl := lhsl) (rhsl := rhsl) (var2exprs0 := var2exprs0); intro.
      assert (exists n, nth_error (List.split lhsl).1 n = Some v).
      admit. (* 由Hin *)
      destruct H0 as [n H0]; clear Hinl.
      specialize H with (n := n).
      case Hlhsl : (nth_error lhsl n) => [[ref1 b1]|]; rewrite Hlhsl in H; try done.
      assert (v = ref1).
      move : H0 Hlhsl.
      admit.
      case Hb1 : b1; rewrite Hb1 in H Hlhsl; clear Hb1 b1.
      case Hrhsl : (nth_error rhsl n) => [[ref2 b2]|]; rewrite Hrhsl in H; try done.
      case Hb2 : b2; rewrite Hb2 in H Hrhsl; try done; clear Hb2 b2.
      apply add_expr_non_passive_notin' with (n := n) in Hadd; clear H.
      rewrite Hlhsl Hrhsl in Hadd.
      rewrite -H1 in Hadd; rewrite -Hadd Hfind0.
      specialize find_sub_expr0_notin' with (lhsl := lhsl) (rhsl := rhsl) (n := n); intro.
      rewrite Hlhsl Hrhsl in H; rewrite H1 H.
      simpl; split; apply TopoSort.subset_refl.
      done.
      admit.
      case Hrhsl : (nth_error rhsl n) => [[ref2 b2]|]; rewrite Hrhsl in H; try done.
      case Hb2 : b2; rewrite Hb2 in H Hrhsl; try done; clear Hb2 b2.
      rewrite Hadd -H1 Hfind0 in H; rewrite H.
      specialize find_sub_expr0_in with (lhsl := lhsl) (rhsl := rhsl) (n := n); intro.
      rewrite Hlhsl Hrhsl in H2; rewrite H1 H2.
      rewrite cons_cat_eq; split; apply TopoSort.subset_refl.
      done.
      admit. (* H0与Hlhsl相悖 *)
      - (* Flipped *)
      case Hinr : (v \in (List.split rhsl).1).
      specialize add_expr_non_passive_findn with (lhsl := lhsl) (rhsl := rhsl) (var2exprs0 := var2exprs0); intro.
      assert (exists n, nth_error (List.split rhsl).1 n = Some v).
      admit. (* 由Hin *)
      destruct H0 as [n H0]; clear Hinl.
      specialize H with (n := n).
      case Hlhsl : (nth_error lhsl n) => [[ref1 b1]|]; rewrite Hlhsl in H; try done.
      case Hb1 : b1; rewrite Hb1 in H Hlhsl; clear Hb1 b1.
      case Hrhsl : (nth_error rhsl n) => [[ref2 b2]|]; rewrite Hrhsl in H; try done.
      case Hb2 : b2; rewrite Hb2 in H Hrhsl; try done; clear Hb2 b2.
      assert (v = ref2).
      move : H0 Hrhsl.
      admit.
      rewrite H1 in H0 Hfind0 Hinr; rewrite H1; clear H1 v.
      rewrite Hadd Hfind0 in H; rewrite H; clear H.
      apply add_expr_non_passive_notin' with (n := n) in Hadd.
      rewrite Hlhsl Hrhsl in Hadd.
      specialize find_sub_expr0_in with (lhsl := lhsl) (rhsl := rhsl) (n := n); intro.
      rewrite Hlhsl Hrhsl in H; rewrite H.
      rewrite cons_cat_eq; split; apply TopoSort.subset_refl.
      done.
      case Hrhsl : (nth_error rhsl n) => [[ref2 b2]|]; rewrite Hrhsl in H; try done.
      case Hb2 : b2; rewrite Hb2 in H Hrhsl; try done; clear Hb2 b2.
      clear H.
      assert (v = ref2).
      move : H0 Hrhsl.
      admit.
      specialize find_sub_expr0_notin' with (lhsl := lhsl) (rhsl := rhsl) (n := n); intro.
      rewrite Hlhsl Hrhsl in H1; rewrite H H1.
      apply add_expr_non_passive_notin' with (n := n) in Hadd.
      rewrite Hlhsl Hrhsl in Hadd; rewrite -Hadd -H Hfind0.
      simpl; split; apply TopoSort.subset_refl.
      done.
      admit.
      admit. (* H0与Hlhsl相悖 *)
      - (* 啥也不是 *)
      rewrite find_sub_expr0_notin.
      apply add_expr_non_passive_notin with (v := v) in Hadd.
      rewrite -Hadd Hfind0.
      simpl; split; apply TopoSort.subset_refl.
      1,3 : rewrite Hinl //.
      1,2 : rewrite Hinr //.
      done.
    - (* 第一次连接 *)
      - (* Nflip *)
      case Hinl : (v \in (List.split lhsl).1).
      specialize add_expr_non_passive_findn with (lhsl := lhsl) (rhsl := rhsl) (var2exprs0 := var2exprs0); intro.
      assert (exists n, nth_error (List.split lhsl).1 n = Some v).
      admit. (* 由Hin *)
      destruct H0 as [n H0]; clear Hinl.
      specialize H with (n := n).
      case Hlhsl : (nth_error lhsl n) => [[ref1 b1]|]; rewrite Hlhsl in H; try done.
      assert (v = ref1).
      move : H0 Hlhsl.
      admit.
      case Hb1 : b1; rewrite Hb1 in H Hlhsl; clear Hb1 b1.
      case Hrhsl : (nth_error rhsl n) => [[ref2 b2]|]; rewrite Hrhsl in H; try done.
      case Hb2 : b2; rewrite Hb2 in H Hrhsl; try done; clear Hb2 b2.
      apply add_expr_non_passive_notin' with (n := n) in Hadd; clear H.
      rewrite Hlhsl Hrhsl in Hadd.
      rewrite -H1 in Hadd; rewrite -Hadd Hfind0.
      specialize find_sub_expr0_notin' with (lhsl := lhsl) (rhsl := rhsl) (n := n); intro.
      rewrite Hlhsl Hrhsl in H; rewrite H1 H.
      simpl; split; apply TopoSort.subset_refl.
      done.
      admit.
      case Hrhsl : (nth_error rhsl n) => [[ref2 b2]|]; rewrite Hrhsl in H; try done.
      case Hb2 : b2; rewrite Hb2 in H Hrhsl; try done; clear Hb2 b2.
      rewrite Hadd -H1 Hfind0 in H; rewrite H.
      specialize find_sub_expr0_in with (lhsl := lhsl) (rhsl := rhsl) (n := n); intro.
      rewrite Hlhsl Hrhsl in H2; rewrite H1 H2.
      rewrite cons_cat_eq; split; apply TopoSort.subset_refl.
      done.
      admit. (* H0与Hlhsl相悖 *)
      - (* Flipped *)
      case Hinr : (v \in (List.split rhsl).1).
      specialize add_expr_non_passive_findn with (lhsl := lhsl) (rhsl := rhsl) (var2exprs0 := var2exprs0); intro.
      assert (exists n, nth_error (List.split rhsl).1 n = Some v).
      admit. (* 由Hin *)
      destruct H0 as [n H0]; clear Hinl.
      specialize H with (n := n).
      case Hlhsl : (nth_error lhsl n) => [[ref1 b1]|]; rewrite Hlhsl in H; try done.
      case Hb1 : b1; rewrite Hb1 in H Hlhsl; clear Hb1 b1.
      case Hrhsl : (nth_error rhsl n) => [[ref2 b2]|]; rewrite Hrhsl in H; try done.
      case Hb2 : b2; rewrite Hb2 in H Hrhsl; try done; clear Hb2 b2.
      assert (v = ref2).
      move : H0 Hrhsl.
      admit.
      rewrite H1 in H0 Hfind0 Hinr; rewrite H1; clear H1 v.
      rewrite Hadd Hfind0 in H; rewrite H; clear H.
      apply add_expr_non_passive_notin' with (n := n) in Hadd.
      rewrite Hlhsl Hrhsl in Hadd.
      specialize find_sub_expr0_in with (lhsl := lhsl) (rhsl := rhsl) (n := n); intro.
      rewrite Hlhsl Hrhsl in H; rewrite H.
      rewrite cons_cat_eq; split; apply TopoSort.subset_refl.
      done.
      case Hrhsl : (nth_error rhsl n) => [[ref2 b2]|]; rewrite Hrhsl in H; try done.
      case Hb2 : b2; rewrite Hb2 in H Hrhsl; try done; clear Hb2 b2.
      clear H.
      assert (v = ref2).
      move : H0 Hrhsl.
      admit.
      specialize find_sub_expr0_notin' with (lhsl := lhsl) (rhsl := rhsl) (n := n); intro.
      rewrite Hlhsl Hrhsl in H1; rewrite H H1.
      apply add_expr_non_passive_notin' with (n := n) in Hadd.
      rewrite Hlhsl Hrhsl in Hadd; rewrite -Hadd -H Hfind0.
      simpl; split; apply TopoSort.subset_refl.
      done.
      admit.
      admit. (* H0与Hlhsl相悖 *)
      - (* 啥也不是 *)
      rewrite find_sub_expr0_notin.
      apply add_expr_non_passive_notin with (v := v) in Hadd.
      rewrite -Hadd Hfind0.
      simpl; split; apply TopoSort.subset_refl.
      1,3 : rewrite Hinl //.
      1,2 : rewrite Hinr //.
      done.
  - (* invalid *)
    inversion H. 
    case Hfind : (CEP.find v var2exprs) => [el0|]; try done.
    split; apply TopoSort.subset_refl.
  - (* when *)
    case Hstmts : (stmts_tmap (tmap0, var2exprs0) s1) => [[tmap' var2exprs']|]; rewrite Hstmts in H; try discriminate. 
    apply find_sub_exprs_eq with (v := v) in Hstmts.
    apply find_sub_exprs_eq with (v := v) in H; clear find_sub_exprs_eq.
    assert (find_sub_exprs v s1 tmap = find_sub_exprs v s1 tmap').
    admit.
    case Hfind0 : (CEP.find v var2exprs0) => [el0|]; rewrite Hfind0 in Hstmts; try done.
    - (* 有其他连接 *)
      case Hexpr1 : (find_sub_exprs v s1 tmap) => [e1|]; rewrite -H0 Hexpr1 in Hstmts; try done.
      case Hfind' : (CEP.find v var2exprs') => [el'|]; rewrite Hfind' in H Hstmts; try done.
      case Hexpr2 : (find_sub_exprs v s2 tmap) => [e2|]; rewrite Hexpr2 in H; try done.
      case Hfind : (CEP.find v var2exprs) => [el|]; rewrite Hfind in H; try done.
      admit.
    - (* 第一次连接 *)
      case Hexpr1 : (find_sub_exprs v s1 tmap) => [e1|]; rewrite -H0 Hexpr1 in Hstmts; try done.
      case Hfind' : (CEP.find v var2exprs') => [el'|]; rewrite Hfind' in H Hstmts; try done.
      case Hexpr2 : (find_sub_exprs v s2 tmap) => [e2|]; rewrite Hexpr2 in H; try done.
      case Hfind : (CEP.find v var2exprs) => [el|]; rewrite Hfind in H; try done.
      admit.
    case He1 : e1; rewrite He1 in Hstmts; try done; clear Hstmts.
    case Hexpr2 : (find_sub_exprs v s2 tmap) => [e2|]; rewrite Hexpr2 in H; try done.

  clear find_sub_exprs_eq.
  elim.
  admit.
  intros hd tl IH tmap0 tmap var2exprs0 var2exprs H v.
  simpl in H.
  case Hstmts : (stmt_tmap (tmap0, var2exprs0) hd) => [[tmap' var2exprs']|]; rewrite Hstmts in H; try discriminate. 
  apply find_sub_expr_eq with (v := v) in Hstmts.
  apply IH with (v := v) in H; clear find_sub_expr_eq IH.
  assert (find_sub_expr v hd tmap = find_sub_expr v hd tmap').
  admit.
  case Hfind0 : (CEP.find v var2exprs0) => [el0|]; rewrite Hfind0 in Hstmts; try done.
  - (* 有其他连接 *)
    simpl.
    case Hexpr1 : (find_sub_expr v hd tmap) => [e1|]; rewrite -H0 Hexpr1 in Hstmts; try done.
    case Hfind' : (CEP.find v var2exprs') => [el'|]; rewrite Hfind' in H Hstmts; try done.
    case Hexpr2 : (find_sub_exprs v tl tmap) => [e2|]; rewrite Hexpr2 in H; try done.
    case Hfind : (CEP.find v var2exprs) => [el|]; rewrite Hfind in H; try done.
    admit.
  - (* 第一次连接 *)
    simpl.
    case Hexpr1 : (find_sub_expr v hd tmap) => [e1|]; rewrite -H0 Hexpr1 in Hstmts; try done.
    case Hfind' : (CEP.find v var2exprs') => [el'|]; rewrite Hfind' in H Hstmts; try done.
    case Hexpr2 : (find_sub_exprs v tl tmap) => [e2|]; rewrite Hexpr2 in H; try done.
    case Hfind : (CEP.find v var2exprs) => [el|]; rewrite Hfind in H; try done.
    admit.
  case He1 : e1; rewrite He1 in Hstmts; try done; clear Hstmts.
  case Hexpr2 : (find_sub_exprs v tl tmap) => [e2|]; rewrite Hexpr2 in H; try done.*)
Admitted.

Lemma infer_finde_eq : forall order var2exprs tmap newtm v ss, InferWidths_fun order var2exprs tmap = Some newtm -> find_sub_exprs v ss newtm = find_sub_exprs v ss tmap.
Proof.
Admitted.    

Lemma list_gtypref_fsteq : forall ref_tgt tgt v_tgt, In v_tgt (list_gtypref ref_tgt tgt) -> ref_tgt.1 = v_tgt.1.
Proof.
Admitted.

Lemma type_refn : forall checkt ft ref n gt, ft_find_sub checkt ref = Some ft -> ft_find_sub ft n = Some gt -> ft_find_sub checkt (N.add ref n) = Some gt.
Proof.
  elim.
  intro gt.
  elim.
  intros.
  simpl in H; simpl in H0; simpl. 
  case Hn : (ref == 0%num); rewrite Hn in H; try discriminate.
  inversion H; clear H. 
  move /eqP : Hn => Hn; rewrite Hn; simpl in H0.
  case Hn0 : (n == 0%num); rewrite Hn0 in H0; try discriminate; try done.
  intros atyp IH na ref n0.
  intros.
  simpl in H; simpl in H0; simpl.
  case Hn : (ref == 0%num); rewrite Hn in H; try discriminate.
  elim.
  intros; simpl in H.
  case Hn : (ref == 0%num); rewrite Hn in H; try discriminate.
  intros v fl f ff IH ref n gt0 H H0.
  simpl in H.
  case Hn : (ref == 0%num); rewrite Hn in H; try discriminate.

  intros atyp IH na.
  elim.
  intros.
  simpl; simpl in H0; simpl in H.
  case Hn : (ref == 0%num); rewrite Hn in H; try discriminate.
  case Hn0 : (n == 0%num); rewrite Hn0 in H0; try discriminate.
  assert (((ref + n)%num == 0%num) = false).
  admit. (* Hn *)
  rewrite H1; clear H1.
  inversion H0; clear H0 H2 gt.
  case Hn4 : (num_ref atyp * na <= N.to_nat ref - 1); rewrite Hn4 in H; try discriminate.
  move /eqP : Hn0 => Hn0; rewrite Hn0 N.add_0_r Hn4.
  case Hn2 : ((N.to_nat ref - 1) mod num_ref atyp == 0); rewrite Hn2 in H; try done.
  
  intros; clear H.
  simpl in H0; simpl in H1; simpl.
  case Hn : (ref == 0%num); rewrite Hn in H0; try discriminate.
  move /eqP : Hn => Hn; rewrite Hn N.add_0_l.
  case Hn0 : (n0 == 0%num); rewrite Hn0 in H1; try discriminate; try rewrite H0; try done.
  inversion H0.
  case Hn4 : (num_ref f * n <= N.to_nat n0 - 1); rewrite Hn4 in H1; try discriminate.
  case Hn2 : ((N.to_nat n0 - 1) mod num_ref f == 0); rewrite Hn2 in H1; try done.
  case Hn0 : (n0 == 0%num); rewrite Hn0 in H1; try discriminate.
  move /eqP : Hn0 => Hn0; rewrite Hn0 N.add_0_r Hn.
  case Hn4 : (num_ref atyp * na <= N.to_nat ref - 1); rewrite Hn4 in H0; try discriminate.
  case Hn2 : ((N.to_nat ref - 1) mod num_ref atyp == 0); rewrite Hn2 in H0; rewrite -H1; try done.
  assert (((ref + n0)%num == 0%num) = false).
  admit. (* Hn *)
  rewrite H; clear H. 
  case Hn4 : (num_ref f * n <= N.to_nat n0 - 1); rewrite Hn4 in H1; try discriminate.
  case Hn5 : (num_ref atyp * na <= N.to_nat ref - 1); rewrite Hn5 in H0; try discriminate.
  case Hn2 : ((N.to_nat n0 - 1) mod num_ref f == 0); rewrite Hn2 in H1; try done.
  case Hn1 : ((N.to_nat ref - 1) mod num_ref atyp == 0); rewrite Hn1 in H0; rewrite -H1; try done.
  assert ((num_ref atyp * na <= N.to_nat (ref + n0) - 1) = false).
  admit. (* 由Hn1 Hn5 知 num_ref atyp * (na - 1) >= N.to_nat ref - 1
            由Hn4 知 num_ref atyp > n0 - 1
            由ft_find n0 = Some, 知 n0 < num_ref atyp *) 
  rewrite H; clear H. 
  assert (((N.to_nat (ref + n0) - 1) mod num_ref atyp == 0) = false).
  admit. (*由ft_find n0 = Some, 知 n0 < num_ref atyp *) 
  rewrite H.
  inversion H0; rewrite -{2}H3; simpl; clear H0.
  assert ((N.of_nat ((N.to_nat (ref + n0) - 1) mod num_ref atyp) == 0%num) = false).
  admit. (*rewrite H.*)
  rewrite H0; clear H0.
  assert (((N.to_nat (ref + n0) - 1) mod num_ref atyp) = N.to_nat n0).
  admit.
  rewrite H0 Nnat.Nat2N.id Hn4 Hn2 //.

  assert ((num_ref atyp * na <= N.to_nat (ref + n0) - 1) = false).
  admit.
  assert (((N.to_nat (ref + n0) - 1) mod num_ref atyp == 0) = false).
  admit.
  rewrite H H2; clear H H2.
  assert (ft_find_sub (Atyp f n) n0 = Some f).
  simpl; rewrite Hn0 Hn2 Hn4 //.
  move : H0 H.
  admit. (* apply IH *)
  
  case Hn1 : ((N.to_nat ref - 1) mod num_ref atyp == 0); rewrite Hn1 in H0; rewrite -H1; try done.
  assert ((num_ref atyp * na <= N.to_nat (ref + n0) - 1) = false).
  admit.
  assert (((N.to_nat (ref + n0) - 1) mod num_ref atyp == 0) = false).
  admit.
  rewrite H H2 H1; clear H H2.
  assert ((N.to_nat (ref + n0) - 1) mod num_ref atyp = N.to_nat n0).
  admit. (* 由Hn1 *)
  rewrite H Nnat.N2Nat.id; clear H.
  inversion H0; clear H0; simpl; rewrite Hn0 Hn4 Hn2 //.
  assert ((num_ref atyp * na <= N.to_nat (ref + n0) - 1) = false).
  admit.
  assert (((N.to_nat (ref + n0) - 1) mod num_ref atyp == 0) = false).
  admit.
  rewrite H H2 H1; clear H H2.
  assert (ft_find_sub (Atyp f n) n0 = Some gt).
  simpl; rewrite Hn0 Hn4 Hn2 //.
  move : H0 H. 
  admit.

  intros; simpl; simpl in H.
  simpl in H; simpl in H0.
  case Hn : (ref == 0%num); rewrite Hn in H; try discriminate.
  case Hn0 : (n == 0%num); rewrite Hn0 in H0; try discriminate.
  inversion H0; clear H0.
  move /eqP : Hn0 => Hn0; rewrite Hn0 N.add_0_r Hn //.
  assert (((ref + n)%num == 0%num) = false).
  admit. (* Hn *)
  rewrite H1; clear H1.
  case Hn4 : (num_ref atyp * na <= N.to_nat ref - 1); rewrite Hn4 in H; try discriminate.
  case Hn2 : ((N.to_nat ref - 1) mod num_ref atyp == 0); rewrite Hn2 in H.
  assert ((num_ref atyp * na <= N.to_nat (ref + n) - 1) = false).
  admit.
  assert (((N.to_nat (ref + n) - 1) mod num_ref atyp == 0) = false).
  admit.
  rewrite H1 H2; clear H1 H2.
  assert (((N.to_nat (ref + n) - 1) mod num_ref atyp) = N.to_nat n).
  admit. (* 由Hn2 *)
  rewrite H1 Nnat.N2Nat.id; clear H1.
  inversion H; simpl; rewrite Hn0 //.
  assert ((num_ref atyp * na <= N.to_nat (ref + n) - 1) = false).
  admit.
  assert (((N.to_nat (ref + n) - 1) mod num_ref atyp == 0) = false).
  admit. (* 好像不能证出来，不够紧？ *)
  rewrite H1 H2; clear H1 H2.
  assert (ft_find_sub (Btyp f) n = Some gt).
  simpl; rewrite Hn0 //.
  move : H H1.
  admit. (* n < num_ref atyp *)

  (* btyp *)
  intros.
  case Hf : ft => [fgt|fat na|fbt]; rewrite Hf in H0 H; clear Hf ft.
  simpl; simpl in H0.
  case Hn0 : (n == 0%num); rewrite Hn0 in H0; try discriminate.
  move /eqP : Hn0 => Hn0; rewrite Hn0 N.add_0_r.
  simpl in H. 
  case Hn : (ref == 0%num); rewrite Hn in H; try discriminate.
  rewrite -H0 //.
  simpl; simpl in H0.
  case Hn0 : (n == 0%num); rewrite Hn0 in H0; try discriminate.
  move /eqP : Hn0 => Hn0; rewrite Hn0 N.add_0_r.
  simpl in H.
  case Hn : (ref == 0%num); rewrite Hn in H; try discriminate.
  rewrite -H0 //.
  simpl in H.
  case Hn : (ref == 0%num); rewrite Hn in H; try discriminate.
  assert (((ref + n)%num == 0%num) = false).
  admit. (* Hn *)
  rewrite H1; clear H1.


(* TBD *)
Admitted.

Lemma list_match : forall ft v n ref2 gt, nth_error (list_gtypref v ft) n = Some ref2 -> nth_error (list_gtyp ft) n = Some gt -> ft_find_sub ft (N.sub ref2.2 v.2) = Some (Gtyp gt)
with list_matchb : forall ft v n ref2 gt, nth_error (list_gtypref_ff v ft) n = Some ref2 -> nth_error (list_gtyp_ff ft) n = Some gt -> ft_find_ff ft (N.sub ref2.2 v.2) = Some (Gtyp gt).
Proof.
  clear list_match.
  elim. 
  clear list_matchb.
  intros.
  simpl in H; simpl in H0; simpl.
  induction n as [|n'].
  simpl in H; simpl in H0.
  inversion H; inversion H0; clear H H0.
  rewrite N.sub_diag eq_refl //.
  simpl in H; apply nth_error_In in H.
  apply List.in_nil in H; done.
  intros.
  clear list_matchb.
  simpl; simpl in H0; simpl in H1.
  generalize H0; intro H0'.
  apply H with (gt := gt) in H0; try done.
  simpl in H0.
  apply nth_error_In in H0'.
  assert (N.lt v.2 ref2.2).
  admit.
  apply N.sub_gt in H2.
  assert (((ref2.2 - v.2)%num == 0%num) = false).
  admit.
  assert ((num_ref f * n <= N.to_nat (ref2.2 - v.2) - 1) = false).
  admit.
  rewrite H3 H4; clear H3 H4.
  case Hn :((N.to_nat (ref2.2 - v.2) - 1) mod num_ref f == 0).
  admit. (* 由H0 Hn *)

  (* TBD *)
Admitted.

Lemma list_match' : forall ft v n ref2 gt, nth_error (list_gtypref v ft) n = Some ref2 -> ft_find_sub ft (N.sub ref2.2 v.2) = Some (Gtyp gt) -> nth_error (list_gtyp ft) n = Some gt.
Proof.
(* TBD *)
Admitted.

Lemma list_gtypn' : forall (t : ftype) (ref : ProdVarOrder.t) (newtm : CEP.t ftype) (ref2 : ProdVarOrder.t) (n : nat) (gt : fgtyp),
  type_ref ref newtm = Some t ->
  nth_error (list_gtypref ref t) n = Some ref2 ->
  type_ref ref2 newtm = Some (Gtyp gt) ->
  nth_error (list_gtyp t) n = Some gt.
Proof.
  intros t ref newtm ref2 n gt Ht. 
  rewrite /type_ref in Ht. 
  case Hcheckt : (CEP.find (ref.1, 0%num) newtm) => [checkt|]; rewrite Hcheckt in Ht; try discriminate.
  intros.
  rewrite /type_ref in H0.
  generalize H.
  apply nth_error_In in H.
  move => H'.
  apply list_gtypref_fsteq in H; rewrite -H Hcheckt in H0.

  specialize list_match'; intro.
  apply H1 with (gt := gt) in H'; try done.
  apply type_refn with (gt := (Gtyp gt)) (n := (N.sub ref2.2 ref.2)) in Ht; try done; try rewrite -H0.
Admitted.


  (*move : Ht H' H0.
  clear Hcheckt H newtm.
  move : t checkt ref ref2 n gt.
  elim.
    - (* gtyp *)
    intros.
    simpl in H'; simpl.
    case Hn : (ref.2 == 0%num); rewrite Hn in Ht; try discriminate.
    inversion Ht; clear Ht. 
    case Hn' : (ref2.2 == 0%num); rewrite Hn' in H0; try discriminate.
    inversion H0; clear H0.
    rewrite -H1 in H'; simpl in H'; simpl.
    induction n as [|n']; try simpl; try done.
    clear IHn'; simpl in H'.
    apply nth_error_In in H'; apply List.in_nil in H'; done.
    admit.
    - (* atyp *)
    intros atyp IH n0 checkt.
    intros.
    simpl; simpl in H'.
    move : H' H0.
    apply IH; simpl.
    (*case Hcheckt : checkt => [|atyp0 na|btyp]; rewrite Hcheckt in Ht; simpl in Ht.
    case Hn : (ref.2 == 0%num); rewrite Hn in Ht; try discriminate.
    case Hn : (ref.2 == 0%num); rewrite Hn in Ht; try discriminate.
    inversion Ht;clear Ht. 
    simpl. 
    move /eqP : Hn => Hn; rewrite Hn.
    admit.
    simpl.*)
    admit. (* TBD *) 
    - (* btyp *)
    intros.
    specialize list_match'; intro.
    apply H with (gt := gt) in H'; try done.
    rewrite -H0.
    apply type_refn with (n := (N.sub ref2.2 ref.2)) in Ht; rewrite -Ht.
    admit.

Admitted.
*)
Lemma list_gtypn'0 : forall (ref : ProdVarOrder.t) (newtm : CEP.t ftype) (t : ftype) (ref2 : ProdVarOrder.t) (n : nat) (gt : fgtyp),
  type_ref ref newtm = Some t ->
  nth_error (list_gtypref ref t) n = Some ref2 ->
  nth_error (list_gtyp t) n = Some gt ->
  type_ref ref2 newtm = Some (Gtyp gt).
Proof.
(* TBD *)
Admitted.

Lemma list_gtypn : forall ref_tgt newtm checkt tgt, CEP.find (ref_tgt.1, 0%num) newtm = Some checkt -> ft_find_sub checkt ref_tgt.2 = Some tgt -> (forall n v_tgt nt',
nth_error (list_gtypref ref_tgt tgt) n = Some v_tgt -> ft_find_sub checkt v_tgt.2 = Some (Gtyp nt') -> nth_error (list_gtyp tgt) n = Some nt').
Proof.
(* 和前 type_refn ？？ *)
  intros.
  specialize list_gtypn' with (ref := ref_tgt) (newtm := newtm) (t := tgt) (ref2 := v_tgt) (n := n) (gt := nt'); intro.
  assert (v_tgt.1 = ref_tgt.1). (* list_gtypref_fsteq *)
  admit.
  rewrite /type_ref in H3.
  rewrite H4 in H3.
  rewrite H in H3.
  apply H3 in H0; clear H3; try done.
Admitted.

Lemma list_gtyp_non_passive_fsteq' : forall ref_src t_src rhsl fstl sndl newtm, type_ref ref_src newtm = Some t_src -> split_expr_non_passive ref_src t_src false = Some rhsl -> List.split rhsl = (fstl, sndl) -> fstl = (list_gtypref ref_src t_src).
Proof.
Admitted.

Lemma list_gtyp_non_passive_fsteq : forall ref_src t_src rhsl ref2 b2 newtm, type_ref ref_src newtm = Some t_src -> split_expr_non_passive ref_src t_src false = Some rhsl -> In (ref2, b2) rhsl -> ref_src.1 = ref2.1.
Proof.
  intros.
  case Hsplit : (List.split rhsl) => [fstl sndl].
  apply list_gtyp_non_passive_fsteq' with (newtm := newtm) (fstl := fstl) (sndl := sndl) in H0; try done.
  apply in_split_l in H1; simpl in H1.
  rewrite Hsplit H0 in H1; simpl in H1.
  move : H1.
  apply list_gtypref_fsteq.
Qed.

Lemma split_non_passive_typeeq : forall ref_src newtm t_src rhsl ref2 b2 n srcl src, type_ref ref_src newtm = Some t_src -> list_gtyp t_src = srcl ->
  split_expr_non_passive ref_src t_src false = Some rhsl -> nth_error rhsl n = Some (ref2, b2) -> nth_error srcl n = Some src -> type_ref ref2 newtm = Some (Gtyp src).
Proof.
  intros.
  case Hsplit : (List.split rhsl) => [fstl sndl].
  apply list_gtyp_non_passive_fsteq' with (newtm := newtm) (fstl := fstl) (sndl := sndl) in H1; try done.
  rewrite H1 in Hsplit; clear H1.
  rewrite -H0 in H3; clear H0.
  assert (nth_error (list_gtypref ref_src t_src) n = Some ref2).
  admit. (* 由H2 只有split_nth *)
  move : H H0 H3. 
  apply list_gtypn'0.
Admitted.

Lemma list_gtyprefeq : forall ref_tgt t_expr ft, ftype_equiv ft t_expr -> list_gtypref ref_tgt ft = list_gtypref ref_tgt t_expr.
Proof.
Admitted.

Lemma list_gtyp_non_passive_n : forall ref_src newtm t_src rhsl, type_ref ref_src newtm = Some t_src -> split_expr_non_passive ref_src t_src false = Some rhsl ->
forall n ref2 b2 te, nth_error rhsl n = Some (ref2, b2) -> type_ref ref2 newtm = Some (Gtyp te) -> nth_error (list_gtyp t_src) n = Some te.
Proof.
  intros.
  case Hsplit : (List.split rhsl) => [fstl sndl].
  apply list_gtyp_non_passive_fsteq' with (newtm := newtm) (fstl := fstl) (sndl := sndl) in H0; try done.
  rewrite H0 in Hsplit; clear H0.
  assert (nth_error (list_gtypref ref_src t_src) n = Some ref2).
  admit. (* 由H1 只有split_nth *)
  move : H H0 H2. 
  apply list_gtypn'.
Admitted.

Lemma split_non_passive_correct' : forall ref ref0 newtm t_tgt t_src rhsl lhsl n ref1 ref2 el, 
type_ref ref newtm = Some t_tgt -> type_ref ref0 newtm = Some t_src -> split_expr_non_passive ref0 t_src false = Some rhsl -> split_expr_non_passive ref t_tgt false = Some lhsl ->
(nth_error lhsl n = Some (ref1, false) -> nth_error rhsl n = Some (ref2, false) -> find_sub_expr ref1 (Sfcnct (Eid ref) (Eref (Eid ref0))) newtm = Some el -> Eref (Eid ref2) \in el) /\
(nth_error lhsl n = Some (ref1, true) -> nth_error rhsl n = Some (ref2, true) -> find_sub_expr ref2 (Sfcnct (Eid ref) (Eref (Eid ref0))) newtm = Some el -> Eref (Eid ref1) \in el).
Proof.
  intros.
  split; intros.
  simpl in H5; rewrite H H0 H1 H2 in H5.
  specialize find_sub_expr0_in with (rhsl := rhsl) (lhsl := lhsl) (n := n); intro.
  rewrite H3 H4 H5 in H6.
  inversion H6; clear H6.
  rewrite mem_seq1 eq_refl //.

  simpl in H5; rewrite H H0 H1 H2 in H5.
  specialize find_sub_expr0_in with (rhsl := rhsl) (lhsl := lhsl) (n := n); intro.
  rewrite H3 H4 H5 in H6.
  inversion H6; clear H6.
  rewrite mem_seq1 eq_refl //.
Qed.

Lemma split_non_passive_correct : forall ss ref ref0 newtm t_tgt t_src rhsl lhsl n ref1 ref2 el, 
  Qin (Sfcnct (Eid ref) (Eref (Eid ref0))) ss -> type_ref ref newtm = Some t_tgt -> type_ref ref0 newtm = Some t_src -> 
  split_expr_non_passive ref0 t_src false = Some rhsl -> split_expr_non_passive ref t_tgt false = Some lhsl ->
  (nth_error rhsl n = Some (ref2, false) -> nth_error lhsl n = Some (ref1, false) -> find_sub_exprs ref1 ss newtm = Some el -> Eref (Eid ref2) \in el) /\
  (nth_error lhsl n = Some (ref1, true) -> nth_error rhsl n = Some (ref2, true) -> find_sub_exprs ref2 ss newtm = Some el -> Eref (Eid ref1) \in el).
Proof.
  elim.
  intros.
  discriminate.
  intros hd tl IH.
  intros.
  split; intros.
  simpl in H.
  case Heq : (hfstmt_eqn hd (Sfcnct (Eid ref) (Eref (Eid ref0)))).
  clear H. 
  simpl in H6.
  case Hfind : (find_sub_expr ref1 hd newtm) => [e|]; rewrite Hfind in H6.
  assert (hd = (Sfcnct (Eid ref) (Eref (Eid ref0)))).
  admit. (* Heq *)
  rewrite H in Hfind; clear H.
  assert (Eref (Eid ref2) \in e).
  specialize split_non_passive_correct'; intros.
  specialize H with (ref := ref) (ref0 := ref0) (newtm := newtm) (t_tgt := t_tgt) (t_src := t_src) (rhsl := rhsl) (lhsl := lhsl) (n := n) (ref1 := ref1) (ref2 := ref2) (el := e).
  apply H in H0; try done; clear H.
  move : H0 => [H0 _].
  apply H0 in H4; clear H0; try done.
  case Hfind' : (find_sub_exprs ref1 tl newtm) => [el'|]; rewrite Hfind' in H6; try discriminate.
  inversion H6; clear H6.
  rewrite mem_cat H; done.
  discriminate.

  rewrite Heq orb_false_l in H. 
  simpl in H6.
  case Hfind : (find_sub_expr ref1 hd newtm) => [e|]; rewrite Hfind in H6; try discriminate.
  case Hfind' : (find_sub_exprs ref1 tl newtm) => [el'|]; rewrite Hfind' in H6; try discriminate.
  inversion H6; clear H6.
  assert (Eref (Eid ref2) \in el').
  specialize IH with (ref := ref) (ref0 := ref0) (newtm := newtm) (t_tgt := t_tgt) (t_src := t_src) (rhsl := rhsl) (lhsl := lhsl) (n := n) (ref1 := ref1) (ref2 := ref2) (el := el').
  apply IH in H; try done; clear IH.
  move : H => [H _].
  apply H in H4; clear H; try done.
  rewrite mem_cat H6 orb_true_r //.

  simpl in H.
  case Heq : (hfstmt_eqn hd (Sfcnct (Eid ref) (Eref (Eid ref0)))).
  clear H. 
  simpl in H6.
  case Hfind : (find_sub_expr ref2 hd newtm) => [e|]; rewrite Hfind in H6.
  assert (hd = (Sfcnct (Eid ref) (Eref (Eid ref0)))).
  admit. (* Heq *)
  rewrite H in Hfind; clear H.
  assert (Eref (Eid ref1) \in e).
  specialize split_non_passive_correct'; intros.
  specialize H with (ref := ref) (ref0 := ref0) (newtm := newtm) (t_tgt := t_tgt) (t_src := t_src) (rhsl := rhsl) (lhsl := lhsl) (n := n) (ref1 := ref1) (ref2 := ref2) (el := e).
  apply H in H0; try done; clear H.
  move : H0 => [_ H0].
  apply H0 in H4; clear H0; try done.
  case Hfind' : (find_sub_exprs ref2 tl newtm) => [el'|]; rewrite Hfind' in H6; try discriminate.
  inversion H6; clear H6.
  rewrite mem_cat H; done.
  discriminate.

  rewrite Heq orb_false_l in H. 
  simpl in H6.
  case Hfind : (find_sub_expr ref2 hd newtm) => [e|]; rewrite Hfind in H6; try discriminate.
  case Hfind' : (find_sub_exprs ref2 tl newtm) => [el'|]; rewrite Hfind' in H6; try discriminate.
  inversion H6; clear H6.
  assert (Eref (Eid ref1) \in el').
  specialize IH with (ref := ref) (ref0 := ref0) (newtm := newtm) (t_tgt := t_tgt) (t_src := t_src) (rhsl := rhsl) (lhsl := lhsl) (n := n) (ref1 := ref1) (ref2 := ref2) (el := el').
  apply IH in H; try done; clear IH.
  move : H => [_ H].
  apply H in H4; clear H; try done.
  rewrite mem_cat H6 orb_true_r //.
Admitted.

Lemma listref_split_lengtheq : forall v t b ls, split_expr_non_passive v t b = Some ls -> length ls = length (list_gtypref v t)
with listref_splitf_lengtheq : forall v t b ls, split_expr_non_passive_f v t b = Some ls -> length ls = length (list_gtypref_ff v t).
Proof.
Admitted.

Lemma listref_split_eq : forall t_tgt ref_tgt (*newtm*) v_tgt lhsl n b, (*type_ref ref_tgt newtm = Some t_tgt ->*) split_expr_non_passive ref_tgt t_tgt b = Some lhsl -> nth_error lhsl n = Some v_tgt -> nth_error (list_gtypref ref_tgt t_tgt) n = Some v_tgt.1 
with listref_splitf_eq : forall t_tgt ref_tgt (*newtm*) v_tgt lhsl n b, (*type_ref ref_tgt newtm = Some t_tgt ->*) split_expr_non_passive_f ref_tgt t_tgt b = Some lhsl -> nth_error lhsl n = Some v_tgt -> nth_error (list_gtypref_ff ref_tgt t_tgt) n = Some v_tgt.1.
Proof.
  elim. 
  intros.
  simpl in H; simpl in H0.
  inversion H; rewrite -H2 in H0; clear H H2 lhsl.
  induction n.
  simpl in H0; simpl; inversion H0; simpl; done.
  assert (length [:: (ref_tgt, b)] <= n.+1).
  simpl; apply ltn0Sn.
  apply Nats.leq_le in H. 
  apply nth_error_None in H; rewrite H in H0; discriminate.

  intros f H.
  intros.
  simpl in H0; simpl.
  apply H with (v_tgt := v_tgt) (n := n0) in H0; try done.

  intros.
  simpl in H; simpl.
  move : H H0; apply listref_splitf_eq.

  clear listref_splitf_eq.
  elim.
  intros; simpl.
  simpl in H; simpl.
  inversion H; clear H; rewrite -H2 in H0.
  apply nth_error_In in H0.
  admit. (*rewrite in_nil in H0.*)
  intros.
  simpl in H0; simpl.
  case Hf : f; rewrite Hf in H0.
  (*case Hsplit0 : (split_expr_non_passive_f (ref_tgt.1, (ref_tgt.2 + N.of_nat (num_ref f0 + 1))%num) f1 b) => [ls|]; rewrite Hsplit0 in H0; try discriminate.
  case Hsplit1 : (split_expr_non_passive (ref_tgt.1, (ref_tgt.2 + 1)%num) f0 (~~ b)) => [ls'|]; rewrite Hsplit1 in H0; try discriminate.
  inversion H0; clear H0; rewrite -H3 in H1.
  case Hn : (n < length ls').
  apply Nats.ltn_lt in Hn. 
  generalize Hn.
  apply nth_error_app1 with (l' := ls) in Hn.
  move => Hn'.
  apply listref_split_lengtheq in Hsplit1; rewrite Hsplit1 in Hn'.
  apply nth_error_app1 with (l' := list_gtypref_ff (ref_tgt.1, (ref_tgt.2 + N.of_nat (num_ref f0 + 1))%num) f1) in Hn'.
  admit. (* %list ?? *)
  specialize AuxLemmas.ltn_geq_total with (n := n) (m := length ls'); intro.
  rewrite Hn in H0; clear Hn; rewrite orb_false_l in H0.
  apply Nats.leq_le in H0.
  apply listref_split_lengtheq in Hsplit1; rewrite Hsplit1 in H0.
  apply nth_error_app2 with (l' := list_gtypref_ff (ref_tgt.1, (ref_tgt.2 + N.of_nat (num_ref f0 + 1))%num) f1) in H0.
  admit.*)
Admitted.

Lemma InferWidths_fun_correct : forall ps ss (hfs : HiFP.hfstmt) (inferorder : seq ProdVarOrder.t) (var2exprs : CEP.t (seq HiFP.hfexpr)) (tmap newtm : CEP.t ftype),
  stmts_tmap (ports_tmap ps, CEP.empty (seq HiFP.hfexpr)) ss = Some (tmap, var2exprs) -> Qin hfs ss ->
  InferWidths_fun inferorder var2exprs tmap = Some newtm -> match hfs with
    | Sfcnct (Eid ref_tgt) (Eref (Eid ref_src)) => match type_ref ref_tgt newtm, type_ref ref_src newtm with
                                      | Some t_tgt, Some t_src => connect_non_passive_type t_tgt t_src
                                      | _, _ => True
                                      end 
    | Sfcnct (Eid ref_tgt) (Eref _) => True
    | Sfcnct (Eid ref_tgt) expr_src => match type_ref ref_tgt newtm, type_of_hfexpr expr_src newtm with
                                      | Some tgt, Some t_expr => connect_type_compatible tgt t_expr
                                      | _, _ => True
                                      end
    | _ => True
    end.
Proof.
  intros ps ss hfs inferorder var2exprs tmap newtm Hpre Hin Hinfer.
  case Hs : hfs => [||||||ref expr||]; try done.
  case He : expr => [ct c| c e1 | u e1 | op e1 e2 | c e1 e2 | c e1 | ref0 ]. 
  (* const *)
  rewrite -He; clear He ct c; rewrite Hs in Hin; clear Hs hfs.
  case Href : ref => [ref_tgt|||]; try done.
  case Hbase : (type_ref ref_tgt newtm) => [tgt|]; try done.
  case Hte : (type_of_hfexpr expr newtm) => [t_expr|] ; try done.
  rewrite /connect_type_compatible.
  apply rwP with (P := ftype_equiv tgt t_expr /\
    check_connect_fgtyp_compatible (list_gtyp tgt) (list_gtyp t_expr)).
  apply andP.
  split. 
  admit. (* 对connection语句的要求 *)

  apply check_connect_fgtyp_compatible4n with (ft := list_gtyp tgt) (te := list_gtyp t_expr).
  intros n.
  case Hlhs : (nth_error (list_gtyp tgt) n) => [gt|].
  case Hrhs : (nth_error (list_gtyp t_expr) n) => [gte|]; try done.
  case Hv : (nth_error (list_gtypref ref_tgt tgt) n) => [v_tgt|].
  generalize Hinfer.
  assert (exists order1 order2, (inferorder = order1 ++ (v_tgt :: order2)) /\ (v_tgt \notin order1) 
    /\ (v_tgt \notin order2)).
  admit. (* inferorder 的正确性，是展开时的标号 *)
  move : H => [order1 [order2 [H [Horder1 Horder2]]]].
  rewrite H in Hinfer.
  move => Hinfer'.
  case Hinfer1 : (InferWidths_fun order1 var2exprs tmap) => [tmap'|].
  assert (Hinfer2 : InferWidths_fun (v_tgt :: order2) var2exprs tmap' = Some newtm).
  move : Hinfer Hinfer1.
  apply infer_cons_order.
  clear Hinfer.
  simpl in Hinfer2.
  case Hel : (CEP.find v_tgt var2exprs) => [el|]; rewrite Hel in Hinfer2; try done.
  case Hinfer : (InferWidth_fun v_tgt el tmap') => [newtm'|]; rewrite Hinfer in Hinfer2; try discriminate.
  specialize split_expr_type_correct; intro.
  case Hsplit : (split_expr_connect expr t_expr) => [rhs_expr_ls|].
  generalize Hsplit.
  apply H0 with (expr := expr) (rhs_expr_ls := rhs_expr_ls) (t_expr := t_expr) (newtm := newtm) (n := n) in Hsplit; try done; clear H0.
  move => Hsplit'.
  case Htexpr : (nth_error rhs_expr_ls n) => [texpr|]; rewrite Htexpr in Hsplit.
  rewrite Hrhs in Hsplit.
  apply InferWidth_fun_correct with (pv := v_tgt) (el := el) (tmap := tmap') (newtm := newtm') (expr := texpr) in Hinfer.
  generalize Hv.
  apply nth_error_In in Hv.
  apply list_gtypref_fsteq in Hv; rewrite -Hv in Hinfer; clear Hv.
  move => Hv.
  case Htgt0 : (CEP.find (ref_tgt.1, 0%num) newtm') => [checkt'|]; rewrite Htgt0 in Hinfer.
  case Hsub0 : (ft_find_sub checkt' v_tgt.2) => [nt|]; rewrite Hsub0 in Hinfer.
  rewrite /type_ref in Hbase.
  case Htgt : (CEP.find (ref_tgt.1, 0%num) newtm) => [checkt|]; rewrite Htgt in Hbase; try discriminate.
  apply inferwidths_ls with (var2exprs := var2exprs) (tmap := newtm') (tmap' := newtm) (checkt := checkt') (checkt' := checkt) in Horder2; try done.
  rewrite Hsub0 in Horder2; clear Hsub0.
  case Hnt : nt => [nt'||]; rewrite Hnt in Hinfer.
  assert (type_of_hfexpr texpr newtm = type_of_hfexpr texpr newtm').
  admit.
  rewrite -H0 Hsplit in Hinfer; clear H0.
  rewrite Hnt in Horder2; clear Hnt nt.
  apply list_gtypn with (tgt := tgt) (n := n) (v_tgt := v_tgt) (nt' := nt') in Htgt; try done; rewrite Htgt in Hlhs.
  inversion Hlhs; clear Hlhs; rewrite -H1; apply Hinfer.
  admit. (* 从某个地方来的连接合法的前提 *)
  admit. (* 应只涉及gtyp *)
  admit. (* 应只涉及gtyp *)
  apply nth_error_In in Hv; apply list_gtypref_fsteq in Hv; rewrite -Hv; clear Hv; done.
  apply nth_error_In in Hv; apply list_gtypref_fsteq in Hv; rewrite -Hv; clear Hv; done.
  admit. (* 不是None *)
  admit. (* 不是None *)
  rewrite Href in Hin; clear Href ref.
  apply find_sub_exprs_eq with (ss := ss) (tmap0 := ports_tmap ps) (tmap := tmap) (var2exprs0 := CEP.empty (seq HiFP.hfexpr)) (var2exprs := var2exprs) (v := v_tgt) in Hpre; try done.
  simpl in Hpre.
  case Hfinde : (find_sub_exprs v_tgt ss tmap) => [el'|]; rewrite Hfinde in Hpre. 
  rewrite Hel in Hpre.
  case Hel' : el'; rewrite Hel' in Hpre. 
  rewrite -Hel' in Hpre; clear Hel'.
  move : Hpre => [_ Hpre]; move : Hpre; apply TopoSort.in_subset_trans.
  apply split_exprs_connect_correct with (tgt := v_tgt) (ss := ss) (ref_tgt := ref_tgt) (expr := expr) (t_expr := t_expr) (rhsl := rhs_expr_ls) (newtm := newtm) (n := n) (texpr := texpr) (el := el'); try done.
  specialize list_gtyprefeq with (t_expr := t_expr) (ft := tgt) (ref_tgt := ref_tgt); intro.
  rewrite -H0; clear H0.
  done.
  admit.
  rewrite -Hfinde; move : Hinfer'.
  apply infer_finde_eq.
    rewrite -Hel' in Hpre; clear Hel'.
    move : Hpre => [_ Hpre]; move : Hpre; apply TopoSort.in_subset_trans.
    apply split_exprs_connect_correct with (tgt := v_tgt) (ss := ss) (ref_tgt := ref_tgt) (expr := expr) (t_expr := t_expr) (rhsl := rhs_expr_ls) (newtm := newtm) (n := n) (texpr := texpr) (el := el'); try done.
    specialize list_gtyprefeq with (t_expr := t_expr) (ft := tgt) (ref_tgt := ref_tgt); intro.
    rewrite -H0; clear H0.
    done.
    admit.
    rewrite -Hfinde; move : Hinfer'.
    apply infer_finde_eq.
    done.
  admit. (* 不是None *)
  admit. (* 不是None *)
  admit. (* 不是None *)
  admit. (* 不是None *)
  admit. (* 不是None *)
  admit. (* 不是None *)
  case Hnth : (nth_error (list_gtyp t_expr) n) => [nth|]; try done.
  admit. (* Hlhs与Hnth长度匹配 *)

  (* 所有passive的expr都一样 *)
  admit.
  admit.
  admit.
  admit.
  admit.

  (* ref non_passive *)
  rewrite He in Hs; clear He expr; rewrite Hs in Hin; clear Hs hfs.
  case Href : ref => [ref_tgt|||]; try done.
  case Href0 : ref0 => [ref_src|||]; try done.
  case Htgt : (type_ref ref_tgt newtm) => [t_tgt|]; try done.
  case Hsrc : (type_ref ref_src newtm) => [t_src|]; try done.
  rewrite Href Href0 in Hin; clear Href Href0 ref ref0.
  rewrite /connect_non_passive_type.
  apply rwP with (P := ftype_equiv t_tgt t_src /\ check_connect_non_passive_fgtyp (list_gtyp t_tgt) (list_gtyp t_src) (list_flip t_tgt false)).
  apply andP.
  split. 
  admit. (* 对connection语句的要求 *)
  apply check_connect_non_passive_fgtyp4n.
  intro n.
  case Hcheckfl : (nth_error (list_flip t_tgt false) n) => [b|]; try done.
  case Hb : b.

  (* Flip *)
  admit.
  (* Nflip *)
  case Hlhs : (nth_error (list_gtyp t_tgt) n) => [gt|]; try done.
  case Hrhs : (nth_error (list_gtyp t_src) n) => [gte|]; try done.
  case Hv : (nth_error (list_gtypref ref_tgt t_tgt) n) => [v_tgt|].
  assert (v_tgt \in inferorder).
  admit. (* inferorder 的正确性，是展开时的标号 *)
  assert (exists order1 order2, inferorder = order1 ++ (v_tgt :: order2) /\ ~ v_tgt \in order1 /\ ~ v_tgt \in order2).
  admit. (* 由H推出 *)
  clear H.
  move : H0 => [order1 [order2 [H2 [Horder1 Horder2]]]].
  rewrite H2 in Hinfer; rewrite /InferWidths_fun in Hinfer.
  case Hinfer1 : (InferWidths_fun order1 var2exprs tmap) => [tmap'|].
  assert (Hinfer2 : InferWidths_fun (v_tgt :: order2) var2exprs tmap' = Some newtm).
  move : Hinfer Hinfer1.
  apply infer_cons_order.
  clear Hinfer.
  simpl in Hinfer2.
  case Hel : (CEP.find v_tgt var2exprs) => [el|]; rewrite Hel in Hinfer2; try done.
  case Hinfer : (InferWidth_fun v_tgt el tmap') => [newtm'|]; rewrite Hinfer in Hinfer2; try discriminate.
  case Hsplit_rhs : (split_expr_non_passive ref_src t_src false) => [rhsl|].
  case Hrhsl : (nth_error rhsl n) => [[ref2 b2]|].
  case Hsplit_lhs : (split_expr_non_passive ref_tgt t_tgt false) => [lhsl|].
  case Hlhsl : (nth_error lhsl n) => [[ref1 b1]|].
  apply InferWidth_fun_correct with (pv := v_tgt) (el := el) (tmap := tmap') (newtm := newtm') (expr := (Eref (Eid ref2))) in Hinfer.
  generalize Hv.
  apply nth_error_In in Hv.
  apply list_gtypref_fsteq in Hv; rewrite -Hv in Hinfer; clear Hv.
  move => Hv.
  case Htgt0 : (CEP.find (ref_tgt.1, 0%num) newtm') => [checkt'|]; rewrite Htgt0 in Hinfer.
  case Hsub0 : (ft_find_sub checkt' v_tgt.2) => [nt|]; rewrite Hsub0 in Hinfer.
  case Hnt : nt => [nt'||]; rewrite Hnt in Hinfer.
  simpl in Hinfer.
  case Hsrc0 : (type_ref ref2 newtm') => [f0|]; rewrite Hsrc0 in Hinfer.
  case Hf0 : f0 => [te||]; rewrite Hf0 in Hinfer.
  rewrite Hf0 in Hsrc0; clear Hf0 f0; rewrite Hnt in Hsub0; clear Hnt nt.
  case Htgtn : (CEP.find (ref_tgt.1, 0%num) newtm) => [checkt|].
  generalize Hinfer2.
  apply inferwidths_ls with (el := order2) (checkt := checkt') (checkt' := checkt) (a := v_tgt) in Hinfer2; simpl in Hinfer2; try done.
  rewrite Hinfer2 in Hsub0; clear Hinfer2.
  move => Hinfer2.
  apply list_gtypn with (tgt := t_tgt) (n := n) (v_tgt := v_tgt) (nt' := nt') in Htgtn; try done. rewrite Htgtn in Hlhs.
  inversion Hlhs; clear Hlhs; rewrite -H0; clear H0.
  generalize Hsrc.
  rewrite /type_ref in Hsrc0; rewrite /type_ref in Hsrc.
  move => Hsrc'.
  case Href2 : (CEP.find (ref_src.1, 0%num) newtm) => [checkt0|]; rewrite Href2 in Hsrc; try discriminate.
  apply list_gtyp_non_passive_n with (rhsl := rhsl) (n := n) (ref2 := ref2) (b2 := b2) (te := te) in Hsrc'; try done.
  rewrite Hsrc' in Hrhs; inversion Hrhs.
  rewrite -H0; apply Hinfer.
  admit.
  apply list_gtyp_non_passive_fsteq with (rhsl := rhsl) (ref2 := ref2) (b2 := b2) in Hsrc'; try done.
  rewrite Hsrc' in Href2; clear Hsrc'.
  case Href2' : (CEP.find (ref2.1, 0%num) newtm') => [checkt0'|]; rewrite Href2' in Hsrc0; try discriminate.
  apply inferwidths_ls with (el := order2) (checkt := checkt0') (checkt' := checkt0) (a := ref2) in Hinfer2; simpl in Hinfer2; try done.
  rewrite Hinfer2 in Hsrc0; clear Hinfer2.
  rewrite /type_ref Href2 Hsrc0; done.
  admit. (* topo规定 *)
  move : Hrhsl; apply nth_error_In.
  rewrite /type_ref Htgtn in Htgt; done.
  admit. (* Horder2 *)
  apply nth_error_In in Hv; apply list_gtypref_fsteq in Hv; rewrite -Hv; done.
  apply nth_error_In in Hv; apply list_gtypref_fsteq in Hv; rewrite -Hv; done.
  admit. (* 不是None *)
  admit. (* 应只涉及gtyp *)
  admit. (* 应只涉及gtyp *)
  admit. (* 不是None *)
  admit. (* 应只涉及gtyp *)
  admit. (* 应只涉及gtyp *)
  admit. (* 不是None *)
  admit. (* 不是None *)

  apply find_sub_exprs_eq with (v := v_tgt) in Hpre; simpl in Hpre.
  rewrite Hel in Hpre.
  case Hsube : (find_sub_exprs v_tgt ss tmap) => [el'|]; rewrite Hsube in Hpre; try done.
  case Hel' : el'; rewrite Hel' in Hpre. 
  1,2:rewrite -Hel' in Hpre; clear Hel'.
  1,2:move : Hpre => [_ Hpre]; move : Hpre.
  1,2:apply TopoSort.in_subset_trans.
  assert (Hsube' : find_sub_exprs v_tgt ss newtm = Some el').
  admit. (* Hsube *)
  clear Hsube.
  apply split_non_passive_correct with (newtm := newtm) (t_tgt := t_tgt)(t_src := t_src) (rhsl := rhsl) (lhsl := lhsl) (n := n) (ref1 := v_tgt) (ref2 := ref2) (el := el') in Hin; try done.
  move : Hin => [Hin _].
  assert (b2 = b /\ b1 = b).
  admit.
  move : H => [H1 H1']; rewrite H1 Hb in Hrhsl; rewrite H1' Hb in Hlhsl; clear H1 H1'.
  apply Hin; try done.
  apply listref_split_eq with (v_tgt := (ref1, false)) (n := n) in Hsplit_lhs; try done; simpl in Hsplit_lhs.
  rewrite Hv in Hsplit_lhs; inversion Hsplit_lhs; done.
    assert (Hsube' : find_sub_exprs v_tgt ss newtm = Some el').
    admit. (* Hsube *)
    clear Hsube.
    apply split_non_passive_correct with (newtm := newtm) (t_tgt := t_tgt)(t_src := t_src) (rhsl := rhsl) (lhsl := lhsl) (n := n) (ref1 := v_tgt) (ref2 := ref2) (el := el') in Hin; try done.
    move : Hin => [Hin _].
    assert (b2 = b /\ b1 = b).
    admit.
    move : H => [H1 H1']; rewrite H1 Hb in Hrhsl; rewrite H1' Hb in Hlhsl; clear H1 H1'.
    apply Hin; try done.
    apply listref_split_eq with (v_tgt := (ref1, false)) (n := n) in Hsplit_lhs; try done; simpl in Hsplit_lhs.
    rewrite Hv in Hsplit_lhs; inversion Hsplit_lhs; done.
  admit. (* 不是None *)
  admit. (* 不是None *)
  admit. (* 不是None *)
  admit. (* 不是None *)
  admit. (* 不是None *)
  admit. (* 不是None *)
  admit. (* 不是None *)
  admit. (* 不是None *)
  case Hnth : (nth_error (list_gtyp t_tgt) n) => [nth|]; try done.
  admit. (* 不是None *)
  case Hnth' : (nth_error (list_gtyp t_src) n) => [nth'|]; try done.
  admit. (* 不是None *)
Admitted.

Definition InferWidths_m F : option (HiFP.hfmodule * CEP.t ftype) :=
  match InferWidths_stage1 F with
  | Some newtm => match InferWidths_stage2 F newtm with
                  | Some nm => Some (nm, newtm)
                  | _ => None
                  end
  | None => None
  end.

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

Lemma Sem_wdgeqmax ss : forall vm_old ct_old vm_new ct_new tmap, Sem_frag_stmts vm_old ct_old ss vm_new ct_new tmap -> (forall v t el, CEP.find v vm_new = Some t -> find_sub_exprs v ss tmap = Some el -> (forall e te, e \in el -> type_of_hfexpr e tmap = Some (Gtyp te) -> sizeof_fgtyp (type_of_vx t) >= sizeof_fgtyp te)).
Proof.
  induction ss. 
  simpl. 
  intros.
  inversion H1; rewrite -H5 in H2; rewrite in_nil in H2; discriminate.
  intros vm_old ct_old vm_new ct_new tmap Hsem.
  simpl in Hsem.
  destruct Hsem as [vm' [ct' [Hsem0 Hsem]]].
  intros v t el Hv Hfinde e te Hin Hte. 
  simpl in Hfinde.
  case Hfinde0 : (find_sub_expr v h tmap) => [e0|]; rewrite Hfinde0  in Hfinde; try discriminate.
  case Hfinde1 : (find_sub_exprs v ss tmap) => [e1|]; rewrite Hfinde1 in Hfinde; try discriminate.
  inversion Hfinde; clear Hfinde.
  rewrite -H0 in Hin; clear H0 el.
  rewrite mem_cat in Hin.
  case Hin0 : (e \in e0); rewrite Hin0 in Hin. 
  clear Hin Hsem Hfinde1. 

  admit.
  clear Hin0; rewrite orb_false_l in Hin.
  apply IHss with (v := v) (t := t) (el := e1) (e := e) (te := te) in Hsem; try done.
Admitted.

Lemma geq_conj2mux : forall tmap (gt initt : fgtyp) (el : seq HiFP.hfexpr) eftl (nt : fgtyp), (forall (texpr : HiFP.hfexpr) (te : fgtyp), texpr \in el -> type_of_hfexpr texpr tmap = Some (Gtyp te) -> ((sizeof_fgtyp gt) >= (sizeof_fgtyp te))) ->
        fil_ftlist [seq type_of_hfexpr e tmap | e <- el] = Some eftl -> sizeof_fgtyp initt = 0 -> max_ftlist eftl initt = Some nt -> ((sizeof_fgtyp gt) >= (sizeof_fgtyp nt)).
Proof.
  intros tmap gt initt.
  elim.
  intros.
  simpl in H0.
  inversion H0; clear H0.
  rewrite -H4 in H2.
  simpl in H2.
  inversion H2; clear H2.
  rewrite -H3 H1.
  rewrite /sizeof_fgtyp.
  case Het : gt; try done.

  intros hd tl IH eftl nt H Heftl Hinitt Hmax.
  simpl in Heftl.
  case Hhd : (type_of_hfexpr hd tmap) => [f|]; rewrite Hhd in Heftl; try discriminate.
  case Hf : f => [hdt||]; rewrite Hf in Hhd Heftl; clear Hf; try discriminate.
  case Heftl' : (fil_ftlist [seq type_of_hfexpr e tmap | e <- tl]) => [eftl'|]; rewrite Heftl' in Heftl; try discriminate.
  inversion Heftl; clear Heftl.
  rewrite -H1 in Hmax.
  simpl in Hmax.
  case Hmax' : (max_ftlist eftl' initt) => [nt'|]; rewrite Hmax' in Hmax; try discriminate.

  assert (max_fgtyp hdt nt' = Some nt -> sizeof_fgtyp nt' <= sizeof_fgtyp gt -> sizeof_fgtyp hdt <= sizeof_fgtyp gt -> sizeof_fgtyp nt <= sizeof_fgtyp gt).
  clear.
  intros.
  rewrite /max_fgtyp in H.
  case Hhd : hdt => [w|w|w|w|||]; rewrite Hhd in H H1; try discriminate.
  case Hnt' : nt' => [w'|w'|w'|w'|||]; rewrite Hnt' in H H0; try discriminate.
  inversion H; clear H.
  simpl in H1; simpl in H0; simpl.

  specialize Nat.max_spec_le with (n := w) (m := w'); intro.
  move : H1 H0.
  admit.
  case Hnt' : nt' => [w'|w'|w'|w'|||]; rewrite Hnt' in H H0; try discriminate.
  inversion H; clear H.
  simpl in H1; simpl in H0; simpl.
  move : H1 H0.
  admit.
  case Hnt' : nt' => [w'|w'|w'|w'|||]; rewrite Hnt' in H H0; try discriminate.
  inversion H; clear H.
  simpl in H1; simpl in H0; simpl.
  move : H1 H0.
  admit.
  case Hnt' : nt' => [w'|w'|w'|w'|||]; rewrite Hnt' in H H0; try discriminate.
  inversion H; clear H.
  simpl in H1; simpl in H0; simpl.
  move : H1 H0.
  admit.

  apply H0 in Hmax; try done; clear H0.
  apply IH with (eftl := eftl'); try done.
  intros expr tge Hin.
  apply H.
  rewrite in_cons Hin.
  rewrite orb_true_r; done.
  apply H with (texpr := hd); try done.
  rewrite in_cons.
  rewrite eq_refl.
  rewrite orb_true_l; done.
Admitted.

Theorem InferWidths_correct' :
  forall (F : HiFP.hfmodule) (vm : CEP.t vertex_type) (vm' : CEP.t vertex_type) (ct : CEP.t def_expr),
    match InferWidths_m F with
    | Some (F', _) => Sem F' vm' ct -> Sem F vm ct -> vm_le vm vm'
    | _ => True
    end.
Proof.
  intros.
  case Hinfer : (InferWidths_m F) => [[F' ftmap]|]; try done.
  intros Hsem' Hsem.
  rewrite /vm_le; intro v.
  case Ht' : (CEP.find v vm') => [t'|].
  case Ht : (CEP.find v vm) => [t|]; try done.
  case Himpli : (not_implicit (type_of_vx t')); try done.
  rewrite /InferWidths_m in Hinfer.
  case Hinfer1 : (InferWidths_stage1 F) => [newtm|]; rewrite Hinfer1 in Hinfer; try discriminate.
  rewrite /InferWidths_stage1 in Hinfer1.
  case HF : F => [mv ps ss|]; rewrite HF in Hinfer1; try discriminate.
  rewrite HF in Hsem Hinfer; clear HF F.
  case Hpre : (stmts_tmap (ports_tmap ps, CEP.empty (seq HiFP.hfexpr)) ss) => [[tmap' var2exprs]|]; rewrite Hpre in Hinfer1; try discriminate.
  (*case Hexplireg : (explireg_stmts ss) => [expli_reg|]; rewrite Hexplireg in Hinfer1; try discriminate.
  case Hdraw : (drawg (CEP.elements var2exprs) tmap' expli_reg emptyg [::]) => [[theg vertices]|]; rewrite Hdraw in Hinfer1; try discriminate.
  case Htopo : (TopoSort.topo_sort vertices theg) => [inferorder||]; rewrite Htopo in Hinfer1; try discriminate.
  assert (v \in inferorder).
  admit. (* inferorder 的正确性，是展开时的标号 *)
  assert (exists order1 order2, inferorder = order1 ++ (v :: order2) /\ ~ v \in order1 /\ ~ v \in order2).
  admit. (* 由H推出 *)
  clear H.
  move : H0 => [order1 [order2 [H2 [Horder1 Horder2]]]].
  rewrite H2 in Hinfer1; rewrite /InferWidths_fun in Hinfer1.
  case Hinfer1' : (InferWidths_fun order1 var2exprs tmap') => [tmap'0|].
  assert (Hinfer2 : InferWidths_fun (v :: order2) var2exprs tmap'0 = Some newtm).
  move : Hinfer1 Hinfer1'.
  apply infer_cons_order.
  clear Hinfer1.
  simpl in Hinfer2.
  case Hel : (CEP.find v var2exprs) => [el|]; rewrite Hel in Hinfer2; try discriminate.
  case Hinfer1 : (InferWidth_fun v el tmap'0) => [newtm'|]; rewrite Hinfer1 in Hinfer2; try discriminate.
  rewrite /InferWidth_fun in Hinfer1.
  case Hfil : (fil_ftlist [seq type_of_hfexpr e tmap'0 | e <- el]) => [eftl|]; rewrite Hfil in Hinfer1; try done.
  case Hinit : (CEP.find (v.1, 0%num) tmap'0) => [init|]; rewrite Hinit in Hinfer1; try discriminate.
  case Hf : (ft_find_sub init v.2) => [f|]; rewrite Hf in Hinfer1; try discriminate.
  case Hinitt : f => [initt||]; rewrite Hinitt in Hinfer1; try discriminate.
  rewrite Hinitt in Hf; clear Hinitt f.
  assert (not_implicit initt = false). 
  admit. (* Himpli *)
  rewrite H in Hinfer1; clear H.
  case Hmax : (max_ftlist eftl initt) => [nt|]; rewrite Hmax in Hinfer1; try discriminate.
  case Hset : (ft_set_sub init nt v.2) => [nt0|]; rewrite Hset in Hinfer1; try discriminate. 
  inversion Hinfer1; clear Hinfer1.
  assert (type_ref v newtm' = Some (Gtyp (type_of_vx t'))).
  admit.
  rewrite /type_ref -H0 in H. 
  rewrite CEP.Lemmas.find_add_eq in H; try apply CEP.SE.eq_refl.
  apply set_find_sub in Hset.
  rewrite H in Hset; clear H. 
  inversion Hset; clear Hset; rewrite H1; clear H1.
  rewrite /Sem in Hsem.
  case Hpre0 : (ModuleGraph_simplified.ports_stmts_tmap ps ss vm) => [pmap|]; rewrite Hpre0 in Hsem; try done.
  move : Hsem => [_ Hsem].
  (*case Hpre1 : (ModuleGraph_simplified.stmts_tmap (pmap, pmap) ss vm) => [[tmap0 t0]|]; rewrite Hpre1 in Hsem; try done.
  destruct Hsem as [vm0 [ct0 [_ Hsem]]].
  apply geq_conj2mux with (tmap := tmap0) (initt := initt) (el := el) (eftl := eftl); try done.
  apply Sem_wdgeqmax with (vm_old := vm0) (ct_old := ct0) (ss := ss) (vm_new := vm) (ct_new := ct) (v := v); try done.
  rewrite -Hel; move : Hpre1 Hpre.
  admit. (* TBD!! *)
  admit. (* topo结果 TBD!! *)
  admit. (* topo结果 TBD!! *)
  apply ft_set_sub_eq with (nt' := nt) (n := v.2) (init := (Gtyp initt)); try done.
  simpl.
  apply max_ftlist_correct in Hmax; move : Hmax => [_ Hmax]; done.

  admit. (* 不是None *)
  admit. (* 不是None *)
  case Ht : (CEP.find v vm) => [t|]; try done.
  admit. (* 不是None *) *)*)
Admitted.

(*Theorem InferWidths_correct :
  forall (F : HiFP.hfmodule) (vm' : CEP.t vertex_type) (ct : CEP.t def_expr),
    match InferWidths_m F with
    | Some F' => Sem F' vm' ct -> Sem F (make_vm_implicit F vm') ct
    | _ => True
    end.
Proof.
assert (Sem F' vm' ct -> Sem_frag_stmts' vm' ss tmap).
assert (Sem_frag_stmts' vm' ss tmap -> InferWidths_fun inferorder var2exprs tmap = Some newtm -> Sem_frag_stmts' vm' ss' tmap).
assert (Sem F' vm' ct -> Sem_frag_stmts' vm' ss' tmap -> Sem F (make_vm_implicit F vm') ct).
Admitted.*)
