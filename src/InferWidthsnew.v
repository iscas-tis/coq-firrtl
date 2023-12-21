From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq ssrfun.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.
From firrtl Require Import Firrtl Env HiEnv HiFirrtl ModuleGraph TopoSort. 

Fixpoint tmap_type_size (t : ftype) : N :=
(* calculates how many entries in tmap.env would be created/affected by a variable of type t *)
match t with
| Gtyp _ => 1
| Atyp t _ => tmap_type_size t (* only one entry is needed for the array *)
| Btyp ff => tmap_type_size_fields ff
end
with tmap_type_size_fields (ff : ffield) : N :=
match ff with
| Fnil => 0
| Fflips _ _ ft ff' => tmap_type_size ft + tmap_type_size_fields ff'
end.

(* 以下函数都是只考虑gtyp的版本，并且array只考虑一个元素 *)
Fixpoint ft_find_sub (checkt : ftype) (num : N) : option fgtyp :=
  match checkt with
  | Gtyp gt => if num == N0 then Some gt else None
  | Atyp atyp n => ft_find_sub atyp num
  | Btyp ff => if num >= (tmap_type_size_fields) ff then None else ft_find_ff ff num 
  end
with ft_find_ff (ff : ffield) (num : N) : option fgtyp :=
  match ff with
  | Fflips v0 _ ft ff' => if num >= (N.of_nat (tmap_type_size ft)) (* 不在该field中, 找下一个field *)
                              then ft_find_ff ff' (N.sub num (N.of_nat (num_ref ft)))
                           else (* 在field v0中 *)
                              ft_find_sub ft num
  | _ => None
  end.

Fixpoint ft_check_flip (checkt : ftype) (num : N) (fl : bool) : option bool :=
  match checkt with
  | Gtyp gt => if num == N0 then Some fl else None
  | Atyp atyp n => ft_check_flip atyp num fl
  | Btyp ff => if num >= (tmap_type_size_fields) ff then None else ft_check_flip_f ff num fl
  end
with ft_check_flip_f (ff : ffield) (num : N) (fl : bool) : option bool :=
  match ff with
  | Fflips v0 Flipped ft ff' => if num >= (N.of_nat (tmap_type_size ft)) (* 不在该field中, 找下一个field *)
                                  then ft_check_flip_f ff' (N.sub num (N.of_nat (num_ref ft))) fl
                              else (* 在field v0中 *)
                                  ft_check_flip ft num (~~fl)
  | Fflips v0 Nflip ft ff' => if num >= (N.of_nat (tmap_type_size ft)) (* 不在该field中, 找下一个field *)
                                  then ft_check_flip_f ff' (N.sub num (N.of_nat (num_ref ft))) fl
                              else (* 在field v0中 *)
                                  ft_check_flip ft num fl
  | _ => None
  end.

Fixpoint ft_set_sub (checkt : ftype) (newt : fgtyp) (num : N) : option ftype :=
  match checkt with
  | Gtyp _ => if num == N0 then Some (Gtyp newt) else None
  | Atyp atyp n => match ft_set_sub atyp newt num with
                      | Some natyp => Some (Atyp natyp n)
                      | None => None
                      end
  | Btyp ff => if num >= (tmap_type_size_fields) ff then None else
                match ft_set_sub_f ff newt num with
                | Some newf => Some (Btyp newf)
                | None => None
                end
  end
with ft_set_sub_f (ff : ffield) (newt : fgtyp) (num : N) : option ffield :=
  match ff with
  | Fflips v0 fl ft ff' => if N.to_nat num >= (tmap_type_size ft) (* 不在该field中, 找下一个field *)
                            then match ft_set_sub_f ff' newt (N.sub num (N.of_nat (tmap_type_size ft))) with
                                | Some newf => Some (Fflips v0 fl ft newf)
                                | None => None
                                end
                          else (* 在field v0中 *)
                            match ft_set_sub ft newt num with
                            | Some newt' => Some (Fflips v0 fl newt' ff')
                            | None => None
                            end
  | _ => None
  end.

(* 有必要check这几个函数功能是否正确 *)
Definition testaty0 := (Atyp (Gtyp (Fuint_implicit 0)) 2).
Definition testaty := (Atyp (Atyp (Gtyp (Fuint 4)) 2) 2).
Definition testbty0 := (Btyp (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 0)) 2) (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 1)) 2) Fnil))).
Definition testbty := (Btyp (Fflips (1%num) Flipped (Btyp (Fflips (1%num) Nflip (Gtyp (Fuint_implicit 0)) (Fflips (1%num) Flipped (Atyp (Gtyp (Fuint_implicit 1)) 2) Fnil))) (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 2)) 2) Fnil))).
Definition testgt := (Fuint 4).
Compute (tmap_type_size testaty). 
Compute (ft_find_sub testbty 2%num).
Compute (ft_check_flip testbty 2%num false).
Compute (ft_set_sub testbty testgt 3%num).

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

(* type of mux expression *)
Fixpoint mux_types (t1 : ftype) (t2 : ftype) : option ftype :=
      match t1, t2 with
      | Gtyp (Fuint w1), Gtyp (Fuint w2) => Some (Gtyp (Fuint (maxn w1 w2)))
      | Gtyp (Fsint w1), Gtyp (Fsint w2) => Some (Gtyp (Fsint (maxn w1 w2)))
      | Gtyp Fclock, Gtyp Fclock => Some (Gtyp Fclock)
      | Gtyp Freset, Gtyp Freset => Some (Gtyp Freset)
      | Gtyp Fasyncreset, Gtyp Fasyncreset => Some (Gtyp Fasyncreset)
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

Fixpoint base_ref_fields (base : VarOrder.t * N) (v : VarOrder.t) (ff : ffield) : option (VarOrder.t * N * ftype) :=
(* find field v in ff. If found, return its type as an auxiliary to base_ref. *)
match ff with
| Fnil => None
| Fflips v' _ t' ff' =>
    if v == v' then Some (base, t')
               else base_ref_fields (base.1, (base.2 + tmap_type_size t')%num) v ff'
end.

Fixpoint base_ref (ref : HiFP.href) (tmap : CEP.t ftype) : option (VarOrder.t * N * ftype) :=
(* For reference ref, finds the pair (v, n) and the type that corresponds to it.
(v,n) is the first item in the list of variables associated to ref that is affected by it.
This function counts n for tmap, i.e. all arrays are treated as having only one element. *)
match ref with
| Eid v =>
    match CEP.find v tmap with
    | Some t => Some (v, t)
    | None   => None
    end
| Esubfield ref' v' =>
    match base_ref ref' tmap with
    | Some (base, Btyp ff) => base_ref_fields base v' ff
    | _ => None
    end
| Esubindex ref' _
| Esubaccess ref' _ =>
    match base_ref ref' tmap with
    | Some (base, Atyp t' _) => Some (base, t')
    | _ => None
    end
end.

Fixpoint type_of_hfexpr (e : HiFP.hfexpr) (ce : CEP.t ftype) : option ftype :=
(* calculates the type of the expression e.
   In contrast to HiFP.type_of_hfexpr, this function only needs the map of types,
   and it will preserve the information whether some ground type has an implicit width
   (I am not sure yet whether that information needs to be preserved at all.)
   Should the width of variables be preserved faithfully? Not sure at this moment;
   perhaps we need two versions. *)
match e with
| Econst t _ => Some (Gtyp t)
| Eref r => match base_ref r ce with
            | Some (_, ft) => Some ft
            | None => None
            end
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
| Ecast AsAsync e1 => match type_of_hfexpr e1 ce  with
                      | Some (Gtyp _) => Some (Gtyp Fasyncreset)
                      | _ => None
                      end
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
                  | Some (Gtyp (Fuint 1)), Some t1, Some t2
                  | Some (Gtyp (Fuint_implicit 1)), Some t1, Some t2 =>
                      mux_types t1 t2
                  | _, _, _ => None
                  end
| Evalidif c e1 => match type_of_hfexpr c ce with
                   | Some (Gtyp (Fuint 1)) | Some (Gtyp (Fuint_implicit 1)) => type_of_hfexpr e1 ce
                   | _ => None
                   end
end.

Fixpoint tmap_add_bidir_connect (m_nt_ns : var2exprsmap * N * N) (v_tgt : VarOrder.t) (ref_tgt : HiFP.href) (t_tgt : ftype) (v_src : VarOrder.t) (ref_src : HiFP.href) (t_src : ftype) : option (var2exprsmap * N * N) :=
(* check whether types are compatible and add connections for all ground-type entries of ref_tgt <= ref_src,
   while taking into account flipped fields.
   This works for InferWidths, so for arrays it only adds one connection, not one connection per entry.
   m_n is a pair: a var2exprsmap to which connections are added
                  a natural number that indicates which index of ref_tgt and ref_src is to be connected
   v_tgt and v_src are variable names.
   ref_tgt and ref_src are the respective hrefs that correspond to (v_tgt, m_nt_ns.1.2) and (v_src, m_nt_ns.2).
   The return value is a triple where the first element is the updated var2exprsmap and
   the second and third is increased by as many connections as there have been added. *)
match t_tgt, t_src with
| Gtyp (Fuint _), Gtyp (Fuint _) | Gtyp (Fuint _), Gtyp (Fuint_implicit _)
| Gtyp (Fsint _), Gtyp (Fsint _) | Gtyp (Fsint _), Gtyp (Fsint_implicit _)
| Gtyp Fclock, Gtyp Fclock
| Gtyp Freset, Gtyp Freset
| Gtyp Fasyncreset, Gtyp Fasyncreset =>
    (* the target has explicit width, do not register the connection *)
    Some (m_nt_ns.1.1, (m_nt_ns.1.2 + 1)%num, (m_nt_ns.2 + 1)%num)
| Gtyp (Fuint_implicit _), Gtyp (Fuint _) | Gtyp (Fuint_implicit _), Gtyp (Fuint_implicit _)
| Gtyp (Fsint_implicit _), Gtyp (Fsint _) | Gtyp (Fsint_implicit _), Gtyp (Fsint_implicit _) =>
    Some (match module_graph_vertex_set_p.find (v_tgt, m_nt_ns.1.2) m_nt_ns.1.1 with
          | Some expr_list => module_graph_vertex_set_p.add (v_tgt, m_nt_ns.1.2)    (Eref ref_src :: expr_list) m_nt_ns.1.1
          | None =>           module_graph_vertex_set_p.add (v_tgt, m_nt_ns.1.2) [:: Eref ref_src]              m_nt_ns.1.1
          end, (m_nt_ns.1.2 + 1)%num, (m_nt_ns.2 + 1)%num)
| Atyp t_tgt' n_tgt, Atyp t_src' n_src =>
    if n_tgt != n_src then None
    else tmap_add_bidir_connect m_nt_ns v_tgt (Esubindex ref_tgt 0) t_tgt' v_src (Esubindex ref_src 0) t_src'
| Btyp ff_tgt, Btyp ff_src => tmap_add_bidir_connect_fields m_nt_ns v_tgt ref_tgt ff_tgt v_src ref_src ff_src
| _, _ => None
end
with tmap_add_bidir_connect_fields (m_nt_ns : var2exprsmap * N * N) (v_tgt : VarOrder.t) (ref_tgt : HiFP.href) (ff_tgt : ffield) (v_src : VarOrder.t) (ref_src : HiFP.href) (ff_src : ffield) : option (var2exprsmap * N * N) :=
(* check whether types are compatible and add connections for all ground-type entries of ref_tgt <= ref_src,
   where these are bundle types with types (Btyp ff_tgt) and (Btyp ff_src), respectively. *)
match ff_tgt, ff_src with
| Fnil, Fnil => Some m_nt_ns
| Fflips v_tgt Nflip t_tgt ff_tgt', Fflips v_src Nflip t_src ff_src' =>
    if v_tgt != v_src then None
    else if tmap_add_bidir_connect m_nt_ns v_tgt (Esubfield ref_tgt v_tgt) t_tgt v_src (Esubfield ref_src v_src) t_src is Some m_nt_ns'
         then tmap_add_bidir_connect_fields m_nt_ns' v_tgt ref_tgt ff_tgt' v_src ref_src ff_src'
         else None
| Fflips v_tgt Flipped t_tgt ff_tgt', Fflips v_src Flipped t_src ff_src' =>
    if v_tgt != v_src then None
    else if tmap_add_bidir_connect_flipped m_nt_ns v_tgt (Esubfield ref_tgt v_tgt) t_tgt v_src (Esubfield ref_src v_src) t_src is Some m_nt_ns'
         then tmap_add_bidir_connect_fields m_nt_ns' v_tgt ref_tgt ff_tgt' v_src ref_src ff_src'
         else None
| _, _ => None
end
with tmap_add_bidir_connect_flipped (m_nt_ns : var2exprsmap * N * N) (v_tgt : VarOrder.t) (ref_tgt : HiFP.href) (t_tgt : ftype) (v_src : VarOrder.t) (ref_src : HiFP.href) (t_src : ftype) : option (var2exprsmap * N * N) :=
(* check whether types are compatible and add connections for all ground-type entries of ref_src <= ref_tgt,
   i.e. the other direction than tmap_add_bidir_connect. *)
match t_tgt, t_src with
| Gtyp (Fuint _), Gtyp (Fuint _) | Gtyp (Fuint_implicit _), Gtyp (Fuint _)
| Gtyp (Fsint _), Gtyp (Fsint _) | Gtyp (Fsint_implicit _), Gtyp (Fsint _)
| Gtyp Fclock, Gtyp Fclock
| Gtyp Freset, Gtyp Freset
| Gtyp Fasyncreset, Gtyp Fasyncreset =>
    (* the target has explicit width, do not register the connection *)
    Some (m_nt_ns.1.1, (m_nt_ns.1.2 + 1)%num, (m_nt_ns.2 + 1)%num)
| Gtyp (Fuint _), Gtyp (Fuint_implicit _) | Gtyp (Fuint_implicit _), Gtyp (Fuint_implicit _)
| Gtyp (Fsint _), Gtyp (Fsint_implicit _) | Gtyp (Fsint_implicit _), Gtyp (Fsint_implicit _) =>
    Some (match module_graph_vertex_set_p.find (v_src, m_nt_ns.2) m_nt_ns.1.1 with
          | Some expr_list => module_graph_vertex_set_p.add (v_src, m_nt_ns.2)    (Eref ref_tgt :: expr_list) m_nt_ns.1.1
          | None =>           module_graph_vertex_set_p.add (v_src, m_nt_ns.2) [:: Eref ref_tgt]              m_nt_ns.1.1
          end, (m_nt_ns.1.2 + 1)%num, (m_nt_ns.2 + 1)%num)
| Atyp t_tgt' n_tgt, Atyp t_src' n_src =>
    if n_tgt != n_src then None
    else tmap_add_bidir_connect_flipped m_nt_ns v_tgt (Esubindex ref_tgt 0) t_tgt' v_src (Esubindex ref_src 0) t_src'
| Btyp ff_tgt, Btyp ff_src => tmap_add_bidir_connect_flipped_fields m_nt_ns v_tgt ref_tgt ff_tgt v_src ref_src ff_src
| _, _ => None
end
with tmap_add_bidir_connect_flipped_fields (m_nt_ns : var2exprsmap * N * N) (v_tgt : VarOrder.t) (ref_tgt : HiFP.href) (ff_tgt : ffield) (v_src : VarOrder.t) (ref_src : HiFP.href) (ff_src : ffield) : option (var2exprsmap * N * N) :=
(* check whether types are compatible and add connections for all ground-type entries of ref_src <= ref_tgt,
   where these are bundle types with types (Btyp ff_src) and (Btyp ff_tgt), respectively,
   i.e. the other direction than tmap_add_bidir_connect_fields. *)
match ff_tgt, ff_src with
| Fnil, Fnil => Some m_nt_ns
| Fflips v_tgt Nflip t_tgt ff_tgt', Fflips v_src Nflip t_src ff_src' =>
    if v_tgt != v_src then None
    else if tmap_add_bidir_connect_flipped m_nt_ns v_tgt (Esubfield ref_tgt v_tgt) t_tgt v_src (Esubfield ref_src v_src) t_src is Some m_nt_ns'
         then tmap_add_bidir_connect_flipped_fields m_nt_ns' v_tgt ref_tgt ff_tgt' v_src ref_src ff_src'
         else None
| Fflips v_tgt Flipped t_tgt ff_tgt', Fflips v_src Flipped t_src ff_src' =>
    if v_tgt != v_src then None
    else if tmap_add_bidir_connect m_nt_ns v_tgt (Esubfield ref_tgt v_tgt) t_tgt v_src (Esubfield ref_src v_src) t_src is Some m_nt_ns'
         then tmap_add_bidir_connect_flipped_fields m_nt_ns' v_tgt ref_tgt ff_tgt' v_src ref_src ff_src'
         else None
| _, _ => None
end.

Fixpoint tmap_add_passive_connect (m_nt : var2exprsmap * N) (v_tgt : VarOrder.t) (ref_src : HiFP.href) (t : ftype) : option (var2exprsmap * N) :=
(* passive version of tmap_add_bidir_connect.
   This works for InferWidths, so for arrays it only adds one connection, not one connection per entry.
   m_nt is a pair: a var2exprsmap to which connections are added
                  a natural number that indicates which index of ref_tgt and ref_src is to be connected
   v_tgt is the variable name.
   ref_src is the href that v_tgt is connected to.
   The return value is a pair where the first element is the updated var2exprsmap and
   the second element is increased by as many connections as there have been added. *)
match t with
| Gtyp (Fuint_implicit _)
| Gtyp (Fsint_implicit _) =>
    match module_graph_vertex_set_p.find (v_tgt, m_nt.2) m_nt.1 with
    | Some expr_list => Some (module_graph_vertex_set_p.add (v_tgt, m_nt.2)    (Eref ref_src :: expr_list) m_nt.1, (m_nt.2 + 1)%num)
    | None =>           Some (module_graph_vertex_set_p.add (v_tgt, m_nt.2) [:: Eref ref_src]              m_nt.1, (m_nt.2 + 1)%num)
    end
| Gtyp _ => Some (m_nt.1, (m_nt.2 + 1)%num)
| Atyp t' _ => tmap_add_passive_connect m_nt v_tgt (Esubindex ref_src 0) t'
| Btyp ff => tmap_add_passive_connect_fields m_nt v_tgt ref_src ff
end
with tmap_add_passive_connect_fields (m_nt : var2exprsmap * N) (v_tgt : VarOrder.t) (ref_src : HiFP.href) (ff : ffield) : option (var2exprsmap * N) :=
match ff with
| Fnil => Some m_nt
| Fflips v Nflip   t ff' =>
    match tmap_add_passive_connect m_nt v_tgt (Esubfield ref_src v) t with
    | Some m_nt' => tmap_add_passive_connect_fields m_nt' v_tgt ref_src ff'
    | None => None
    end
| Fflips v Flipped t ff' => None
end.

Fixpoint split_expr (ref_src : HiFP.href) (t : ftype) : option (seq HiFP.href) :=
  match t with
  | Gtyp _ => Some [:: ref_src]
  | Atyp atyp _ => split_expr (Esubindex ref_src 0) atyp
  | Btyp ff => split_expr_f ref_src ff 
  end
with split_expr_f (ref_src : HiFP.href) (ff : ffield) : option (seq HiFP.href) :=
  match ff with
  | Fnil => Some nil
  | Fflips v Nflip t ff' =>
    match split_expr_f ref_src ff', split_expr (Esubfield ref_src v) t with
    | Some ls, Some ls' => Some (ls' ++ ls)
    | _,_ => None
    end
  | Fflips v Flipped t ff' => None
  end.

Fixpoint split_expr_non_passive (ref_src : HiFP.href) (t : ftype) (fl : bool) : option (seq (HiFP.href * bool)) :=
  match t with
  | Gtyp _ => Some [:: (ref_src, fl)]
  | Atyp atyp _ => split_expr_non_passive (Esubindex ref_src 0) atyp fl
  | Btyp ff => split_expr_non_passive_f ref_src ff fl
  end
with split_expr_non_passive_f (ref_src : HiFP.href) (ff : ffield) (fl : bool) : option (seq (HiFP.href * bool)) :=
  match ff with
  | Fnil => Some nil
  | Fflips v Nflip t ff' =>
    match split_expr_non_passive_f ref_src ff' fl, split_expr_non_passive (Esubfield ref_src v) t fl with
    | Some ls, Some ls' => Some (ls' ++ ls)
    | _,_ => None
    end
  | Fflips v Flipped t ff' => 
    match split_expr_non_passive_f ref_src ff' (~~fl), split_expr_non_passive (Esubfield ref_src v) t (~~fl) with
    | Some ls, Some ls' => Some (ls' ++ ls)
    | _,_ => None
    end
  end.

Fixpoint tmap_add_expr_connect (m_nt : var2exprsmap * N) (v_tgt : VarOrder.t) (expr_src : HiFP.hfexpr) (t : ftype) : option var2exprsmap :=
(* add connections for all ground-type entries of ref_tgt <= expr_src.
   This works for InferWidths, so for arrays it only adds one connection, not one connection per entry.
   m_n is a pair: a var2exprsmap to which connections are added
                  a natural number that indicates which index of ref_tgt is to be connected
   v_tgt is the base variable name.
   ref_tgt is the href that corresponds to (v_tgt, m_nt.2).
   The return value is the updated var2exprsmap. *)
match t, expr_src with
| Gtyp (Fuint_implicit _), expr
| Gtyp (Fsint_implicit _), expr =>
    match module_graph_vertex_set_p.find (v_tgt, m_nt.2) m_nt.1 with
    | Some expr_list => Some (module_graph_vertex_set_p.add (v_tgt, m_nt.2)    (expr_src :: expr_list) m_nt.1)
    | None =>           Some (module_graph_vertex_set_p.add (v_tgt, m_nt.2) [:: expr_src]              m_nt.1)
    end
| Gtyp _, _ => Some m_nt.1
(* In Emux and Evalidif (below) the condition is not important for width inference. So ignore it. *)
| t, Emux _ e1 e2 =>
    match tmap_add_expr_connect m_nt v_tgt e1 t with
    | Some m' => tmap_add_expr_connect (m', m_nt.2) v_tgt e2 t
    | None => None
    end
| t, Evalidif _ e => tmap_add_expr_connect m_nt v_tgt e t
| t, Eref ref =>
    match tmap_add_passive_connect m_nt v_tgt ref t with
    | Some (m', _) => Some m'
    | None => None
    end
| _, _ => None
end.

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
  | Eref ref => match split_expr ref t with
                | Some refl => Some (map (fun tref => (Eref tref)) refl)
                | None => None
                end
  | Emux c e1 e2 => match split_expr_connect e1 t, split_expr_connect e2 t with
                  | Some el1, Some el2 => combine_mux_expr c el1 el2
                  | _ ,_ => None
                  end
  | _ => Some [:: expr_src] 
  end.

Definition connect_fgtyp_compatible (t_tgt t_src : fgtyp) : bool :=
  if (not_implicit t_tgt) then true
  else (sizeof_fgtyp t_tgt >= sizeof_fgtyp t_src) && fgtyp_equiv t_tgt t_src.

Fixpoint check_connect_fgtyp_compatible (t_tgt t_src : ftype) (n : nat) : bool :=
  match n with
  | 0 => true
  | S m => match ft_find_sub t_tgt (N.of_nat m), ft_find_sub t_src (N.of_nat m) with
          | Some gt_tgt, Some gt_src => connect_fgtyp_compatible gt_tgt gt_src && check_connect_fgtyp_compatible t_tgt t_src m
          | _,_ => false
          end
  end.

Fixpoint check_connect_non_passive_fgtyp (t_tgt t_src : ftype) (n : nat) : bool :=
  match n with
  | 0 => true
  | S m => match ft_check_flip t_tgt (N.of_nat m) false, ft_find_sub t_tgt (N.of_nat m), ft_find_sub t_src (N.of_nat m) with
          | Some false, Some gt_tgt, Some gt_src => connect_fgtyp_compatible gt_tgt gt_src && check_connect_non_passive_fgtyp t_tgt t_src m
          | Some true, Some gt_tgt, Some gt_src => connect_fgtyp_compatible gt_src gt_tgt && check_connect_non_passive_fgtyp t_tgt t_src m
          | _,_,_ => false
          end
  end.

Definition connect_non_passive_type (t_tgt : ftype) (t_src : ftype) : Prop :=
  ftype_equiv t_tgt t_src && check_connect_non_passive_fgtyp t_tgt t_src (tmap_type_size t_tgt).

Definition connect_type_compatible (t_tgt t_src : ftype) : bool :=
  ftype_equiv t_tgt t_src && check_connect_fgtyp_compatible t_tgt t_src (tmap_type_size t_tgt).

(*match list_gtyp t_tgt, list_gtyp t_src with
  | nil, nil => true
  | hd1 :: tl1, 
match t_tgt, t_src with
| Gtyp (Fuint _), Gtyp (Fuint _)
| Gtyp (Fuint _), Gtyp (Fuint_implicit _)
| Gtyp (Fuint_implicit _), Gtyp (Fuint _)
| Gtyp (Fuint_implicit _), Gtyp (Fuint_implicit _)
| Gtyp (Fsint _), Gtyp (Fsint _)
| Gtyp (Fsint _), Gtyp (Fsint_implicit _)
| Gtyp (Fsint_implicit _), Gtyp (Fsint _)
| Gtyp (Fsint_implicit _), Gtyp (Fsint_implicit _)
| Gtyp Fclock, Gtyp Fclock
| Gtyp Freset, Gtyp Freset
| Gtyp Fasyncreset, Gtyp Fasyncreset => true
| Atyp t_tgt' n_tgt, Atyp t_src' n_src => (n_tgt == n_src) && connect_type_compatible t_tgt' t_src'
| Btyp ff_tgt, Btyp ff_src => connect_type_compatible_fields ff_tgt ff_src
| _, _ => false
end
with connect_type_compatible_fields (ff_tgt ff_src : ffield) : bool :=
match ff_tgt, ff_src with
| Fnil, Fnil => true
| Fflips v_tgt f_tgt t_tgt ff_tgt', Fflips v_src f_src t_src ff_src' =>
    (v_tgt == v_src) && (fflip_eqn f_tgt f_src) && connect_type_compatible t_tgt t_src && connect_type_compatible_fields ff_tgt' ff_src'
| _, _ => false
end. (* should be none flip *)
*)

Fixpoint add_expr_connect (v : ProdVarOrder.t) (el : seq HiFP.hfexpr) (var2exprs : var2exprsmap) : var2exprsmap :=
  match el with
  | nil => var2exprs
  | hd :: tl => match module_graph_vertex_set_p.find v var2exprs with
                | Some ls => add_expr_connect (v.1, N.add v.2 1%num) tl (module_graph_vertex_set_p.add v (hd :: ls) var2exprs)
                | None => add_expr_connect (v.1, N.add v.2 1%num) tl (module_graph_vertex_set_p.add v [::hd] var2exprs)
                end
  end.

Fixpoint add_expr_connect_non_passive (v_lhs v_rhs : ProdVarOrder.t) (el1 el2 : seq (HiFP.href * bool)) (var2exprs : var2exprsmap) : option var2exprsmap :=
  match el1, el2 with
  | nil, nil => Some var2exprs
  | (ref1, false) :: tl1, (ref2, false) :: tl2 => 
                match module_graph_vertex_set_p.find v_lhs var2exprs with
                | Some ls => add_expr_connect_non_passive (v_lhs.1, N.add v_lhs.2 1%num) (v_rhs.1, N.add v_rhs.2 1%num) tl1 tl2 (module_graph_vertex_set_p.add v_lhs ((Eref ref1) :: ls) var2exprs)
                | None => add_expr_connect_non_passive (v_lhs.1, N.add v_lhs.2 1%num) (v_rhs.1, N.add v_rhs.2 1%num) tl1 tl2 (module_graph_vertex_set_p.add v_lhs [::(Eref ref1)] var2exprs)
                end
  | (ref1, true) :: tl1, (ref2, true) :: tl2 => 
                match module_graph_vertex_set_p.find v_rhs var2exprs with
                | Some ls => add_expr_connect_non_passive (v_lhs.1, N.add v_lhs.2 1%num) (v_rhs.1, N.add v_rhs.2 1%num) tl1 tl2 (module_graph_vertex_set_p.add v_rhs ((Eref ref2) :: ls) var2exprs)
                | None => add_expr_connect_non_passive (v_lhs.1, N.add v_lhs.2 1%num) (v_rhs.1, N.add v_rhs.2 1%num) tl1 tl2 (module_graph_vertex_set_p.add v_rhs [::(Eref ref2)] var2exprs)
                end
  | _, _ => None
  end.

Fixpoint stmt_tmap (t_v : CEP.t ftype * var2exprsmap) (s: HiFP.hfstmt) : option (CEP.t ftype * var2exprsmap) :=
(* t_v is a pair: tmap of components defined before statement s;
                  map that indicates all expressions assigned to a certain ground-type part of a component.
   s is a statement.
   the result is the pair t_v expanded with the information from s *)
match s with
| Sskip => Some t_v
| Swire v t => if CEP.find v t_v.1 is None
               then Some (CEP.add v t t_v.1, t_v.2)
               else None
| Sreg v r => match CEP.find v t_v.1, reset r with
              | Some _, _ => None
              | None, Rst _ rst_val => match split_expr_connect rst_val (type r) with
                                      | Some rstl => Some (CEP.add v (type r) t_v.1, add_expr_connect v rstl t_v.2)
                                      | None => None
                                      end
              | None, NRst => Some (CEP.add v (type r) t_v.1, t_v.2)
              end
| Smem v m => (* TBD *) None
| Sinst v inst => (* TBD *) None
| Snode v e =>
    match CEP.find v t_v.1, type_of_hfexpr e t_v.1 with
    | None, Some t => match split_expr_connect e t with
                    | Some rstl => Some (CEP.add v t t_v.1, add_expr_connect v rstl t_v.2)
                    | None => None
                    end
    | _, _ => None
    end
| Sfcnct ref_tgt (Eref ref_src) =>
    match base_ref ref_tgt t_v.1, base_ref ref_src t_v.1 with
    | Some (v_tgt, t_tgt), Some (v_src, t_src) =>
      match split_expr_non_passive ref_tgt t_tgt false, split_expr_non_passive ref_src t_src false with
      | Some lhsl, Some rhsl => match add_expr_connect_non_passive v_tgt v_src lhsl rhsl t_v.2 with
                                | Some newv2e => Some (t_v.1, newv2e)
                                | None => None
                                end
      | _, _ => None
      end
    | _, _ => None
    end
| Sfcnct ref_tgt expr_src =>
    match base_ref ref_tgt t_v.1, type_of_hfexpr expr_src t_v.1 with
    | Some (v, t_tgt), Some t_src =>
        if connect_type_compatible t_tgt t_src
          then match split_expr_connect expr_src t_src with
          | Some rstl => Some (t_v.1, add_expr_connect v rstl t_v.2)
          | None => None
          end
        else None
    | _,_ => None
    end
| Sinvalid _ => Some t_v
| Swhen c ss_t ss_f =>
    match stmts_tmap t_v ss_t with
    | Some t_v' => stmts_tmap t_v' ss_f
    | None => None
    end
end
with stmts_tmap (t_v : CEP.t ftype * var2exprsmap) (ss: HiFP.hfstmt_seq) : option (CEP.t ftype * var2exprsmap) :=
match ss with
| Qnil => Some t_v
| Qcons s ss' =>
    match stmt_tmap t_v s with
    | Some t_v' => stmts_tmap t_v' ss'
    | None => None
    end
end.

(* Correctness theorem for stmts_tmap:
- All of the below holds if the output is Some (tmap, var2exprsmap).
  - The tmap contains exactly the entries for all components that appear in the statement sequence
    (in addition to the input parameter). [“contains at least” is needed for correctness; “contains
    at most” is only needed to show minimality.]
  - The var2exprsmap contains all connections to implicit-width components declared in the statement sequence.
  * The var2exprsmap does not contain any connection that is not present in the statement sequence
    (if the input parameter var2exprsmap is the empty map).
    [This is only needed to show minimality.] *)

Fixpoint stmt_tmap_is_correct (t_in : CEP.t ftype) (v2e_in : var2exprsmap) (s : HiFP.hfstmt) (t_out: CEP.t ftype) (v2e_out: var2exprsmap) : Prop :=
   match s with
   | Swire v t => CEP.find v t_in = None ->
                        CEP.find v t_out = Some t
                     /\ (forall v' : ProdVarOrder.t, v != v' -> CEP.find v' t_in = CEP.find v' t_out)
                     /\ module_graph_vertex_set_p.Equal v2e_in v2e_out
   | Sreg v r => CEP.find v t_in = None ->
                       CEP.find v t_out = Some (type r)
                    /\ (forall v' : ProdVarOrder.t, v != v' -> CEP.find v' t_in = CEP.find v' t_out)
                    /\ (reset r = NRst ProdVarOrder.T -> module_graph_vertex_set_p.Equal v2e_in v2e_out)
   | Snode v e => CEP.find v t_in = None ->
                  (type_of_hfexpr e t_in != None) ->
                       CEP.find v t_out = type_of_hfexpr e t_in
                    /\ (forall v' : ProdVarOrder.t, v != v' -> CEP.find v' t_in = CEP.find v' t_out)
                    /\ (module_graph_vertex_set_p.Equal v2e_in v2e_out)
   | Sfcnct v e =>    CEP.Equal t_in t_out
                   /\ (* forall t : ftype, CEP.find v t_in = Some t -> the connection is in v2e*) True
   | Swhen c ss_t ss_f => exists (t_internal : CEP.t ftype) (v2e_internal : var2exprsmap),
                                stmts_tmap_is_correct t_in v2e_in ss_t t_internal v2e_internal
                             /\ stmts_tmap_is_correct t_internal v2e_internal ss_f t_out v2e_out
   | _ =>    CEP.Equal t_in t_out
          /\ module_graph_vertex_set_p.Equal v2e_in v2e_out
   end
with stmts_tmap_is_correct (t_in : CEP.t ftype) (v2e_in : var2exprsmap) (ss : HiFP.hfstmt_seq) (t_out: CEP.t ftype) (v2e_out: var2exprsmap) : Prop :=
   match ss with
   | Qnil => CEP.Equal t_in t_out /\ module_graph_vertex_set_p.Equal v2e_in v2e_out
   | Qcons s ss' => exists (t_internal : CEP.t ftype) (v2e_internal : var2exprsmap),
                          stmt_tmap_is_correct t_in v2e_in s t_internal v2e_internal
                       /\ stmts_tmap_is_correct t_internal v2e_internal ss' t_out v2e_out
   end.

Theorem stmts_tmap_correct :
   forall (ss : HiFP.hfstmt_seq) (t_in : CEP.t ftype) (v2e_in: var2exprsmap) (t_out: CEP.t ftype) (v2e_out: var2exprsmap),
      stmts_tmap (t_in, v2e_in) ss = Some (t_out, v2e_out) ->
         stmts_tmap_is_correct t_in v2e_in ss t_out v2e_out.
Proof.
induction ss as [|s ss'].
* intros.
  simpl stmts_tmap_is_correct.
  simpl stmts_tmap in H.
  injection H ; intros.
  split.
  + unfold CEP.Equal ; intro ; rewrite H1 ; reflexivity.
  + unfold module_graph_vertex_set_p.Equal ; intro ; rewrite H0 ; reflexivity.
* intros.
  simpl stmts_tmap_is_correct.
  simpl stmts_tmap in H.
  destruct (stmt_tmap (t_in, v2e_in) s) eqn: H0.
  + destruct p as [t_internal v2e_internal].
    exists t_internal, v2e_internal.
    split.
    - destruct s.
      * (* Sskip *)
        simpl stmt_tmap_is_correct.
        simpl stmt_tmap in H0.
        injection H0 ; intros.
        split.
        + intro ; rewrite H2 ; reflexivity.
        + unfold module_graph_vertex_set_p.Equal ; intro ; rewrite H1 ; reflexivity.
      * (* Swire *)
        simpl stmt_tmap_is_correct.
        simpl stmt_tmap in H0.
        intro.
        rewrite H1 in H0.
        injection H0 ; intros.
        split.
        + rewrite -H3 CEP.Lemmas.find_add_eq // /HiFirrtl.PVM.SE.eq eq_refl //.
        split.
        + intros.
          apply negbTE in H4.
          rewrite -H3 CEP.Lemmas.find_add_neq // /HiFirrtl.PVM.SE.eq eq_sym H4 //.
        + unfold module_graph_vertex_set_p.Equal ; intro ; rewrite H2 ; reflexivity.
      * (* Sreg *)
        simpl stmt_tmap_is_correct.
        simpl stmt_tmap in H0.
        intro.
        rewrite H1 in H0.
        destruct (reset h).
        + injection H0 ; intros.
          split.
          - rewrite -H3 CEP.Lemmas.find_add_eq // /HiFirrtl.PVM.SE.eq eq_refl //.
          split.
          - intros.
            apply negbTE in H4.
            rewrite -H3 CEP.Lemmas.find_add_neq // /HiFirrtl.PVM.SE.eq eq_sym H4 //.
          - unfold module_graph_vertex_set_p.Equal ; intro ; rewrite H2 ; reflexivity.
        + destruct (tmap_add_expr_connect (v2e_in, s.2) s.1 h1 (type h)) eqn: Htmap ; rewrite Htmap in H0 ; try done.
          injection H0 ; intros.
          split.
          - rewrite -H3 CEP.Lemmas.find_add_eq // /HiFirrtl.PVM.SE.eq eq_refl //.
          - split ; try done.
            intros.
            apply negbTE in H4.
            rewrite -H3 CEP.Lemmas.find_add_neq // /HiFirrtl.PVM.SE.eq eq_sym H4 //.
      * (* Smem has not yet been implemented *)
        unfold stmt_tmap in H0 ; done.
      * (* Sinst has not yet been implemented *)
        unfold stmt_tmap in H0 ; done.
      * (* Snode *)
        simpl stmt_tmap_is_correct.
        simpl stmt_tmap in H0.
        destruct (CEP.find s t_in) eqn: H1 ; try done.
        destruct (type_of_hfexpr h t_in) eqn: H2 ; try done.
        destruct (tmap_add_expr_connect (v2e_in, s.2) s.1 h f) eqn: H3 ; try done ; rewrite H3 in H0.
        injection H0 ; intros.
        split.
        + intro.

    - apply IHss ; exact H.
  + discriminate H.
Admitted.

(* return a fgtyp with the larger width for gtyp *)
Definition max_fgtyp (ft1 : fgtyp) (ft2 : fgtyp) : option fgtyp :=
  match ft1, ft2 with
  | Fuint w1, Fuint_implicit w2 => Some (Fuint_implicit (max w1 w2))
  | Fsint w1, Fsint_implicit w2 => Some (Fsint_implicit (max w1 w2))
  | Fuint_implicit w1, Fuint_implicit w2 => Some (Fuint_implicit (max w1 w2))
  | Fsint_implicit w1, Fsint_implicit w2 => Some (Fsint_implicit (max w1 w2))
  | _,_ => None
  end.
  
Fixpoint expr2varlist (expr : HiFP.hfexpr) (tmap : CEP.t ftype) : option (seq ProdVarOrder.t) :=
   (* Prepends to ls the list of variable/component identifiers accessed by the expression expr.
      tmap is used to look up the identifiers.
      DNJ: I think parameter ls is superfluous, it seems to be never used.  It could be replaced by [::]. *)
   match expr with
   | Econst _ _ => Some nil
   | Eref ref => match base_ref ref tmap with
                | Some (pv,_) => Some [:: pv]
                | None => None
                end
  | Eprim_unop _ e1 => expr2varlist e1 tmap
  | Eprim_binop _ e1 e2 => match expr2varlist e1 tmap, expr2varlist e2 tmap with
                          | Some ls', Some ls'' => Some (ls' ++ ls'')
                          | _,_ => None
                          end
  | Emux e1 e2 e3 => match expr2varlist e1 tmap, expr2varlist e2 tmap, expr2varlist e3 tmap with
                    | Some ls', Some ls'', Some ls''' => Some (ls' ++ ls'' ++ ls''')
                    | _,_,_ => None
                    end
  | Evalidif e1 e2 => match expr2varlist e1 tmap, expr2varlist e2 tmap with
                      | Some ls', Some ls'' => Some (ls' ++ ls'')
                      | _,_ => None
                      end
  | Ecast _ e => expr2varlist e tmap
   end.

Definition updg (key : ProdVarOrder.t) (v : seq ProdVarOrder.t) (map : ProdVarOrder.t -> seq ProdVarOrder.t) : ProdVarOrder.t -> seq ProdVarOrder.t :=
    fun (y : ProdVarOrder.t) => if y == key then v else map y.

Fixpoint drawel (v : ProdVarOrder.t) (el : seq HiFP.hfexpr) (tmap : CEP.t ftype) (newg : ProdVarOrder.t -> seq ProdVarOrder.t) (vertices : seq ProdVarOrder.t) : option ((ProdVarOrder.t -> seq ProdVarOrder.t) * (seq ProdVarOrder.t)) :=
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
   | e :: etl => let vl := expr2varlist e tmap in
                 match vl with (* all elements appearing in e *)
                 | Some ls => let g' := List.fold_left (fun tempg tempv => updg tempv (cons v (tempg tempv)) tempg) ls newg in
                              drawel v etl tmap g' (vertices ++ ls)
                 | None => None
                 end
   end.

Fixpoint drawg depandencyls (tmap : CEP.t ftype) (expli_reg : seq ProdVarOrder.t) (newg : ProdVarOrder.t -> seq ProdVarOrder.t) (vertices : seq ProdVarOrder.t) : option ((ProdVarOrder.t -> seq ProdVarOrder.t) * (seq ProdVarOrder.t)) :=
   (* construct the dependency graph:
      depandencyls: list of pairs (vertex in the module graph, list of expressions)
      tmap: map of (known) types of components
      expli_reg: list of completely explicit-width components; they can be ignored
      newg: current edges in the dependency graph (will be extended by drawel)
      vertices: current vertices in the dependency graph (will be extended by drawel)
      Return value: a pair (edges in the dependency graph, vertices in the dependency graph)
      *)
   match depandencyls with
   (* list of all pairs (element as key, its connections as value) *)
   | nil => Some (newg, vertices)
  | (v, el) :: vtl => if ((fst v, N0) \in expli_reg) then drawg vtl tmap expli_reg newg vertices
                      else match drawel v el tmap newg vertices with (* for a certain element v, draw dependencies in the el to newg *)
                      | Some (g', vertices') => drawg vtl tmap expli_reg g' vertices'
                      | None => None
                      end
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
                | Some init => match ft_find_sub init v.2 with
                                | Some initt => if not_implicit initt then Some tmap
                                                       else match max_ftlist eftl initt with
                                                        | Some nt => match ft_set_sub init nt v.2 with
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
  
Fixpoint InferWidths_fun (od : seq ProdVarOrder.t) (var2exprs : var2exprsmap) (tmap : CEP.t ftype) : option (CEP.t ftype) :=
(* od contains the (implicit-width) ground-type subcomponents in topological order.
   (It is ok if od contains other components, but it is not necessary.)
   var2exprs is a map that maps every ground-type subcomponent to a list of expressions (namely expressions that the (sub)component is connected from).
   tmap is the map of types for every component that has been defined (but there are no separate entries for subcomponents);
   the result is a modified tmap, which ensures that the width of every implicit-width component is large enough. *)
  match od with
  | nil => Some tmap
  | vhd :: vtl => match module_graph_vertex_set_p.find vhd var2exprs with 
                  | Some el => match InferWidth_fun vhd el tmap with
                          | Some tm => InferWidths_fun vtl var2exprs tm
                          | None => None
                          end
                  | None => None
                  end
  end.

Fixpoint list_expligref (n : nat) (pv : ProdVarOrder.t) (checkt : ftype) : option (seq ProdVarOrder.t) := 
  match n with
  | 0 => Some nil
  | S m => match list_expligref m pv checkt, ft_find_sub checkt (N.of_nat m) with
          | Some ls, Some gt => if not_implicit gt then Some ls
                                else Some ((fst pv, N.add (snd pv) (N.of_nat m)) :: ls)
          | _, _ => None
          end
  end.

Fixpoint explireg_stmt (st : HiFP.hfstmt) : option (seq ProdVarOrder.t) :=
  match st with
  | Sskip => Some nil 
  | Swire v t => Some nil
  | Sreg v r => let len := tmap_type_size (type r) in 
                list_expligref len v (type r)
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
  end.

Definition emptyg : (ProdVarOrder.t -> seq ProdVarOrder.t) := (fun _ => [::]).

Definition InferWidths_stage1 (F : HiFP.hfmodule) : option (CEP.t ftype) :=
(* infer widths of implicit-width components among the ports and statements in F.
   A full version would not work on one module alone but on all modules in a circuit together,
   but the principle remains the same. Therefore, let’s just run the algorithm on a single module for now. *)
match F with
| FExmod _ _ _ => None
| FInmod v ps ss =>
    match stmts_tmap (ports_tmap ps, module_graph_vertex_set_p.empty (seq HiFP.hfexpr)) ss, explireg_stmts ss with
    | Some (tmap', var2exprs), Some expli_reg => (* tmap' : all the expli/uninferred impli aggr&gtyp are stored here
                                            var2exprs : every connected elements are stored *)
           match drawg (module_graph_vertex_set_p.elements var2exprs) tmap' expli_reg emptyg nil with
           | Some (theg, vertices) => (* theg : new drawn graph
                                         vertices : set for topo sort to start with *)
               match TopoSort.topo_sort vertices theg with
               | TopoSort.Sorted inferorder => InferWidths_fun inferorder var2exprs tmap'
               | _ => None
               end
           | None => None
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

(*Definition connect_non_passive_gt (gt_tgt : fgtyp) (gt_src : fgtyp) : Prop :=
  match gt_tgt, gt_src with
      | Fuint _, Fuint _
      | Fuint _, Fuint_implicit _
      | Fsint _, Fsint _
      | Fsint _, Fsint_implicit _
      | Fclock, Fclock
      | Freset, Freset
      | Fasyncreset, Fasyncreset => True
      | Fuint_implicit wt, Fuint ws
      | Fuint_implicit wt, Fuint_implicit ws
      | Fsint_implicit wt, Fsint ws
      | Fsint_implicit wt, Fsint_implicit ws => wt >= ws
      | _, _ => False
      end.

Fixpoint connect_non_passive_type (ft_tgt : ftype) (ft_src : ftype) : Prop :=
  match ft_tgt, ft_src with
   | Gtyp gt_tgt, Gtyp gt_src => connect_non_passive_gt gt_tgt gt_src
   | Atyp elt_tgt n1, Atyp elt_src n2 => n1 = n2 /\ connect_non_passive_type elt_tgt elt_src
   | Btyp ft, Btyp fs => connect_non_passive_type_fields ft fs 
   | _, _ => False
   end
with connect_non_passive_type_fields (ft_tgt : ffield) (ft_src : ffield) : Prop :=
  match ft_tgt, ft_src with
   | Fnil, Fnil => True
   | Fflips v1 Nflip gtt ft, Fflips v2 Nflip gts fs => v1 = v2 /\
         connect_non_passive_type gtt gts /\
         connect_non_passive_type_fields ft fs 
   | Fflips v1 Flipped gtt ft, Fflips v2 Flipped gts fs => v1 = v2 /\
         connect_non_passive_type_flipped gts gtt /\
         connect_non_passive_type_fields ft fs
   | _, _ => False
   end
with connect_non_passive_type_flipped (ft_tgt : ftype) (ft_src : ftype) : Prop :=
   (* The code in this predicate is the same as in connect_non_passive. *)
   match ft_tgt, ft_src with
   | Gtyp gt_tgt, Gtyp gt_src => connect_non_passive_gt gt_tgt gt_src
   | Atyp elt_tgt n1, Atyp elt_src n2 => n1 = n2 /\ connect_non_passive_type_flipped elt_tgt elt_src
   | Btyp ft, Btyp fs => connect_non_passive_type_fields_flipped ft fs 
   | _, _ => False
   end
with connect_non_passive_type_fields_flipped (ft_tgt : ffield) (ft_src : ffield) : Prop :=
   (* The code in this predicate is the same as in connect_non_passive_fields. *)
   match ft_tgt, ft_src with
   | Fnil, Fnil => True
   | Fflips v1 Nflip gtt ft, Fflips v2 Nflip gts fs => v1 = v2 /\
         connect_non_passive_type_flipped gtt gts /\
         connect_non_passive_type_fields_flipped ft fs 
   | Fflips v1 Flipped gtt ft, Fflips v2 Flipped gts fs => v1 = v2 /\
         connect_non_passive_type gts gtt /\
         connect_non_passive_type_fields_flipped ft fs
   | _, _ => False
   end.
*)

Lemma set_find_sub : forall checkt nt nt0 n, ft_set_sub checkt nt n = Some nt0 -> ftype_equiv checkt nt0 -> ft_find_sub nt0 n = Some nt
with set_find_sub_f : forall checkf nf nf0 n, ft_set_sub_f checkf nf n = Some nf0 -> fbtyp_equiv checkf nf0 -> ft_find_ff nf0 n = Some nf.
Proof.
  clear set_find_sub.
  elim.
  intro f.
  intros nt nt0 n Hset Heq.
  simpl in Heq.
  simpl in Hset.
  case Ha : (n == N0); rewrite Ha in Hset; try discriminate.
  inversion Hset; clear Hset H0.
  case Hnt0 : (nt0) => [f0||]; rewrite Hnt0 in Heq; try discriminate.
  simpl; rewrite Ha; done.

  intros f Hg fn. 
  intros nt nt0 n Hset Heq.
  simpl in Hset.
  case Hset' : (ft_set_sub f nt n) => [natyp|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  simpl.
  rewrite -H0 in Heq; simpl in Heq.
  move /andP : Heq => [_ Heq].
  apply Hg; try done.

  intros f nt nt0 n Hset Heq.
  simpl in Hset.
  case Ha : (tmap_type_size_fields f <= n); rewrite Ha in Hset; try discriminate.
  case Hset' : (ft_set_sub_f f nt n) => [newf|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  simpl.
  assert (tmap_type_size_fields newf = tmap_type_size_fields f).
  admit.
  rewrite H; clear H; rewrite Ha.
  rewrite -H0 in Heq; simpl in Heq.
  apply set_find_sub_f with (checkf := f); try done.

  (*clear set_find_sub_f.
  intros checkf.
  induction checkf.
  intros nf a nf0 n Hset Heq.
  simpl in Hset; discriminate.

  intros nf a hf0 n Hset Heq.
  simpl in Hset.
  case Hf : f; rewrite Hf in Hset; try discriminate.
  case Ha : (a.2 == (n + 1)%num); rewrite Ha in Hset.
  inversion Hset; clear Hset.
  simpl; rewrite Ha; done.
  case Ha' : ((n + N.of_nat (num_ref f0))%num < a.2); rewrite Ha' in Hset.
  case Hset' : (ft_set_sub_f a checkf nf (n + N.of_nat (num_ref f0))) => [newf|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  apply IHcheckf in Hset'.
  simpl; rewrite Ha Ha'; done.
  rewrite -H0 in Heq.
  simpl in Heq; rewrite Hf in Heq.
  move /andP : Heq => [_ Heq]; done. 

  case Hset' : (ft_set_sub a f0 nf (n+1)) => [newt'|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  assert ((num_ref f0) = (num_ref newt')).
  rewrite -H0 in Heq.
  simpl in Heq.
  rewrite Hf in Heq.
  move /andP : Heq => [Heq _].
  move /andP : Heq => [_ Heq].
  apply num_ref_eq; done.
  rewrite H in Ha'; clear H.
  simpl; rewrite Ha Ha'.
  apply set_find_sub with (checkt := f0); try done.
  rewrite -H0 in Heq.
  simpl in Heq; rewrite Hf in Heq.
  move /andP : Heq => [Heq _].
  move /andP : Heq => [_ Heq].
  done.*)
Admitted.

Lemma ft_set_sub_eq : forall checkt nt' nt0 n init, ft_find_sub checkt n = Some init -> fgtyp_equiv init nt' -> ft_set_sub checkt nt' n = Some nt0 -> ftype_equiv checkt nt0
with ft_set_sub_eq_f : forall checkf nf' nf0 n init, ft_find_ff checkf n = Some init -> fgtyp_equiv init nf' -> ft_set_sub_f checkf nf' n = Some nf0 -> fbtyp_equiv checkf nf0.
Proof.
(* in InferWidths.v *)
Admitted.

Lemma max_compatible : forall el tmap otype nt eftl, fil_ftlist [seq type_of_hfexpr e tmap | e <- el] = Some eftl -> max_ftlist eftl otype = Some nt -> forall expr exprtype, expr \in el -> type_of_hfexpr expr tmap = Some exprtype -> connect_type_compatible (Gtyp nt) exprtype.
Proof.
  elim.
  intros.
  rewrite in_nil in H1; discriminate.
  intros hd tl H tmap init nt eftl Hl Hmax.
  simpl in Hl. 
  (*case Hhd : (type_of_e hd tmap) => [nht|]; rewrite Hhd in Hl; try discriminate.
  case Hl' : (fil_ftlist [seq type_of_e e tmap | e <- tl]) => [tl'|]; rewrite Hl' in Hl; try discriminate.
  inversion Hl; clear Hl.
  rewrite -H1 in Hmax.
  simpl in Hmax.
  case Hmax' : (max_ftlist tl' init) => [nt'|]; rewrite Hmax' in Hmax; try discriminate.

  intros expr exprtype Hin Hexpr.
  rewrite in_cons in Hin.
  case Heq : (expr == hd).
  move /eqP : Heq => Heq.
  rewrite Heq in Hexpr.
  rewrite Hexpr in Hhd.
  inversion Hhd; clear Hhd.
  move : Hmax. (* infer_compatible *)
  admit.
  rewrite Heq in Hin; clear Heq. 
  apply H with (tmap := tmap) (otype := init ) (nt := nt') (eftl := tl') (expr := expr) (exprtype := exprtype) in Hl'; try done.
  apply connect_compatible_dlvr with (t1 := nt) (t2 := nt') (t3 := exprtype); try done.
  move : Hmax.
  apply infer_compatible.*)
Admitted.

Lemma inferwidths_a : forall a v expr_seq tmap tmap', InferWidth_fun v expr_seq tmap = Some tmap' -> 
  if (a == v) then True 
  else match CEP.find (fst a, N0) tmap, CEP.find (fst a, N0) tmap' with
        | Some ft, Some ft' => ft_find_sub ft (snd a) = ft_find_sub ft' (snd a)
        | _, _ => True
        end.
Proof.
  (* 这个定理不对了
  intros.
  case Heq : (a == v); try done.
  case Heq' : ((a.1 == v.1) && (a.2 != v.2)).
  move /andP : Heq' => [H0 H1]; clear Heq.
  move /eqP : H0 => H0.
  rewrite H0. 
  rewrite /InferWidth_fun in H.
  case Hel : (fil_ftlist [seq type_of_e e tmap | e <- expr_seq]) => [eftl|]; rewrite Hel in H; try discriminate.
  case Hfindv0 : (ft_find (v.1, 0%num) tmap) => [init|]; rewrite Hfindv0 in H; try discriminate.
  case Hsub : (ft_find_sub v init 0) => [initt|]; rewrite Hsub in H; try discriminate.
  case Hmax : (max_ftlist eftl initt) => [nt|]; rewrite Hmax in H; try discriminate.
  case Hinfer : (InferWidth_ref v init nt) => [nt0|]; rewrite Hinfer in H; try discriminate.
  inversion H; clear H.
  rewrite ft_find_add.
  rewrite /InferWidth_ref in Hinfer.
  rewrite Hsub in Hinfer.
  case Hinfer' : (infer_implicit initt nt) => [newt|]; rewrite Hinfer' in Hinfer; try discriminate.
  (* forall a v, a.1 = v.1 -> a.2 != v.2 -> ft_set_sub v init newt 0 = Some nt0 -> ft_set_sub v init newt 0 = Some nt0. *)
  admit. (* inferref只改了v位置上的，故find_sub a应该相等 *)
  assert (a.1 != v.1).
  admit. (* 由Heq Heq'推出a.1!=v.1 *)
  rewrite /InferWidth_fun in H.
  case Hel : (fil_ftlist [seq type_of_e e tmap | e <- expr_seq]) => [eftl|]; rewrite Hel in H; try discriminate.
  case Hfindv0 : (ft_find (v.1, 0%num) tmap) => [init|]; rewrite Hfindv0 in H; try discriminate.
  case Hsub : (ft_find_sub v init 0) => [initt|]; rewrite Hsub in H; try discriminate.
  case Hmax : (max_ftlist eftl initt) => [nt|]; rewrite Hmax in H; try discriminate.
  case Hinfer : (InferWidth_ref v init nt) => [nt0|]; rewrite Hinfer in H; try discriminate.
  inversion H; clear H.
  case Hfinda0 : (ft_find (a.1, 0%num) tmap) => [ft|]; try done.
  (* find_add_not. forall a v nt tmap, ft_find a tmap = ft_find a (ft_add v nt tmap) *)
  admit.  ft = ft' *)
Admitted.

Lemma inferwidths_ls : forall el a var2exprs tmap tmap' checkt checkt', InferWidths_fun el var2exprs tmap = Some tmap' -> 
  ~(a \in el) -> CEP.find (fst a, N0) tmap' = Some checkt' -> CEP.find (fst a, N0) tmap = Some checkt -> ft_find_sub checkt (snd a) = ft_find_sub checkt' (snd a).
Proof.
 (* 这个定理不对了 *)
  
Admitted.

Lemma InferWidth_fun_correct : forall pv el tmap newtm, InferWidth_fun pv el tmap = Some newtm -> forall expr, expr \in el -> 
      match CEP.find (fst pv, N0) newtm with
      | Some checkt => match ft_find_sub checkt pv.2, type_of_hfexpr expr newtm with
                              | Some nt, Some te => ftype_equiv (Gtyp nt) te -> connect_type_compatible (Gtyp nt) te
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
  case Hte : (type_of_hfexpr expr newtm) => [te|]; try done.
  intro Heq.
  case Himpli : (not_implicit initt); rewrite Himpli in Hinfer.
  (* case 1 *)
  rewrite /connect_type_compatible.
  apply rwP with (P := ftype_equiv (Gtyp nt) te /\ check_connect_fgtyp_compatible (Gtyp nt) te (tmap_type_size (Gtyp nt))).
  apply andP.
  split; try done.
  simpl.
  case He : te => [gt||]; rewrite He in Heq; simpl in Heq; try discriminate.
  simpl.
  rewrite /connect_fgtyp_compatible.
  inversion Hinfer; clear Hinfer.
  rewrite H0 in Hinit; rewrite Hinit in Hcheckt; inversion Hcheckt; clear Hcheckt H0 Hinit.
  rewrite H1 in Hinitt; rewrite Hinitt in Hnt; inversion Hnt; clear Hnt Hinitt H1.
  rewrite H0 in Himpli; rewrite Himpli; done.
  (* case2 *)
  case Hmax : (max_ftlist eftl initt) => [tmax|]; rewrite Hmax in Hinfer; try discriminate.
  case Hset : (ft_set_sub init tmax pv.2) => [nt0|]; rewrite Hset in Hinfer; try discriminate.
  inversion Hinfer; clear Hinfer.
  rewrite -H0 in Hte Hcheckt; clear H0.
  rewrite HiFP.PCELemmas.OP.P.F.add_eq_o in Hcheckt.
  inversion Hcheckt; clear Hcheckt.
  rewrite -H0 in Hnt; clear H0.
  apply set_find_sub in Hset; try done.
  rewrite Hset in Hnt; clear Hset.
  inversion Hnt; clear Hnt.
  rewrite -H0; clear H0.
  apply max_compatible with (el := el) (tmap := tmap) (otype := initt) (eftl := eftl) (expr := expr); try done.
  admit. (* 由于不成环，不影响expr的type，由Hte *)
  admit. (* ft_set 的性质，由Hset *)
Admitted.

Lemma InferWidths_fun_correct : forall (hfs : HiFP.hfstmt) (inferorder : seq ProdVarOrder.t) (var2exprs : var2exprsmap) (tmap newtm : CEP.t ftype),
  InferWidths_fun inferorder var2exprs tmap = Some newtm -> match hfs with
    | Sfcnct ref_tgt (Eref ref_src) => match base_ref ref_tgt newtm, base_ref ref_src newtm with
                                      | Some (pv_tgt, t_tgt), Some (pv_src, t_src) => connect_non_passive_type t_tgt t_src
                                      | _, _ => True
                                      end 
    | Sfcnct ref_tgt expr_src => match base_ref ref_tgt newtm, type_of_hfexpr expr_src newtm with
                                      | Some tgt, Some t_expr => connect_type_compatible tgt.2 t_expr
                                      | _, _ => True
                                      end
    | _ => True
    end.
Proof.
  intros hfs inferorder var2exprs tmap newtm Hinfer.
  case Hs : hfs => [||||||ref expr||]; try done.
  case He : expr => [ct c| c e1 | u e1 | op e1 e2 | c e1 e2 | c e1 | ref0 ]. 
  (* const *)
  rewrite -He.
  case Hbase : (base_ref ref newtm) => [tgt|]; try done.
  case Hte : (type_of_hfexpr expr newtm) => [t_expr|] ; try done.
  rewrite /connect_type_compatible.
  apply rwP with (P := ftype_equiv tgt.2 t_expr /\
    check_connect_fgtyp_compatible tgt.2 t_expr (tmap_type_size tgt.2)).
  apply andP.
  split. 
  admit. (* 对connection语句的要求 *)

  assert (forall ft te, (forall n gt gte, n < tmap_type_size ft -> ft_find_sub ft (N.of_nat n) = Some gt -> ft_find_sub te (N.of_nat n) = Some gte ->
        connect_fgtyp_compatible gt gte) ->
    check_connect_fgtyp_compatible ft te (tmap_type_size ft)).
  admit.

  apply H; clear H.
  intros n gt gte Hn Hlhs Hrhs.
  assert ((tgt.1.1, N.add tgt.1.2 (N.of_nat n)) \in inferorder).
  admit. (* inferorder 的正确性，是展开时的标号 *)
  assert (exists order1 order2, inferorder = order1 ++ ((tgt.1.1, N.add tgt.1.2 (N.of_nat n)) :: order2) /\ ~ (tgt.1.1, N.add tgt.1.2 (N.of_nat n)) \in order1 /\ ~ (tgt.1.1, N.add tgt.1.2 (N.of_nat n)) \in order2).
  admit. (* 由H推出 *)
  clear H.
  move : H0 => [order1 [order2 [H [Horder1 Horder2]]]].
  rewrite H in Hinfer; rewrite /InferWidths_fun in Hinfer.
  case Hinfer1 : (InferWidths_fun order1 var2exprs tmap) => [tmap'|].
  assert (Hinfer2 : InferWidths_fun ((tgt.1.1, N.add tgt.1.2 (N.of_nat n)) :: order2) var2exprs tmap' = Some newtm).
  admit. (* 由 Hinfer Hinfer1 *)
  clear Hinfer.
  simpl in Hinfer2.
  case Hel : (module_graph_vertex_set_p.find (tgt.1.1, N.add tgt.1.2 (N.of_nat n)) var2exprs) => [el|]; rewrite Hel in Hinfer2; try done.
  case Hinfer : (InferWidth_fun (tgt.1.1, N.add tgt.1.2 (N.of_nat n)) el tmap') => [newtm'|]; rewrite Hinfer in Hinfer2; try discriminate.

  assert (forall expr rhs_expr_ls t_expr newtm, type_of_hfexpr expr newtm = Some t_expr -> split_expr_connect expr t_expr = Some rhs_expr_ls ->  (* 这里可以加bool list用来判断flip *)
            forall n, n < length rhs_expr_ls -> match List.nth_error rhs_expr_ls n, ft_find_sub t_expr (N.of_nat n) with
                                    | Some texpr, Some gt => type_of_hfexpr texpr newtm = Some (Gtyp gt)
                                    | _, _ => true
                                    end). 
  admit. (* split和typeofexpr的性质 *)

  case Hsplit : (split_expr_connect expr t_expr) => [rhs_expr_ls|].
  apply H0 with (expr := expr) (rhs_expr_ls := rhs_expr_ls) (t_expr := t_expr) (newtm := newtm) (n := n) in Hsplit; try done; clear H0.
  case Htexpr : (nth_error rhs_expr_ls n) => [texpr|]; rewrite Htexpr in Hsplit.
  rewrite Hrhs in Hsplit.

  apply InferWidth_fun_correct with (pv := (tgt.1.1, N.add tgt.1.2 (N.of_nat n))) (el := el) (tmap := tmap') (newtm := newtm') (expr := texpr) in Hinfer.
  simpl in Hinfer.
  case Htgt0 : (CEP.find (tgt.1.1, 0%num) newtm') => [checkt'|]; rewrite Htgt0 in Hinfer.
  case Hsub0 : (ft_find_sub checkt' (tgt.1.2 + N.of_nat n)) => [nt|]; rewrite Hsub0 in Hinfer.
  case Htgt : (CEP.find (tgt.1.1, 0%num) newtm) => [checkt|].
  apply inferwidths_ls with (var2exprs := var2exprs) (tmap := newtm') (tmap' := newtm) (checkt := checkt') (checkt' := checkt) in Horder2; try done.
  rewrite Hsub0 in Horder2; clear Hsub0.
  simpl in Horder2.

  assert (forall ref n pv ft tmap, base_ref ref tmap = Some (pv, ft) -> CEP.find (tgt.1.1, 0%num) tmap = Some checkt -> ft_find_sub checkt (tgt.1.2 + N.of_nat n) = ft_find_sub tgt.2 (N.of_nat n)).
  admit. (* 两种返回ftype函数的关系和正确性 *)

  specialize H0 with (ref := ref) (n := n) (pv := tgt.1) (ft := tgt.2) (tmap := newtm).
  apply H0 in Htgt; clear H0; try done.
  rewrite Htgt in Horder2; clear Htgt.
  rewrite Hlhs in Horder2; clear Hlhs.
  inversion Horder2; clear Horder2.

  case Hte' : (type_of_hfexpr texpr newtm') => [te|]; rewrite Hte' in Hinfer.
  assert (type_of_hfexpr texpr newtm = Some te).
  admit. (* 由于拓扑排序，texpr不受order2中的位宽更新影响。由Hte' Hinfer2 *)
  clear Hte'.
  rewrite H0 in Hsplit.
  inversion Hsplit; clear Hsplit.
  rewrite H3 H1 in Hinfer.
  rewrite /connect_type_compatible in Hinfer.
  assert (fgtyp_equiv gt gte).
  admit. (* 从某个地方来的连接合法的前提 *)
  apply Hinfer in H2; clear Hinfer.
  move /andP : H2 => [_ Hinfer].
  simpl in Hinfer. 
  move /andP : Hinfer => [Hinfer _]; done.

  admit. (* type_of_hfexpr 不为None，由Htgt0 *)
  admit. (* eta_expand这是啥，有Hbase *)
  admit. (* 由Htgt0不为None *)
  admit. (* 由 n < tmap_type_size tgt.2 知Hsub0不为None *)
  admit. (* 被连接的应该已被声明，find不为None *)
  admit. (* var2exprs应当满足的性质，由add_expr_connect *)
  admit. (* n 不超过 rhs_expe_ls 的长度，不为None *)
  assert (length rhs_expr_ls = tmap_type_size tgt.2).
  admit. (* 由split_expr_connect的性质 *)
  rewrite H0; clear H0; done.
  admit. (* expr应该与t_expr匹配，不会出错 *)
  admit. (* 若infer order1有错误，则infer没有结果 *)

  (* 所有passive的expr都一样 *)
  admit.
  admit.
  admit.
  admit.
  admit.

  (* ref non_passive *)
  case Htgt : (base_ref ref newtm) => [[v_tgt t_tgt]|]; try done.
  case Hsrc : (base_ref ref0 newtm) => [[v_src t_src]|]; try done.
  rewrite /connect_non_passive_type.
  apply rwP with (P := ftype_equiv t_tgt t_src /\ check_connect_non_passive_fgtyp t_tgt t_src (tmap_type_size t_tgt)).
  apply andP.
  split. 
  admit. (* 对connection语句的要求 *)

  assert (forall ft te, (forall n gt gte, n < tmap_type_size ft -> ft_find_sub ft (N.of_nat n) = Some gt -> ft_find_sub te (N.of_nat n) = Some gte ->
        match ft_check_flip ft (N.of_nat n) false with
        | Some false => connect_fgtyp_compatible gt gte
        | Some true => connect_fgtyp_compatible gte gt
        | None => false
        end) ->
        check_connect_non_passive_fgtyp ft te (tmap_type_size ft)).
  admit.

  apply H; clear H.
  intros n gt gte Hn Hlhs Hrhs.

  (* stop here, 在拆开infer之前，应该确定lhs or rhs的pv in inferorder *)
  (* TBD!! *)
  
  assert ((v_tgt.1, N.add v_tgt.2 (N.of_nat n)) \in inferorder).
  admit. (* inferorder 的正确性，是展开时的标号 *)
  assert (exists order1 order2, inferorder = order1 ++ ((v_tgt.1, N.add v_tgt.2 (N.of_nat n)) :: order2) /\ ~ (v_tgt.1, N.add v_tgt.2 (N.of_nat n)) \in order1 /\ ~ (v_tgt.1, N.add v_tgt.2 (N.of_nat n)) \in order2).
  admit. (* 由H推出 *)
  clear H.
  move : H0 => [order1 [order2 [H [Horder1 Horder2]]]].
  rewrite H in Hinfer; rewrite /InferWidths_fun in Hinfer.
  case Hinfer1 : (InferWidths_fun order1 var2exprs tmap) => [tmap'|].
  assert (Hinfer2 : InferWidths_fun ((v_tgt.1, N.add v_tgt.2 (N.of_nat n)) :: order2) var2exprs tmap' = Some newtm).
  admit. (* 由 Hinfer Hinfer1 *)
  clear Hinfer.
  simpl in Hinfer2.
  case Hel : (module_graph_vertex_set_p.find (v_tgt.1, N.add v_tgt.2 (N.of_nat n)) var2exprs) => [el|]; rewrite Hel in Hinfer2; try done.
  case Hinfer : (InferWidth_fun (v_tgt.1, N.add v_tgt.2 (N.of_nat n)) el tmap') => [newtm'|]; rewrite Hinfer in Hinfer2; try discriminate.

  assert (forall ref_tgt ref_src t_tgt t_src v_tgt v_src tmap, base_ref ref_tgt tmap = Some (v_tgt, t_tgt) -> base_ref ref_src tmap = Some (v_src, t_src) ->
              match split_expr_non_passive ref_tgt t_tgt false, split_expr_non_passive ref_src t_src false with
              | Some lhsl, Some rhsl => (forall n, n < length lhsl -> match List.nth_error lhsl n, List.nth_error rhsl n with
                                        | Some (_, false), Some (ref2, false) => match module_graph_vertex_set_p.find (v_tgt.1, N.add v_tgt.2 (N.of_nat n)) var2exprs with
                                                          | Some el => (Eref ref2) \in el
                                                          | None => false
                                                          end
                                        | Some (ref1, true), Some (_, true) => match module_graph_vertex_set_p.find (v_src.1, N.add v_src.2 (N.of_nat n)) var2exprs with
                                                          | Some el => (Eref ref1) \in el
                                                          | None => false
                                                          end
                                        | _,_ => false
                                        end)
              | _, _ => false
              end). 
  admit. (* split和存var2exprs的性质 *)
  apply H0 with (ref_tgt := ref) (t_tgt := t_tgt) (v_tgt := v_tgt) (ref_src := ref0) (t_src := t_src) (v_src := v_src) in Htgt; try done; clear H0.
  case Hsplit_lhs : (split_expr_non_passive ref t_tgt false) => [lhsl|]; rewrite Hsplit_lhs in Htgt.
  case Hsplit_rhs : (split_expr_non_passive ref0 t_src false) => [rhsl|]; rewrite Hsplit_rhs in Htgt.
  assert (length lhsl = tmap_type_size t_tgt).
  admit.
  rewrite H0 in Htgt; clear H0.
  apply Htgt in Hn; clear Htgt.
  
  case Hlhsl : (nth_error lhsl n) => [[ref1 b1]|]; rewrite Hlhsl in Hn.
  case Hrhsl : (nth_error rhsl n) => [[ref2 b2]|]; rewrite Hrhsl in Hn.
  case Hcheckfl : (ft_check_flip t_tgt (N.of_nat n) false) => [b1'|].
  assert (b1 = b1').
  admit. (* 两种不同的算flip方法应当结果相同 *)
  assert (b1 = b2). (* tgt和src类型相同 *)
  admit.

  case Hb : b1; rewrite Hb in H0 Hn H1; rewrite -H0; rewrite -H1 in Hn.
  (* case1 : flip field *)
  apply InferWidth_fun_correct with (pv := (v_src.1, (v_src.2 + N.of_nat n)%num)) (el := el) (tmap := tmap') (newtm := newtm') (expr := (Eref ref1)) in Hinfer.
  simpl in Hinfer.
  case Htgt0 : (CEP.find (tgt.1.1, 0%num) newtm') => [checkt'|]; rewrite Htgt0 in Hinfer.
  case Hsub0 : (ft_find_sub checkt' (tgt.1.2 + N.of_nat n)) => [nt|]; rewrite Hsub0 in Hinfer.
  case Htgt : (CEP.find (tgt.1.1, 0%num) newtm) => [checkt|].
  apply inferwidths_ls with (var2exprs := var2exprs) (tmap := newtm') (tmap' := newtm) (checkt := checkt') (checkt' := checkt) in Horder2; try done.
  rewrite Hsub0 in Horder2; clear Hsub0.
  simpl in Horder2.

  assert (forall ref n pv ft tmap, base_ref ref tmap = Some (pv, ft) -> CEP.find (tgt.1.1, 0%num) tmap = Some checkt -> ft_find_sub checkt (tgt.1.2 + N.of_nat n) = ft_find_sub tgt.2 (N.of_nat n)).
  admit. (* 两种返回ftype函数的关系和正确性 *)

Admitted.

Definition InferWidths_m F :=
  match InferWidths_stage1 F with
  | Some newtm => InferWidths_stage2 F newtm 
  | None => None
  end.

Lemma InferWidths_correct : forall (F : HiFP.hfmodule) (vm' : module_graph_vertex_set_p.env) (ct : module_graph_connection_trees_p.env),
  match InferWidths_m F with
  | Some F' => Sem F' vm' ct -> Sem F (make_vm_implicit F vm') ct
  | _ => True
  end.
Proof.
  
Admitted.

Fixpoint fillft_vm (n : nat) (ft : ftype) (pv : ProdVarOrder.t) (vmap : module_graph_vertex_set_p.env) : option ftype :=
   match n with
   | 0 => Some ft
   | S m => match module_graph_vertex_set_p.find (fst pv, (N.add (snd pv) (N.of_nat m))) vmap with
            | Some nt => match List.hd_error (input_connectors nt) with
                        | Some gt => match ft_set_sub (fst pv, (N.add (snd pv) (N.of_nat m))) ft (Gtyp gt) (snd pv) with
                                   | Some nft => fillft_vm m nft pv vmap
                                   | None => None
                                   end
                       | None => None
                       end
           | None => None
           end
   end.

Fixpoint type_of_hfexpr_vm (vmap : module_graph_vertex_set_p.env) (e : HiFP.hfexpr) (tmap : CEP.t ftype) : option ftype :=
   match e with
   | Econst t bs => match t with
                    | Fuint_implicit w => Some (Gtyp (Fuint (size bs)))
                    | Fsint_implicit w => Some (Gtyp (Fsint (size bs)))
                    | t => Some (Gtyp t)
                    end
   | Eref r => match base_ref r tmap with
              | Some (pv, checkt) => fillft_vm (tmap_type_size checkt) checkt pv vmap
              | None => None
              end
   | Ecast AsUInt e1 => match type_of_hfexpr_vm vmap e1 tmap with
                         | Some (Gtyp (Fsint w))
                         | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint w))
                         | Some (Gtyp Fclock)
                         | Some (Gtyp Freset)
                         | Some (Gtyp Fasyncreset) => Some (Gtyp (Fuint 1))
                         | _ => None
                         end
   | Ecast AsSInt e1 => match type_of_hfexpr_vm vmap e1 tmap with
                         | Some (Gtyp (Fsint w))
                         | Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint w))
                         | Some (Gtyp Fclock)
                         | Some (Gtyp Freset)
                         | Some (Gtyp Fasyncreset) => Some (Gtyp (Fsint 1))
                         | _ => None
                         end
   | Ecast AsClock e1 => match type_of_hfexpr_vm vmap e1 tmap with
                         | Some (Gtyp _) => Some (Gtyp Fclock)
                         | _ => None
                         end
   | Ecast AsAsync e1 => match type_of_hfexpr_vm vmap e1 tmap with
                         | Some (Gtyp _) => Some (Gtyp Fasyncreset)
                         | _ => None
                         end
   | Eprim_unop (Upad n) e1 => match type_of_hfexpr_vm vmap e1 tmap with
                                | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (maxn w n)))
                                | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (maxn w n)))
                                | _ => None
                                end
   | Eprim_unop (Ushl n) e1 => match type_of_hfexpr_vm vmap e1 tmap with
                                | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (w + n)))
                                | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (w + n)))
                                | _ => None
                                end
   | Eprim_unop (Ushr n) e1 => match type_of_hfexpr_vm vmap e1 tmap with
                                | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (maxn (w - n) 1)))
                                | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (maxn (w - n) 1)))
                                | _ => None
                                end
   | Eprim_unop Ucvt e1 => match type_of_hfexpr_vm vmap e1 tmap with
                            | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint w))
                            | Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint (w + 1)))
                            | _ => None
                            end
   | Eprim_unop Uneg e1 => match type_of_hfexpr_vm vmap e1 tmap with
                            | Some (Gtyp (Fsint w))
                            | Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint (w + 1)))
                            | _ => None
                            end
   | Eprim_unop Unot e1 => match type_of_hfexpr_vm vmap e1 tmap with
                            | Some (Gtyp (Fsint w))
                            | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint w))
                            | _ => None
                            end
   | Eprim_unop (Uextr n1 n2) e1 => match type_of_hfexpr_vm vmap e1 tmap with
                                     | Some (Gtyp (Fsint w))
                                     | Some (Gtyp (Fuint w)) =>
                                          if (n2 <= n1) && (n1 < w) then Some (Gtyp (Fuint (n1 - n2 + 1)))
                                                                    else None
                                     | _ => None
                                     end
   | Eprim_unop (Uhead n) e1 => match type_of_hfexpr_vm vmap e1 tmap with
                                 | Some (Gtyp (Fsint w))
                                 | Some (Gtyp (Fuint w)) =>
                                      if n <= w then Some (Gtyp (Fuint n))
                                                else None
                                 | _ => None
                                 end
   | Eprim_unop (Utail n) e1 => match type_of_hfexpr_vm vmap e1 tmap with
                                 | Some (Gtyp (Fsint w))
                                 | Some (Gtyp (Fuint w)) =>
                                      if n <= w then Some (Gtyp (Fuint (w - n)))
                                                else None
                                 | _ => None
                                 end
   | Eprim_unop _ e1 => match type_of_hfexpr_vm vmap e1 tmap with
                         | Some (Gtyp (Fsint _))
                         | Some (Gtyp (Fuint _)) => Some (Gtyp (Fuint 1))
                         | _ => None
                         end
   | Eprim_binop (Bcomp _) e1 e2 => match type_of_hfexpr_vm vmap e1 tmap, type_of_hfexpr_vm vmap e2 tmap with
                                     | Some (Gtyp (Fsint _)), Some (Gtyp (Fsint _))
                                     | Some (Gtyp (Fuint _)), Some (Gtyp (Fuint _)) => Some (Gtyp (Fuint 1))
                                     | _, _ => None
                                     end
   | Eprim_binop Badd e1 e2
   | Eprim_binop Bsub e1 e2 => match type_of_hfexpr_vm vmap e1 tmap, type_of_hfexpr_vm vmap e2 tmap with
                                | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (maxn w1 w2 + 1)))
                                | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (maxn w1 w2 + 1)))
                                | _, _ => None
                                end
   | Eprim_binop Bmul e1 e2 => match type_of_hfexpr_vm vmap e1 tmap, type_of_hfexpr_vm vmap e2 tmap with
                                | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (w1 + w2)))
                                | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (w1 + w2)))
                                | _, _ => None
                                end
   | Eprim_binop Bdiv e1 e2  => match type_of_hfexpr_vm vmap e1 tmap, type_of_hfexpr_vm vmap e2 tmap with
                                 | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint w1))
                                 | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (w1 + 1)))
                                 | _, _ => None
                                 end
   | Eprim_binop Brem e1 e2 => match type_of_hfexpr_vm vmap e1 tmap, type_of_hfexpr_vm vmap e2 tmap with
                                 | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (minn w1 w2)))
                                 | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (minn w1 w2)))
                                 | _, _ => None
                                 end
   | Eprim_binop Bdshl e1 e2 => match type_of_hfexpr_vm vmap e1 tmap, type_of_hfexpr_vm vmap e2 tmap with
                                 | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (w1 + 2 ^ w2 - 1)))
                                 | Some (Gtyp (Fsint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fsint (w1 + 2 ^ w2 - 1)))
                                 | _, _ => None
                                 end
   | Eprim_binop Bdshr e1 e2 => match type_of_hfexpr_vm vmap e1 tmap, type_of_hfexpr_vm vmap e2 tmap with
                                 | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint w1))
                                 | Some (Gtyp (Fsint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fsint w1))
                                 | _, _ => None
                                 end
   | Eprim_binop Bcat e1 e2 => match type_of_hfexpr_vm vmap e1 tmap, type_of_hfexpr_vm vmap e2 tmap with
                                | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2))
                                | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fuint (w1 + w2)))
                                | _, _ => None
                                end
   | Eprim_binop Band e1 e2
   | Eprim_binop Bor e1 e2
   | Eprim_binop Bxor e1 e2 => match type_of_hfexpr_vm vmap e1 tmap, type_of_hfexpr_vm vmap e2 tmap with
                                | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2))
                                | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fuint (maxn w1 w2)))
                                | _, _ => None
                                end
   | Emux c e1 e2 => match type_of_hfexpr_vm vmap c tmap, type_of_hfexpr_vm vmap e1 tmap, type_of_hfexpr_vm vmap e2 tmap with
                      | Some (Gtyp (Fuint 1)), Some t1, Some t2 => mux_types t1 t2
                      | _, _, _ => None
                      end
   | Evalidif c e1 => match type_of_hfexpr_vm vmap c tmap with
                      | Some (Gtyp (Fuint 1)) => type_of_hfexpr_vm vmap e1 tmap
                      | _ => None
                      end
   | _ => None (* Some (Gtyp (Fuint 0)) *)
   end.

Lemma InferWidths_fun_correct' F : forall vmap inferorder var2exprs tmap ct, Sem F vmap ct -> 
  forall v, v \in inferorder -> 
        match module_graph_vertex_set_p.find v vmap, module_graph_vertex_set_p.find v var2exprs, CEP.find (fst v, N0) tmap with
        | Some nt, Some el, Some init => match List.hd_error (input_connectors nt), fil_ftlist (map (fun e => type_of_hfexpr_vm vmap e tmap) el), ft_find_sub v init N0 with
                    | Some gt, Some eftl, Some (Gtyp initt) => match max_ftlist eftl initt with
                                                        | Some nt => sizeof_fgtyp gt >= sizeof_fgtyp nt
                                                        | _ => true
                                                        end
                    | _,_,_ => true
                    end
        | _,_,_ => true
        end.
Proof.
  
Qed.
