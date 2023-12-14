From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq ssrfun.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.
From firrtl Require Import Firrtl Env HiEnv HiFirrtl ModuleGraph TopoSort. 

Definition s1 := [::true].
Definition s2 := [::true; false].
Compute (TopoSort.subset s1 s2).

Definition updg (key : ProdVarOrder.t) (v : seq ProdVarOrder.t) (map : ProdVarOrder.t -> seq ProdVarOrder.t) : ProdVarOrder.t -> seq ProdVarOrder.t :=
    fun (y : ProdVarOrder.t) => if y == key then v else map y.

Definition g0 := fun (y : N) => if y == N0 then [:: 1%num]
                                else if y == 1%num then [:: 2%num]
                                     else if y == 3%num then [:: 2%num]
                                                        else nil.
Compute (TopoSort.topo_sort [:: N0; 1%num; 2%num; 3%num] g0).

(* search start from roots: const\input port\reg
   update regs after all the other cncts, draw another depandency graph for regs. *)

(* not last connection yet, so that one variable map to a stmt set.
   one element is explored, once all the elements in its stmt set are explored. *)

(*Fixpoint infer_implicit (ft_ref : ftype) (ft_expr : ftype_explicit) : option ftype :=
  (* If ft_ref is an implicit-width type and ft_expr a compatible explicit-width type,
     return an expanded ft_ref whose width fits (at least) ft_expr.
     If ft_ref is an explicit-width type and ft_expr is compatible, return ft_ref.
     If the types are not compatible, return None. *)
  match ft_ref, ft_expr with
  | Gtyp (Fuint _), exist (Gtyp (Fuint _)) _
  | Gtyp (Fsint _), exist (Gtyp (Fsint _)) _
  | Gtyp Fclock, exist (Gtyp Fclock) _
  | Gtyp Freset, exist (Gtyp Freset) _
  | Gtyp Fasyncreset, exist (Gtyp Fasyncreset) _ => Some ft_ref (* if it's not an implicit type, don't change that. *)
  | Gtyp (Fuint_implicit w_ref), exist (Gtyp (Fuint w_expr)) _ => Some (Gtyp (Fuint_implicit (max w_ref w_expr)))
  | Gtyp (Fsint_implicit w_ref), exist (Gtyp (Fsint w_expr)) _ => Some (Gtyp (Fsint_implicit (max w_ref w_expr)))
  | Atyp t_ref n_ref, exist (Atyp t_expr n_expr) p => match (n_ref == n_expr), infer_implicit t_ref (exist ftype_not_implicit_width t_expr p) with
                                                      | true, Some nt => Some (Atyp nt n_expr)
                                                      | _, _ => None
                                                      end
  | Btyp ff_ref, exist (Btyp ff_expr) p => match infer_implicit_fields ff_ref (exist ffield_not_implicit_width ff_expr p) with
                                          | Some nf => Some (Btyp nf)
                                          | None => None
                                          end
  | _, _ => None
  end
with infer_implicit_fields (ff_ref : ffield) (ff_expr : ffield_explicit) : option ffield :=
   match ff_ref, ff_expr with
   | Fnil, exist Fnil _ => Some Fnil
   | Fflips v_ref Nflip t_ref ff_ref', exist (Fflips v_expr Nflip t_expr ff_expr') p =>
          match (v_ref == v_expr), infer_implicit t_ref (exist ftype_not_implicit_width t_expr (proj1 p)), infer_implicit_fields ff_ref' (exist ffield_not_implicit_width ff_expr' (proj2 p)) with
          | true, Some nt, Some nf => Some (Fflips v_ref Nflip nt nf)
          | _,_,_ => None
          end
   | _, _ => None
   end.*)

Fixpoint infer_implicit (ft1 : ftype) (ft2 : ftype) : option ftype :=
  match ft1, ft2 with
  | Gtyp (Fuint w1), Gtyp (Fuint w2)
  | Gtyp (Fsint w1), Gtyp (Fsint w2) => Some ft1
  | Gtyp Fclock, Gtyp Fclock
  | Gtyp Freset, Gtyp Freset
  | Gtyp Fasyncreset, Gtyp Fasyncreset => Some ft1
  | Gtyp (Fuint_implicit w1), Gtyp (Fuint_implicit w2) => Some (Gtyp (Fuint_implicit (max w1 w2)))
  | Gtyp (Fsint_implicit w1), Gtyp (Fsint_implicit w2) => Some (Gtyp (Fsint_implicit (max w1 w2)))
  | Atyp t1 n1, Atyp t2 n2 => match (n1 == n2), infer_implicit t1 t2 with
                              | true, Some nt => Some (Atyp nt n1)
                              | _, _ => None
                              end
  | Btyp ff1, Btyp ff2 => match infer_implicit_fields ff1 ff2 with
                          | Some nf => Some (Btyp nf)
                          | None => None
                          end
  | _, _ => None
  end
with infer_implicit_fields (ff1 : ffield) (ff2 : ffield) : option ffield :=
   match ff1, ff2 with
   | Fnil, Fnil => Some Fnil
   | Fflips v1 f1 t1 ff1', Fflips v2 f2 t2 ff2' =>
          match (v1 == v2), fflip_eqn f1 f2, infer_implicit t1 t2, infer_implicit_fields ff1' ff2' with
          | true, true, Some nt, Some nf => Some (Fflips v1 Nflip nt nf)
          | _,_,_,_ => None
          end
   | _, _ => None
   end.
   
Fixpoint ft_find_upper (v : ProdVarOrder.t) (checkt : ftype) (num : N) (ls : seq ProdVarOrder.t) : option (seq ProdVarOrder.t) :=
  match checkt with
  | Gtyp gt => if (snd v) == num then Some (v :: ls)
                else None
  | Atyp atyp n => if (snd v) == num then Some (v :: ls) (* 是整个Atyp *)
                    else if (((N.to_nat (snd v)) -1 - (N.to_nat num)) mod (num_ref atyp)) == 0 (* 是atyp *)
                      then Some (v :: ls)
                    else (* 是atyp中的结构 *)
                      let n' := ((N.to_nat (snd v)) - 1- (N.to_nat num)) / (num_ref atyp) in
                      match ft_find_upper v atyp (N.add num (N.of_nat (n' * (num_ref atyp)))) ls with
                      | Some ls' => Some (v :: ls')
                      | None => None
                      end
  | Btyp ff => if (snd v) == num then Some (v :: ls)
                else match ft_find_upper_f v ff num ls with
                    | Some ls' => Some ((fst v, num) :: ls')
                    | None => None
                    end
  end
with ft_find_upper_f (v : ProdVarOrder.t) (ff : ffield) (num : N) (ls : seq ProdVarOrder.t) : option (seq ProdVarOrder.t) :=
  match ff with
  | Fflips v0 _ ft ff' => if (snd v) == (N.add num 1%num) (* 找到被更新的标号, 所对应的field *)
                              then Some (v :: ls)
                          else if (snd v) > (N.add num (N.of_nat (num_ref ft))) (* 不在该field中, 找下一个field *)
                              then ft_find_upper_f v ff' (N.add num (N.of_nat (num_ref ft))) ls
                           else (* 在field v0中 *)
                              match ft_find_upper v ft (N.add num 1%num) ls with
                              | Some ls' => Some ((fst v, N.add num 1%num) :: ls')
                              | None => None
                              end
  | _ => None
  end.

(* 有必要check这几个函数功能是否正确 *)

Fixpoint ft_find_sub (v : ProdVarOrder.t) (checkt : ftype) (num : N) : option ftype :=
  match checkt with
  | Gtyp gt => if (snd v) == num then Some checkt else None
  | Atyp atyp n => if (((N.to_nat (snd v)) - 1- (N.to_nat num)) mod (num_ref atyp)) == 0 (* 对应标号是atyp，可能agg *)
                   then Some atyp
                   else (* 继续找atyp中的结构 *)
                    let n' := ((N.to_nat (snd v)) - 1- (N.to_nat num)) / (num_ref atyp) in
                    ft_find_sub v atyp (N.add num (N.of_nat (n' * (num_ref atyp))))
  | Btyp ff => match ft_find_ff v ff num with
              | Some newf => Some newf
              | None => None
              end
  end
with ft_find_ff (v : ProdVarOrder.t) (ff : ffield) (num : N) : option ftype :=
  match ff with
  | Fflips v0 _ ft ff' => if (snd v) == (N.add num 1%num) (* 找到被更新的标号, 所对应的field *)
                              then Some ft
                          else if (snd v) > (N.add num (N.of_nat (num_ref ft))) (* 不在该field中, 找下一个field *)
                              then ft_find_ff v ff' (N.add num (N.of_nat (num_ref ft)))
                           else (* 在field v0中 *)
                              ft_find_sub v ft num
  | _ => None
  end.

(* wire a : { b : { d : SInt, flipped e : UInt<7> }[5], c : UInt<3> }
   wire y : { d : SInt<3>, flipped e : UInt }
   a.b[2].d <= SInt<2>(-1).

   a.b <= ... (array of 5 elements)
   a.b[1] <= y (* should infer widths of a.b[...].d and of y.e *)
   a.b[3].e <= y.e (* which direction does this connection go?  I am not sure; I think data flows from y to a. *)
   I think you need mutual recursion with InferWidth_ff and InferWidth_fun. *)

(*Fixpoint InferWidth_ref (v : ProdVarOrder.t) (checkt : ftype) (newt : ftype_explicit) (num : N) : option ftype :=
  match checkt with
  | Gtyp _ => infer_implicit checkt newt
  | Atyp atyp n => if (((N.to_nat (snd v)) - 1- (N.to_nat num)) mod (num_ref atyp)) == 0
                   then (* 比较atyp与newt是否match, 取较大的更新Atyp *)
                    match infer_implicit atyp newt with
                    | Some newt' => Some (Atyp newt' n)
                    | None => None
                    end
                   else (* 继续找atyp中的结构 *)
                    let n' := ((N.to_nat (snd v)) - 1- (N.to_nat num)) / (num_ref atyp) in
                    InferWidth_ref v atyp newt (N.add num (N.of_nat (n' * (num_ref atyp))))
  | Btyp ff => match InferWidth_ff v ff newt num with
              | Some newf => Some (Btyp newf)
              | None => None
              end
  end
with InferWidth_ff (v : ProdVarOrder.t) (ff : ffield) (newt : ftype_explicit) (num : N) : option ffield :=
  (* changes the (v-num)th field of ff.
     If (v-num) == 1, then the first field is changed from implicit-width to explicit-width.
     If (v-num) == 2, 3, ... 1+size_of_ftype (type of first fieldd), then some subfield of the first field is changed.
     If (v-num) > 1+size_of_ftype (type of first field), then a subsequent field of ff is changed. *)
  match ff with
  | Fflips v0 Nflip ft ff' => if (snd v) == (N.add num 1%num) (* 找到被更新的标号, 所对应的field *)
                              then (* 比较Btyp现有对应位置上的ftype和待更新的newt是否match, 取较大的更新Btyp *)
                                match infer_implicit ft newt with 
                                | Some newt' => Some (Fflips v0 Nflip newt' ff') (* 修改当前field的type, ff'不变 *)
                                | None => None
                                end
                              else if (snd v) > (N.add num (N.of_nat (num_ref ft))) (* 不在该field中, 找下一个field *)
                                   then match InferWidth_ff v ff' newt (N.add num (N.of_nat (num_ref ft))) with
                                      | Some newf => Some (Fflips v0 Nflip ft newf)
                                      | None => None
                                      end
                                   else (* 在field v0中 *)
                                   match InferWidth_ref v ft newt num with
                                   | Some newt' => Some (Fflips v0 Nflip newt' ff')
                                   | None => None
                                   end
  | _ => None
  end.*)

Fixpoint ft_set_sub (v : ProdVarOrder.t) (checkt : ftype) (newt : ftype) (num : N) : option ftype :=
  match checkt with
  | Gtyp _ => if (snd v) == num then Some newt else None
  | Atyp atyp n => if (((N.to_nat (snd v)) - 1- (N.to_nat num)) mod (num_ref atyp)) == 0
                   then (* 比较atyp与newt是否match, 取较大的更新Atyp *)
                    Some (Atyp newt n)
                   else (* 继续找atyp中的结构 *)
                    let n' := ((N.to_nat (snd v)) - 1- (N.to_nat num)) / (num_ref atyp) in
                    match ft_set_sub v atyp newt (N.add num (N.of_nat (n' * (num_ref atyp)))) with
                    | Some natyp => Some (Atyp natyp n)
                    | None => None
                    end
  | Btyp ff => match ft_set_sub_f v ff newt num with
              | Some newf => Some (Btyp newf)
              | None => None
              end
  end
with ft_set_sub_f (v : ProdVarOrder.t) (ff : ffield) (newt : ftype) (num : N) : option ffield :=
  (* changes the (v-num)th field of ff.
     If (v-num) == 1, then the first field is changed from implicit-width to explicit-width.
     If (v-num) == 2, 3, ... 1+size_of_ftype (type of first fieldd), then some subfield of the first field is changed.
     If (v-num) > 1+size_of_ftype (type of first field), then a subsequent field of ff is changed. *)
  match ff with
  | Fflips v0 Nflip ft ff' => if (snd v) == (N.add num 1%num) (* 找到被更新的标号, 所对应的field *)
                              then (* 比较Btyp现有对应位置上的ftype和待更新的newt是否match, 取较大的更新Btyp *)
                                Some (Fflips v0 Nflip newt ff') (* 修改当前field的type, ff'不变 *)
                              else if (snd v) > (N.add num (N.of_nat (num_ref ft))) (* 不在该field中, 找下一个field *)
                                   then match ft_set_sub_f v ff' newt (N.add num (N.of_nat (num_ref ft))) with
                                      | Some newf => Some (Fflips v0 Nflip ft newf)
                                      | None => None
                                      end
                                   else (* 在field v0中 *)
                                   match ft_set_sub v ft newt num with
                                   | Some newt' => Some (Fflips v0 Nflip newt' ff')
                                   | None => None
                                   end
  | _ => None
  end.

Fixpoint list_gref (n : nat) (pv : ProdVarOrder.t) (checkt : ftype) : option (seq ProdVarOrder.t) := 
  match n with
  | 0 => Some nil
  | S m => match list_gref m pv checkt, ft_find_sub (fst pv, N.add (snd pv) (N.of_nat n)) checkt N0 with
          | Some ls, Some (Gtyp _) => Some ((fst pv, N.add (snd pv) (N.of_nat n)) :: ls)
          | Some ls, Some _ => Some ls
          | _, None => None
          | None, _ => None
          end
  end.

Fixpoint expr2varlist (expr : HiFP.hfexpr) (tmap : ft_pmap) (ls : seq (seq ProdVarOrder.t)) : option (seq (seq ProdVarOrder.t)) :=
  (* Prepends to ls the list of variable/component identifiers accessed by the expression expr.
     tmap is used to look up the identifiers.
     DNJ: I think parameter ls is superfluous, it seems to be never used.  It could be replaced by [::]. *)
  match expr with
  | Econst _ _ => Some ls
  | Eref ref => match ref2pvar ref tmap with
                | Some pv => match ft_find (fst pv, N0) tmap with
                            | Some checkt => match ft_find_sub pv checkt N0 with
                                            | Some (Gtyp _) => Some ([::pv] :: ls)
                                            | Some aggt => match list_gref (num_ref aggt) pv checkt with
                                                          | Some nls => Some (nls::ls)
                                                          | None => None
                                                          end
                                            | None => None
                                            end
                            | None => None
                            end
                | None => None
                end
  | Eprim_unop _ e1 => expr2varlist e1 tmap ls
  | Eprim_binop _ e1 e2 => match expr2varlist e1 tmap ls with
                          | Some ls' => expr2varlist e2 tmap ls'
                          | _ => None
                          end
  | Evalidif e1 e2 => match expr2varlist e1 tmap ls with
                      | Some ls' => expr2varlist e2 tmap ls'
                      | _ => None
                      end
  | Ecast _ e => expr2varlist e tmap ls
  | Emux e1 e2 e3 => match expr2varlist e1 tmap ls with
                    | Some ls' => match expr2varlist e2 tmap ls' with
                                  | Some ls'' => expr2varlist e3 tmap ls'' 
                                  | None => None
                                  end
                    | _ => None
                    end
  end.
  
Fixpoint drawe (n : nat) (lhsl : seq ProdVarOrder.t) (rhsl : seq (seq ProdVarOrder.t)) newg : option (ProdVarOrder.t -> seq ProdVarOrder.t) := 
  match n with
  | 0 => Some newg
  | S m => match drawe m lhsl rhsl newg with
          | Some g' => match nth_error lhsl m with
                      | Some v => fold_left (fun tg rhs => match tg, nth_error rhs m with
                                                          | Some tg', Some r => Some (updg v (r :: (tg' v)) tg')
                                                          | _, _ => None
                                                          end) rhsl (Some g')
                      | None => None
                      end
          | None => None
          end
  end.

Definition drawel (v : ProdVarOrder.t) (el : seq HiFP.hfexpr) (tmap : ft_pmap) (newg : ProdVarOrder.t -> seq ProdVarOrder.t) (vertices : seq ProdVarOrder.t) : option ((ProdVarOrder.t -> seq ProdVarOrder.t) * (seq ProdVarOrder.t)) :=
  (* recursively draw dependencies in el for element v *)
  (* v: vertex in the dependency graph that is updated
     el: list of expressions that need to be considered for adding dependency edges
     tmap: map of (known) types of components
     newg: current edges in the dependency graph
     vertices: current vertices in the dependency graph
     Return value: a pair (edges in the dependency graph, vertices in the dependency graph)
     containing additionally the dependencies from el *)
  match fold_left (fun ls e => match ls, (expr2varlist e tmap nil) with
        | Some ls', Some l' => Some (ls' ++ l')
        | _, _=> None
    end) el (Some nil) with
  | Some rhsl => match ft_find (fst v, N0) tmap with
              | Some checkt => let lhs := match ft_find_sub v checkt N0 with
                                    | Some (Gtyp _) => Some [::v]
                                    | Some aggt => list_gref (num_ref aggt) v checkt 
                                    | None => None
                                end in match lhs with
                                | Some lhsl => match drawe (length lhsl) lhsl rhsl newg with
                                              | Some g' => Some (g', lhsl ++ concat rhsl)
                                              | None => None
                                              end
                                | None => None
                                end
              | None => None
              end
  | None => None
  end.

Definition InferWidth_ref (v : ProdVarOrder.t) (checkt : ftype) (newt : ftype) : option ftype :=
  match ft_find_sub v checkt N0 with
  | Some oldt => match infer_implicit oldt newt with
                | Some nt => ft_set_sub v checkt nt N0
                | None => None
                end
  | None => None
  end.

Definition testbty := (Btyp (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 0)) 2) (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 0)) 2) Fnil))).
(*Compute (InferWidth_ref (N0, 4%num) testbty (exist ftype_not_implicit_width (Atyp (Gtyp (Fuint 2)) 2) I) N0).
Compute (InferWidth_ref (N0, 3%num) testbty (exist ftype_not_implicit_width (Gtyp (Fuint 2)) I) N0).*)

(*Definition InferWidth_fun' (v : ProdVarOrder.t) (e : HiFP.hfexpr) (tmap : ft_pmap) : option ft_pmap :=
(* updates the width of v in tmap so that it is at least the width of the expression. *)
  match type_of_e e tmap with 
  | Some newt => match ft_find (fst v, N0) tmap with
                | Some ft => (* 不论是否subfield，都应该在tmap已声明，否则是新的node *)
                  if (snd v) == N0 then (* 当v在tmap中有已存v, 是直接被声明的变量 *)
                    match infer_implicit ft newt with
                    | Some nt => Some (ft_add v nt tmap)
                    | None => None (* type不match，没有新的正确tmap *)
                    end
                  else (* subfield *)
                    match InferWidth_ref v ft newt N0 with
                    | Some nt => Some (ft_add (fst v, N0) nt tmap)
                    | None => None
                    end
                | None => (* node *)
                  if (snd v) == N0 (* 新node声明时一定为（_,0） *)
                    then Some (ft_add v (explicit_to_ftype newt) tmap)
                  else None
                end
  | None => None
  end.*)

Fixpoint max_ftlist (l : seq ftype_explicit) (init : ftype): option ftype :=
  match l with
  | nil => Some init
  | t :: tl => match max_ftlist tl init with
              | Some t' => infer_implicit (explicit_to_ftype t) t'
              | None => None
              end
  end.
  
Fixpoint fil_ftlist (l : seq (option ftype_explicit)) : option (seq ftype_explicit) :=
  match l with
  | nil => Some [::]
  | None :: tl => None
  | (Some t) :: tl => match fil_ftlist tl with
                      | Some tl' => Some (t :: tl')
                      | None => None
                      end
  end.

Definition InferWidth_fun (v : ProdVarOrder.t) (el : seq HiFP.hfexpr) (tmap : ft_pmap) : option ft_pmap :=
(* updates the width of v in tmap so that it is at least the width of the expressions in list el. *)
  match fil_ftlist (map (fun e => type_of_e e tmap) el) with
  | Some eftl => match ft_find (fst v, N0) tmap with
                | Some init => match ft_find_sub v init 0 with
                              | Some initt => match max_ftlist eftl initt with
                                              | Some nt => match InferWidth_ref v init nt with
                                                          | Some nt0 => Some (ft_add (fst v, N0) nt0 tmap)
                                                          | None => None
                                                          end
                                              | None => None
                                              end
                              | None => None
                              end 
                | None => None
                end
  | None => None
  end.
(*
  match el with
  | nil => Some tmap
  | e :: etl => match InferWidth_fun' v e tmap with
                | Some newtm => InferWidth_fun v etl newtm
                | None => None
                end
  end.
*)
(* wire a : { b : UInt, c : SInt }
   wire x : UInt
   c <= SInt<3>(2)
   x <= AsUInt(c)
   b <= x + UInt(1).

   This should be handled in the order: a.b, x, a.c. *)

Fixpoint InferWidths_fun (od : seq ProdVarOrder.t) (var2exprs : var2exprsmap) (tmap : ft_pmap) : option ft_pmap :=
(* od contains the (implicit-width) ground-type subcomponents in topological order.
   (It is ok if od contains other components, but it is not necessary.)
   var2exprs is a map that maps every ground-type subcomponent to a list of expressions (namely expressions that the (sub)component is connected from).
   tmap is the map of types for every component that has been defined (but there are no separate entries for subcomponents);
   the result is a modified tmap, which ensures that the width of every implicit-width component is large enough. *)
  match od with
  | nil => Some tmap
  | vhd :: vtl => match module_graph_vertex_set_p.find vhd var2exprs with (* infer the width of vhd according to its connections *)
                | None => InferWidths_fun vtl var2exprs tmap (* vhd is not connected in the stmt_seq, go on inference on vtl *)
                | Some el => match InferWidth_fun vhd el tmap with 
                            (* vhd is connected to several exprs, compute the width of exprs sequentially, update the largest width for vhd in tmap. *)
                            | Some tmap' => InferWidths_fun vtl var2exprs tmap'
                            | None => None
                            end
                end
  end.

(* Correctness theorem for InferWidths_fun:
   If od is topologically sorted (for var2exprs),
   then the result of InferWidths_fun is a tmap
   that ensures all width constraints for implicit-type connect statements (those in var2exprs) are met.

   Corollary:
   If a module graph has the widths indicated in the result of InferWidths_fun
   (and the correct connection trees),
   then it is a semantic of the corresponding module.

Calculation process:

F = FInmod name ports statements ---> calculate the topological order of dependencies ---> InferWidths_fun ---> result tmap
           :                                                                                                     :
           :                                                                                                     :
           :                                                                                                     :
   module graph set                                                                    contains an element vm with these widths




FInmod name ports statements ---> use tmap to make widths explicit ---> FInmod name ports' statements' = F'
                                                                                     :
                                                                                     :
                                                                                     :
                                                                              module graph vm'

module graph vm' is very similar to the element vm; the only difference is that vm' has explicit widths.

vm = (make_vm_implicit F vm')


Lemma InferWidths_fun_correct:
forall (od : seq ProdVarOrder.t) (var2exprs : var2exprsmap) (tmap : ft_pmap),
   TopoSort.respects_topological_order (fun o : ProdVarOrder.t =>
                                        match module_graph_vertex_set_p.find o var2exprs with
                                        | Some expr_seq => match drawel o expr_seq tmap (fun _ => [::]) [::] with
                                                           | Some (new_edges, _) => new_edges o
                                                           | None => [::]
                                                           end
                                        | None => [::]
                                        end)
                                       od ->
   forall o : ProdVarOrder.t,
      match ft_find o tmap, module_graph_vertex_set_p.find o var2exprs with
      | Some otype, Some expr_seq => forall expr : HiFP.hfexpr, expr \in expr_seq ->
                                        match type_of_e expr tmap with
                                        | Some exprtype => ftype_equiv otype (explicit_to_ftype exprtype)
                                        (* tmap assigns compatible types to o and expr (ignoring width constraints) *)
                                        | None => true
                                        end
      | _, _ => True
      end ->
   match InferWidths_fun od var2exprs tmap with
   | Some newtm => forall o : ProdVarOrder.t,
                      match ft_find o newtm, module_graph_vertex_set_p.find o var2exprs with
                      | Some newotype, Some expr_seq => forall expr : HiFP.hfexpr, expr \in expr_seq ->
                                                           match type_of_e expr newtm with
                                                           | Some newexprtype => connect_type_compatible newotype newexprtype
                                                           (* newtm assigns compatible types to o and expr, including the width constraints *)
                                                           | None => true
                                                           end
                      | _, _ => True
                      end
   | None => True
   end.
*)

Lemma ft_find_add : forall v ft tmap, ft_find v (ft_add v ft tmap) = Some ft.
Proof.
Admitted.

(*Lemma type_of_e_dpdcy : forall v e tmap el nt, expr2varlist e tmap nil = Some el -> ~ v \in el -> type_of_e e (ft_add v nt tmap) = type_of_e e tmap.
Proof.
Admitted.*)

Lemma num_ref_eq : forall checkt nt0, ftype_equiv checkt nt0 -> num_ref checkt = num_ref nt0
with num_ref_eq_f : forall checkf nf0, fbtyp_equiv checkf nf0 -> num_ff checkf = num_ff nf0.
Proof.
  clear num_ref_eq.
  elim.
  intro gt.
  elim.
  intros gt0 Heq.
  simpl; done.
  intros; simpl in H0; discriminate.
  intros; simpl in H; discriminate.

  intros f H n.
  elim.
  intros; simpl in H0; discriminate.
  intros f0 H' n0 Heq; clear H'.
  simpl; simpl in Heq.
  move /andP : Heq => [Hn Heq].
  move /eqP : Hn => Hn.
  rewrite Hn.
  apply H in Heq; rewrite Heq; done.
  intros; simpl in H; discriminate.

  intro f. 
  elim.
  intros; simpl in H; discriminate.
  intros; simpl in H; discriminate.
  intro f0.
  simpl; intro Heq; apply num_ref_eq_f in Heq.
  rewrite Heq; done.

  clear num_ref_eq_f.
  elim.
  intros.
  simpl in H.
  case Hnf0 : nf0; rewrite Hnf0 in H; try discriminate; try done.
  intros v fl ft ff Heq.
  elim.
  intros.
  simpl in H. 
  case Hfl : fl; rewrite Hfl in H; discriminate.
  intros v0 fl0 ft0 ff0 H' Heq0; clear H'.
  simpl.
  simpl in Heq0.
  case Hfl : fl; rewrite Hfl in Heq0.
  case Hfl0 : fl0; rewrite Hfl0 in Heq0; try discriminate.
  move /andP : Heq0 => [Heq0 Heq1].
  move /andP : Heq0 => [_ Heq2].
  apply num_ref_eq in Heq2.
  apply Heq in Heq1.
  rewrite Heq1 Heq2; done.
  case Hfl0 : fl0; rewrite Hfl0 in Heq0; try discriminate.
  move /andP : Heq0 => [Heq0 Heq1].
  move /andP : Heq0 => [_ Heq2].
  apply num_ref_eq in Heq2.
  apply Heq in Heq1.
  rewrite Heq1 Heq2; done.
Qed.

Lemma set_find_sub : forall checkt nt a nt0 n, ft_set_sub a checkt nt n = Some nt0 -> ftype_equiv checkt nt0 -> ft_find_sub a nt0 n = Some nt
with set_find_sub_f : forall checkf nf a nf0 n, ft_set_sub_f a checkf nf n = Some nf0 -> fbtyp_equiv checkf nf0 -> ft_find_ff a nf0 n = Some nf.
Proof.
  clear set_find_sub.
  elim.
  intro f.
  intros nt a nt0 n Hset Heq.
  simpl in Heq.
  simpl in Hset.
  case Ha : (a.2 == n); rewrite Ha in Hset; try discriminate.
  inversion Hset; clear Hset H0.
  case Hnt0 : (nt0) => [f0||]; rewrite Hnt0 in Heq; try discriminate.
  simpl; rewrite Ha; done.

  intros f Hg fn. 
  intros nt a nt0 n Hset Heq.
  simpl in Hset.
  case Ha : ((N.to_nat a.2 - 1 - N.to_nat n) mod num_ref f == 0); rewrite Ha in Hset.
  inversion Hset; clear Hset.
  rewrite /ft_find_sub.
  assert (num_ref f = num_ref nt).
  rewrite -H0 in Heq.
  simpl in Heq.
  move /andP : Heq => [_ Heq].
  apply num_ref_eq; done.
  rewrite -H Ha; clear H; done.
  case Hset' : (ft_set_sub a f nt (n + N.of_nat ((N.to_nat a.2 - 1 - N.to_nat n) / num_ref f * num_ref f))) => [natyp|]; 
    rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  simpl.
  assert (num_ref f = num_ref natyp).
  rewrite -H0 in Heq.
  simpl in Heq.
  move /andP : Heq => [_ Heq].
  apply num_ref_eq; done.
  rewrite -H Ha; clear H.
  apply Hg with (nt := nt) (a := a) (nt0 := natyp); try done.
  rewrite -H0 in Heq.
  simpl in Heq.
  move /andP : Heq => [_ Heq]; done. 

  intros f nt a nt0 n Hset Heq.
  simpl in Hset.
  case Hset' : (ft_set_sub_f a f nt n) => [newf|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  simpl.
  apply set_find_sub_f in Hset'.
  rewrite Hset'; done.
  rewrite -H0 in Heq.
  simpl in Heq; done.

  clear set_find_sub_f.
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

  case Hset' : (ft_set_sub a f0 nf n) => [newt'|]; rewrite Hset' in Hset; try discriminate.
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
  done. 
Qed.

Lemma ft_set_sub_eq : forall checkt nt' a nt0 n init, ft_find_sub a checkt n = Some init -> ftype_equiv init nt' -> ft_set_sub a checkt nt' n = Some nt0 -> ftype_equiv checkt nt0
with ft_set_sub_eq_f : forall checkf nf' a nf0 n init, ft_find_ff a checkf n = Some init -> ftype_equiv init nf' -> ft_set_sub_f a checkf nf' n = Some nf0 -> fbtyp_equiv checkf nf0.
Proof.
  clear ft_set_sub_eq.
  elim.
  intro f.
  elim. 
  intros.
  simpl in H.
  case Ha : (a.2 == n); rewrite Ha in H; try discriminate.
  inversion H; clear H.
  rewrite -H3 in H0; simpl in H0.
  simpl in H1; rewrite Ha in H1.
  inversion H1; clear H1.
  simpl; done.
  intros.
  simpl in H0.
  case Ha : (a.2 == n0); rewrite Ha in H0; try discriminate.
  inversion H0; clear H0.
  rewrite -H4 in H1; simpl in H1; discriminate.
  intros.
  simpl in H.
  case Ha : (a.2 == n); rewrite Ha in H; try discriminate.
  inversion H; clear H.
  rewrite -H3 in H0; simpl in H0; discriminate.

  (* set aggt *)
  intros f H n.
  intros nt a nt0 cnt init Hfind Heq Hset.
  simpl in Hset.
  simpl in Hfind.
  case Ha : ((N.to_nat a.2 - 1 - N.to_nat cnt) mod num_ref f == 0); rewrite Ha in Hset Hfind.
  inversion Hset; clear Hset.
  inversion Hfind; clear Hfind.
  simpl.
  apply rwP with (P := (n == n) /\ ftype_equiv init nt).
  apply andP.
  split; done.
  case Hset' : (ft_set_sub a f nt (cnt + N.of_nat ((N.to_nat a.2 - 1 - N.to_nat cnt) / num_ref f * num_ref f))) => [natyp|]; 
  rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  simpl.
  apply H with (init := init) in Hset'; try done.
  apply rwP with (P := (n == n) /\ ftype_equiv f natyp).
  apply andP.
  split; done.

  (* set btyp *)
  intros f nt a nt0 cnt init Hfind Heq Hset.
  simpl in Hfind.
  simpl in Hset.
  case Hfind' : (ft_find_ff a f cnt) => [newf|]; rewrite Hfind' in Hfind; try discriminate.
  case Hset' : (ft_set_sub_f a f nt cnt) => [nf|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  simpl.
  inversion Hfind; clear Hfind.
  rewrite H1 in Hfind'.
  apply ft_set_sub_eq_f with (nf' := nt) (a := a) (n := cnt) (init := init); try done.
  
  (* field *)
  clear ft_set_sub_eq_f.
  induction checkf.
  intros.
  simpl in H; discriminate.
  intros nt a nf0 cnt init Hfind Heq Hset.
  simpl in Hfind.
  simpl in Hset.
  case Hf : f; rewrite Hf in Hset; try discriminate.
  case Ha : (a.2 == (cnt + 1)%num); rewrite Ha in Hfind Hset.
  inversion Hfind; inversion Hset; clear Hfind Hset.
  simpl.
  apply rwP with (P := (v == v) && ftype_equiv init nt /\ fbtyp_equiv checkf checkf).
  apply andP.
  split; try done.
  apply rwP with (P := (v == v) /\ ftype_equiv init nt).
  apply andP.
  split; try done.
  admit.
  case Ha' : ((cnt + N.of_nat (num_ref f0))%num < a.2); rewrite Ha' in Hfind Hset.
  case Hset' : (ft_set_sub_f a checkf nt (cnt + N.of_nat (num_ref f0))) => [newf|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  simpl.
  apply rwP with (P := (v == v) && ftype_equiv f0 f0 /\ fbtyp_equiv checkf newf).
  apply andP.
  split; try done.
  apply rwP with (P := (v == v) /\ ftype_equiv f0 f0).
  apply andP.
  split; try done.
  admit.
  specialize IHcheckf with (nf' := nt) (a := a) (init := init).
  apply IHcheckf with (nf0 := newf) in Hfind; done.
  case Hset' : (ft_set_sub a f0 nt cnt) => [newf|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  simpl.
  apply rwP with (P := (v == v) && ftype_equiv f0 newf /\ fbtyp_equiv checkf checkf).
  apply andP.
  split; try done.
  apply rwP with (P := (v == v) /\ ftype_equiv f0 newf).
  apply andP.
  split; try done.
  apply ft_set_sub_eq with (nt' := nt) (a := a) (n := cnt) (init := init); try done.
  admit.
Admitted.

Lemma infer_compatible : forall te otype nt, infer_implicit te otype = Some nt -> connect_type_compatible nt (make_ftype_explicit otype)
with infer_compatible_f : forall te (f : ffield) (nf : ffield),
infer_implicit (Btyp f) te = Some (Btyp nf) -> connect_type_compatible_fields nf (make_ffield_explicit f).
Proof.
  clear infer_compatible.
  elim.
  intro f. 
  elim.
  (* ground match ground *)
  case Hgt : f => [w'|w'|w'|w'|||]; move => ogt nt Hinfer.
  (* te = Gtyp (uint w') *)
  - case Hogt : ogt => [ow'|ow'|ow'|ow'|||]; rewrite Hogt in Hinfer; simpl in Hinfer; try discriminate.
    (* otype = Gtyp (uint ow') *)
    inversion Hinfer as [Hinfer']; clear Hinfer.
    simpl; done.
  (* te = Gtyp (sint w') *)
  - case Hogt : ogt => [ow'|ow'|ow'|ow'|||]; rewrite Hogt in Hinfer; simpl in Hinfer; try discriminate.
    (* otype = Gtyp (sint ow') *)
    inversion Hinfer as [Hinfer']; clear Hinfer.
    simpl; done.
  (* te = Gtyp (uint_implicit w') *)
  - case Hogt : ogt => [ow'|ow'|ow'|ow'|||]; rewrite Hogt in Hinfer; simpl in Hinfer; try discriminate.
    inversion Hinfer as [Hinfer']; clear Hinfer.
    simpl.
    rewrite Nat.max_comm.
    specialize Nat.le_max_l with (n := w') (m := ow').
    admit.
  (* te = Gtyp (sint_implicit w') *)
  - case Hogt : ogt => [ow'|ow'|ow'|ow'|||]; rewrite Hogt in Hinfer; simpl in Hinfer; try discriminate.
    inversion Hinfer as [Hinfer']; clear Hinfer.
    simpl.
    rewrite Nat.max_comm.
    specialize Nat.le_max_l with (n := w') (m := ow').
    admit.
  (* te = Gtyp Fclock *)
  - case Hogt : ogt => [ow'|ow'|ow'|ow'|||]; rewrite Hogt in Hinfer; simpl in Hinfer; try discriminate.
    inversion Hinfer as [Hinfer']; clear Hinfer.
    simpl; done.
  (* te = Gtyp Freset *)
  - case Hogt : ogt => [ow'|ow'|ow'|ow'|||]; rewrite Hogt in Hinfer; simpl in Hinfer; try discriminate.
    inversion Hinfer as [Hinfer']; clear Hinfer.
    simpl; done.
  (* te = Gtyp Fasyncreset *)
  - case Hogt : ogt => [ow'|ow'|ow'|ow'|||]; rewrite Hogt in Hinfer; simpl in Hinfer; try discriminate.
    inversion Hinfer as [Hinfer']; clear Hinfer.
    simpl; done.
  (* array match ground *)
  intros; simpl in H0.
  case H' : f; rewrite H' in H0; try discriminate.
  (* bundle match ground *)
  intros. simpl in H. 
  case H' : f; rewrite H' in H; try discriminate. 

  intros f Ho n.
  elim.
  (* ground match array *)
  intros. simpl in H; try discriminate.
  (* array match array *)
  intros; clear H infer_compatible_f.
  simpl in H0.
  case Heq : (n == n0); rewrite Heq in H0; try discriminate.
  case Hinfer : (infer_implicit f f0) => [nt'|]; rewrite Hinfer in H0; try discriminate.
  inversion H0 as [H0']; clear H0 H0'.
  apply Ho in Hinfer; clear Ho.
  move : Heq Hinfer.
  admit.
  (* bundle match array *)
  intros. simpl in H; discriminate.

  intro f. 
  elim.
  (* ground match bundle *)
  intros. simpl in H; try discriminate.
  (* array match bundle *)
  intros. simpl in H0; discriminate.
  (* bundle match bundle *)
  intros.
  generalize H; simpl in H.
  case Hinfer : (infer_implicit_fields f f0) => [nf|]; rewrite Hinfer in H; try discriminate.
  inversion H; clear H1 H.
  specialize infer_compatible_f with (f := f) (nf := nf) (te := (Btyp f0)).
  intro.
  apply infer_compatible_f in H; move : H.
  admit.

  (* proof of infer_compatible_f *)
  clear infer_compatible_f.
  elim.
  (* bundle match gtyp *)
  intros. simpl in H; discriminate.
  (* bundle match array *)
  intros. simpl in H0; discriminate.
  (* bundle match bundle *)
  intros. simpl in H.
  case Hinferf : (infer_implicit_fields f0 f) => [nf'|]; rewrite Hinferf in H; try discriminate.
  inversion H as [H']; clear H.
  specialize infer_compatible with (otype := (Btyp f)) (te := Btyp f0) (nt := Btyp nf').
  simpl in infer_compatible; rewrite Hinferf in infer_compatible.
  admit.
Admitted.

(*Lemma infer_implicit_correct : forall te' otype te  p nt, te = (exist ftype_not_implicit_width te' p) -> infer_implicit otype te = Some nt -> 
ftype_equiv otype te' -> connect_type_compatible nt te
with infer_implicit_f_correct : forall (f0 : ffield) (f : ffield) (te : {x : ftype | ftype_not_implicit_width x}) (p : ftype_not_implicit_width (Btyp f)) (nt : ftype),
te = exist ftype_not_implicit_width (Btyp f) p -> infer_implicit (Btyp f0) te = Some nt ->
ftype_equiv (Btyp f0) (Btyp f) -> connect_type_compatible nt te.
Proof.
  clear infer_implicit_correct.
  elim.
  intro f. 
  elim.
  (* ground match ground *)
  case Hgt : f => [w'|w'|w'|w'|||]; move => ogt te p nt Hte Hinfer Heq; simpl in p; try done.
  (* te' = Gtyp (uint w') *)
  - case Hogt : ogt => [ow'|ow'|ow'|ow'|||]; rewrite Hogt Hte in Hinfer; simpl in Hinfer; try discriminate.
    (* otype = Gtyp (uint ow') *)
    inversion Hinfer as [Hinfer']; clear Hinfer.
    rewrite Hte. 
    simpl; done.
    (* otype = Gtyp (uint_implicit ow') *)
    inversion Hinfer as [Hinfer']; clear Hinfer.
    rewrite Hte.
    simpl. 
    rewrite Nat.max_comm.
    specialize Nat.le_max_l with (n := w') (m := ow').
    admit.
  (* te' = Gtyp (sint w') *)
  - case Hogt : ogt => [ow'|ow'|ow'|ow'|||]; rewrite Hogt Hte in Hinfer; simpl in Hinfer; try discriminate.
    (* otype = Gtyp (sint ow') *)
    inversion Hinfer as [Hinfer']; clear Hinfer.
    rewrite Hte. 
    simpl; done.
    (* otype = Gtyp (sint_implicit ow') *)
    inversion Hinfer as [Hinfer']; clear Hinfer.
    rewrite Hte.
    simpl. 
    rewrite Nat.max_comm.
    specialize Nat.le_max_l with (n := w') (m := ow').
    admit.
  (* te' = Gtyp Fclock *)
  - case Hogt : ogt => [ow'|ow'|ow'|ow'|||]; rewrite Hogt Hte in Hinfer; simpl in Hinfer; try discriminate.
    (* otype = Gtyp Fclock *)
    inversion Hinfer as [Hinfer']; clear Hinfer.
    rewrite Hte. 
    simpl; done.
  (* te' = Gtyp Freset *)
  - case Hogt : ogt => [ow'|ow'|ow'|ow'|||]; rewrite Hogt Hte in Hinfer; simpl in Hinfer; try discriminate.
    (* otype = Gtyp Freset *)
    inversion Hinfer as [Hinfer']; clear Hinfer.
    rewrite Hte. 
    simpl; done.
  (* te' = Gtyp Fasync *)
  - case Hogt : ogt => [ow'|ow'|ow'|ow'|||]; rewrite Hogt Hte in Hinfer; simpl in Hinfer; try discriminate.
    (* otype = Gtyp Fasync *)
    inversion Hinfer as [Hinfer']; clear Hinfer.
    rewrite Hte. 
    simpl; done.
  
  (* array match ground *)
  intros; simpl in H2; discriminate.
  (* bundle match ground *)
  intros; simpl in H1; discriminate.

  intros f Ho n.
  elim.
  (* ground match array *)
  intros. simpl in H1; discriminate.
  (* array match array *)
  intros; clear H.
  simpl in H2.
  rewrite H0 in H1; simpl in H1.
  move /andP : H2 => [H2 H3].
  rewrite H2 in H1; simpl in H1.
  case Hinfer : (infer_implicit f0 (exist ftype_not_implicit_width f p)) => [nt0|]; rewrite Hinfer in H1; try discriminate.
  inversion H1 as [H1']; clear H1.
  rewrite H0.
  simpl.
  simpl in p.
  specialize Ho with (otype := f0) (te := exist ftype_not_implicit_width f p) (p := p) (nt := nt0).
  rewrite Ho; try done.
  rewrite (eq_refl n); done.
  (* bundle match array *)
  intros. simpl in H1; discriminate.

  
  intro f. 
  elim.
  (* ground match bundle *)
  intros. simpl in H1; discriminate.
  (* array match bundle *)
  intros. simpl in H2; discriminate.
  (* bundle match bundle *)
  intros.
  apply infer_implicit_f_correct with (f0 := f0) (f := f) (p := p); try done.

  clear infer_implicit_f_correct.
  elim.
  elim.
  intros; rewrite H in H0; simpl in H0.
  inversion H0 as [H0']; clear H0.
  rewrite H; simpl; done.
  intros. simpl in H2. discriminate.
  intros v fl ft ff Hf.
  elim.
  intros. simpl in H1; case Hfl : fl; rewrite Hfl in H1; discriminate. 
  intros; clear H.


  simpl in H2.
  case Hfl : fl; rewrite Hfl in H2; case Hf0 : f; rewrite Hf0 in H2; try discriminate.
  rewrite H0 Hf0 Hfl in H1; simpl in H1; discriminate.
  move /andP : H2 => [H3 H4].
  move /andP : H3 => [H2 H3].
  rewrite H0 Hf0 Hfl in H1; simpl in H1.
  rewrite H2 in H1.
  case Hinfer : (infer_implicit ft (exist ftype_not_implicit_width f0 (proj1 p))) => [nt0|]; rewrite Hinfer in H1; try discriminate.
  case Hinfer' : (infer_implicit_fields ff (exist ffield_not_implicit_width f1 (proj2 p))) => [nf0|]; rewrite Hinfer' in H1; try discriminate.
  inversion H1 as [H1']; clear H1.
  rewrite H0.
  simpl.
  rewrite Hf0.
  apply rwP with (P := (v == v0) &&
    connect_type_compatible nt0
      (exist ftype_not_implicit_width f0 (proj1 p)) /\
    connect_type_compatible_fields nf0
      (exist ffield_not_implicit_width f1 (proj2 p))).
  apply andP.
  split.
  apply rwP with (P := (v == v0) /\
    connect_type_compatible nt0
      (exist ftype_not_implicit_width f0 (proj1 p))).
  apply andP.
  split; try done.
  apply infer_implicit_correct with (te' := f0) (otype := ft) (te := exist ftype_not_implicit_width f0 (proj1 p)) (p := (proj1 p)) (nt := nt0); try done.

  simpl in p.
  assert (connect_type_compatible_fields nf0 (exist ffield_not_implicit_width f1 (proj2 p)) = 
  connect_type_compatible (Btyp nf0) (exist ftype_not_implicit_width (Btyp f1) (proj2 p))).
  simpl; done.
  rewrite H.
  specialize Hf with (f := f1) (te := exist ftype_not_implicit_width (Btyp f1) (proj2 p)) (p := proj2 p) (nt := Btyp nf0).
  apply Hf; try done.
  simpl.
  rewrite Hinfer'; done.
  Admitted.

Lemma InferWidth_fun_correct':
forall (v : ProdVarOrder.t) (expr : HiFP.hfexpr) (tmap : ft_pmap),
  match InferWidth_fun' v expr tmap with
  | Some newtm => match ft_find v tmap, ft_find v newtm with
                  | Some otype, Some newotype => 
                      match type_of_e expr tmap, type_of_e expr newtm with
                      | Some exprtype, Some newexprtype => ftype_equiv otype (explicit_to_ftype exprtype) -> connect_type_compatible newotype newexprtype
                      | _, _ => True
                      end
                  | _,_ => True
                  end
  | None => True
  end.
Proof.
  intros.
  case Hinfer : (InferWidth_fun' v expr tmap) => [newtm|]; try done.
  case Hdcl : (ft_find v tmap) => [otype|]; try done.
  case Hdcl' : (ft_find v newtm) => [newotype|]; try done.
  rewrite /InferWidth_fun' in Hinfer; simpl in Hinfer; rewrite Hdcl in Hinfer.
  case He : (type_of_e expr tmap) => [te|]; rewrite He in Hinfer; try done.
  case Hte : te => [te' p]; rewrite Hte in Hinfer.
  (*move : p Hte Hinfer He Hdcl.
  move : te' otype te.
  elim.
  move => f.
  elim.
  admit.
  admit.
  admit.
  intros f Ho n.
  elim.
  admit.
  intros.*)

  case Hnt : (infer_implicit otype (exist [eta ftype_not_implicit_width] te' p)) => [nt|]; rewrite Hnt in Hinfer; try discriminate.
  inversion Hinfer as [Hinfer']; clear Hinfer.
  rewrite -Hinfer' in Hdcl'.
  rewrite ft_find_add in Hdcl'.
  inversion Hdcl' as [Hdcl'']; clear Hdcl'.
  case He2varl : (expr2varlist expr tmap nil) => [el|].
  specialize type_of_e_dpdcy with (v := v) (e := expr) (tmap := tmap) (el := el) (nt := newotype); intro.
  rewrite H; try done. 
  rewrite He Hte. 
  simpl.
  rewrite -Hdcl''.
  apply infer_implicit_correct with (p := p); try done.
  admit.
  admit.
  Admitted.

Lemma infer_ftequiv : forall otype newt nt ft, infer_implicit otype newt = Some nt -> ftype_equiv otype ft -> ftype_equiv nt ft.
Admitted. 

Lemma compatible_keep : forall v expr_seq tmap newtm te nt newotype, InferWidth_fun v expr_seq tmap = Some newtm -> ft_find v tmap = Some nt -> connect_type_compatible nt te -> ft_find v newtm = Some newotype -> connect_type_compatible newotype te.
Admitted.

Lemma InferWidth_fun_correct:
forall (v : ProdVarOrder.t) (expr_seq : seq HiFP.hfexpr) (tmap : ft_pmap),
  (* all varaibles that v depends on should have been infered in tmap *)
  match InferWidth_fun v expr_seq tmap with
  | Some newtm => match ft_find v tmap, ft_find v newtm with
                  | Some otype, Some newotype => 
                    forall expr : HiFP.hfexpr, expr \in expr_seq ->
                      match type_of_e expr tmap, type_of_e expr newtm with
                      | Some exprtype, Some newexprtype => ftype_equiv otype (explicit_to_ftype exprtype) -> connect_type_compatible newotype newexprtype
                      (* tmap assigns compatible types to o and expr (ignoring width constraints) *)
                      (* newtm assigns compatible types to o and expr, including the width constraints *)
                      | _, _ => True
                      end
                  | _,_ => True
                  end
  | None => True
  end.
Proof.
  induction expr_seq.
  move => tmap.
  simpl.
  case Hdcl : (ft_find v tmap) => [otype|]; try done.

  move => tmap.
  case Hinfer : (InferWidth_fun v (a :: expr_seq) tmap) => [newtm|]; try done.
  simpl in Hinfer.
  case Hinfer' : (InferWidth_fun' v a tmap) => [newtm'|]; rewrite Hinfer' in Hinfer; try discriminate.
  case Hdcl : (ft_find v tmap) => [otype|]; try done.
  specialize IHexpr_seq with (tmap := newtm'); rewrite Hinfer in IHexpr_seq.
  generalize Hinfer'.
  rewrite /InferWidth_fun' in Hinfer'.
  intros Hinferv'.
  case Hte : (type_of_e a tmap) => [newt|]; rewrite Hte in Hinfer'; try discriminate.
  rewrite Hdcl in Hinfer'.
  case Hinfert : (infer_implicit otype newt) => [nt|]; rewrite Hinfert in Hinfer'; try discriminate.
  inversion Hinfer' as [Hinfer'']; clear Hinfer'.
  rewrite -Hinfer'' in IHexpr_seq; rewrite ft_find_add in IHexpr_seq.
  
  case Hdcl' : (ft_find v newtm) => [newotype|]; rewrite Hdcl' in IHexpr_seq; try done.
  intros expr Hexpr.
  rewrite in_cons in Hexpr.
  case Hin : (expr \in expr_seq).
  specialize IHexpr_seq with (expr := expr).
  rewrite Hin in IHexpr_seq.
  case Hdpdcy : (expr2varlist expr tmap [::]) => [el|].
  specialize type_of_e_dpdcy with (v := v) (e := expr) (tmap := tmap) (nt := nt) (el := el); intro.
  rewrite H in IHexpr_seq; clear H.
  case Hte' : (type_of_e expr tmap) => [exprtype|]; rewrite Hte' in IHexpr_seq; try done.
  case Hte'' : (type_of_e expr newtm) => [newexprtype|]; rewrite Hte'' in IHexpr_seq; try done.
  intro.
  apply IHexpr_seq; try done.
  specialize infer_ftequiv with (otype := otype) (newt := newt) (nt := nt) (ft := (explicit_to_ftype exprtype)); intro.
  apply H0; try done.
  done.
  admit.
  admit.

  rewrite Hin in Hexpr.
  case Ha : (expr == a); rewrite Ha in Hexpr; simpl in Hexpr; try discriminate.
  clear IHexpr_seq Hexpr Hin.
  specialize InferWidth_fun_correct' with (v := v) (expr := expr) (tmap := tmap); intro.
  move : (eqP Ha).
  clear Ha; intro Ha.
  rewrite -Ha in Hinferv'; rewrite Hinferv' Hdcl -{1}Hinfer'' in H; rewrite ft_find_add in H.
  case Hte' : (type_of_e expr tmap) => [exprtype|]; rewrite Hte' in H; try done.
  assert (Hte'' : type_of_e expr newtm' = Some exprtype).
  admit.
  assert (Hte''' : type_of_e expr newtm = Some exprtype).
  admit.
  rewrite Hte'' in H; rewrite Hte'''; intro; apply H in H0; clear H.
  apply compatible_keep with (v := v) (expr_seq := expr_seq) (tmap := newtm') (newtm := newtm) (nt := nt); try done.
  rewrite -Hinfer''.
  rewrite ft_find_add; done.

Admitted.*)

Lemma inferwidths_a' : forall a v expr_seq tmap tmap', InferWidth_fun v expr_seq tmap = Some tmap' -> 
  if (a == v) then True 
  else match ft_find (fst a, N0) tmap, ft_find (fst a, N0) tmap' with
        | Some ft, Some ft' => ft_find_sub a ft N0 = ft_find_sub a ft' N0
        | _, _ => True
        end.
Proof.
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
  admit. (* ft = ft' *)
Admitted.

Lemma inferwidths_ls : forall el a var2exprs tmap tmap' checkt checkt', InferWidths_fun el var2exprs tmap = Some tmap' -> 
  ~(a \in el) -> ft_find (fst a, N0) tmap' = Some checkt' -> ft_find (fst a, N0) tmap = Some checkt -> ft_find_sub a checkt N0 = ft_find_sub a checkt' N0.
Proof.
  elim.
  
Admitted.

(*Lemma ftype_equiv_dlvr : forall t1 t2 t3, ftype_equiv t1 t2 -> ftype_equiv t2 t3 -> ftype_equiv t1 t3.
Proof.

Admitted.*)

Lemma connect_compatible_dlvr : forall t1 t2 t3, connect_type_compatible t1 (make_ftype_explicit t2) -> connect_type_compatible t2 t3 -> connect_type_compatible t1 t3.
Proof.
  
Admitted.

(*Lemma mkexpli_eq : forall t1 t2, make_ftype_explicit t1 = make_ftype_explicit t2 -> t1 = t2.
Proof.

Admitted.*)

Lemma max_compatible : forall el tmap otype nt eftl, fil_ftlist [seq type_of_e e tmap | e <- el] = Some eftl -> max_ftlist eftl otype = Some nt -> forall expr exprtype, expr \in el -> type_of_e expr tmap = Some exprtype -> connect_type_compatible nt exprtype.
Proof.
  elim.
  intros.
  rewrite in_nil in H1; discriminate.
  intros hd tl H tmap init nt eftl Hl Hmax.
  simpl in Hl. 
  case Hhd : (type_of_e hd tmap) => [nht|]; rewrite Hhd in Hl; try discriminate.
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
  apply infer_compatible.
Admitted.

Lemma InferWidths_fun_correct:
forall (od : seq ProdVarOrder.t) (var2exprs : var2exprsmap) (tmap : ft_pmap),
  (* TopoSort.respects_topological_order (fun o : ProdVarOrder.t =>
                                        match module_graph_vertex_set_p.find o var2exprs with
                                        | Some expr_seq => match drawel o expr_seq tmap (fun _ => [::]) [::] with
                                                           | Some (new_edges, _) => new_edges o
                                                           | None => [::]
                                                           end
                                        | None => [::]
                                        end)
                                       od -> *)

  (*forall o : ProdVarOrder.t,
  match module_graph_vertex_set_p.find o var2exprs, ft_find o tmap with
  | Some expr_seq, Some otype => forall expr : HiFP.hfexpr, expr \in expr_seq ->
            match type_of_e expr tmap with
            | Some exprtype => ftype_equiv otype (explicit_to_ftype exprtype)
            | None => false
            end
  | _, _ => true
  end) ->*)

  match InferWidths_fun od var2exprs tmap with 
  | Some newtm => forall o : ProdVarOrder.t, o \in od ->
                  match module_graph_vertex_set_p.find o var2exprs, ft_find (fst o, N0) tmap, ft_find (fst o, N0) newtm with
                  | Some expr_seq, Some checkt, Some newcheckt => match ft_find_sub o checkt N0, ft_find_sub o newcheckt N0 with                  
                        | Some otype, Some newotype => 
                          forall expr : HiFP.hfexpr, expr \in expr_seq ->
                            match type_of_e expr tmap, type_of_e expr newtm with
                            | Some exprtype, Some newexprtype => ftype_equiv otype (explicit_to_ftype exprtype) -> connect_type_compatible newotype newexprtype
                            (* tmap assigns compatible types to o and expr (ignoring width constraints) *)
                            (* newtm assigns compatible types to o and expr, including the width constraints *)
                            | _, _ => True
                            end
                        | _, _ => True
                        end
                  | _,_,_ => True
                  end
  | None => True
  end.
Proof.
  induction od.
  move => var2exprs tmap (*Hpre*).
  simpl.
  move => v Hin.
  rewrite in_nil in Hin; discriminate.

  intros var2exprs tmap (*Hpre*). 
  simpl.
  case Hel : (module_graph_vertex_set_p.find a var2exprs) => [el|]; try done.
  case Hinfera : (InferWidth_fun a el tmap) => [tmap'|]; try done.
  specialize IHod with (var2exprs := var2exprs) (tmap := tmap').

  case Hinfers : (InferWidths_fun od var2exprs tmap') => [newtm|]; try done; rewrite Hinfers in IHod.
  intros o Hin; specialize IHod with (o := o).
  case Ho : (o == a).
    move : (eqP Ho); clear Ho IHod Hin; intro Ho.
    rewrite Ho Hel; clear Ho o Hel.
    case Ha0 : (ft_find (a.1, 0%num) tmap) => [checkt|]; try done.
    case Ha0new : (ft_find (a.1, 0%num) newtm) => [newcheckt|]; try done.
    case Ha : (ft_find_sub a checkt 0) => [otype|]; try done.
    case Hanew : (ft_find_sub a newcheckt 0) => [newotype|]; try done.
    case Ha0' : (ft_find (a.1, 0%num) tmap') => [checkt'|].
    assert (ft_find_sub a checkt' 0 = Some newotype).
    specialize inferwidths_ls with (el := od) (a := a) (var2exprs := var2exprs) (tmap := tmap') (tmap' := newtm) (checkt := checkt') (checkt' := newcheckt); intro.
    rewrite H; try done.
    admit. (* 不成环 *)
    case Ha' : (ft_find_sub a checkt' 0) => [otype'|].
    rewrite Ha' in H; inversion H; clear H; rewrite -H1; clear H1 Hanew newotype Ha0new newcheckt.
    intros expr Hin.
    assert (type_of_e expr newtm = type_of_e expr tmap').
    admit. (* 原因是 expr 仅依赖于 拓扑排序在a之前的变量，从tmap'到newtm仅改变拓扑排序在a之后的变量，故没有影响 *)
    rewrite H; clear H Hinfers newtm od var2exprs.
    case Hte : (type_of_e expr tmap) => [exprtype|]; try done.
    case Hte' : (type_of_e expr tmap') => [exprtype'|]; try done.
    intro Heq.
    rewrite /InferWidth_fun in Hinfera.
    case Hel : (fil_ftlist [seq type_of_e e tmap | e <- el]) => [eftl|]; rewrite Hel in Hinfera; try discriminate.
    rewrite Ha0 Ha in Hinfera.
    case Hmax : (max_ftlist eftl otype) => [nt|]; rewrite Hmax in Hinfera; try discriminate.
    case Hinferref : (InferWidth_ref a checkt nt) => [nt0|]; rewrite Hinferref in Hinfera; try discriminate.
    inversion Hinfera as [Htmap']; clear Hinfera; rewrite -Htmap' in Ha0'.
    rewrite ft_find_add in Ha0'; inversion Ha0' as [Hcheckt']; clear Ha0'.
    rewrite -Hcheckt' in Ha'.
    assert (exprtype = exprtype').
    admit.
    rewrite -H.
    clear Hte' H Hcheckt' Htmap' exprtype' checkt' tmap'.
    apply connect_compatible_dlvr with (t1 := otype') (t2 := nt) (t3 := exprtype).
    apply infer_compatible with (nt := otype') (otype := nt) (te := otype).
    rewrite /InferWidth_ref Ha in Hinferref.
    case Hinfer : (infer_implicit otype nt) => [nt'|]; rewrite Hinfer in Hinferref; try discriminate.
    rewrite -Ha'. symmetry; apply set_find_sub with (checkt := checkt); try done.
    apply ft_set_sub_eq with (nt' := nt') (a := a) (n := N0) (init := otype); try done.
    move : Hinfer.
    admit.
    (* apply infer_compatible. 还需要交换律*)
    
    apply max_compatible with (el := el) (expr := expr) (tmap := tmap) (otype := otype) (eftl := eftl); try done.

    (*move : otype' eftl nt nt0 Hel Hmax Hinferref Ha' expr exprtype Hin Hte Heq.
    induction el as [|hd tl].
    admit.
    intros.
    simpl in Hel.
    case Hthd : (type_of_e hd tmap) => [thd|]; rewrite Hthd in Hel; try discriminate.
    case Hel' : (fil_ftlist [seq type_of_e e tmap | e <- tl]) => [eftl'|]; rewrite Hel' in Hel; try discriminate.
    inversion Hel as [Heftl]; clear Hel.
    rewrite -Heftl in Hmax; simpl in Hmax.
    case Hmax' : (max_ftlist eftl' otype) => [nt'|]; rewrite Hmax' in Hmax; try discriminate.
    case Hinferref' : (InferWidth_ref a checkt nt' 0) => [nt0'|].
    case Ha'0 : (ft_find_sub a nt0' 0) => [otype0|].

    rewrite in_cons in Hin. 
    case Hhd : (expr == hd); rewrite Hhd in Hin.
    admit.
    case Hin' : (expr \in tl); rewrite Hin' in Hin; try discriminate; clear Hin Hthd.
    specialize IHtl with (otype' := otype0) (eftl := eftl') (nt := nt') (nt0 := nt0') (expr := expr) (exprtype := exprtype).
    apply connect_compatible_dlvr with (t1 := otype') (t2 := otype0) (t3 := exprtype).
    apply find_infer_sub with (init := otype) in Hinferref. rewrite Hinferref in Ha'; clear Hinferref.
    (*inversion Ha' as [Hinferref]; clear Ha'; rewrite -Hinferref.*)
    apply find_infer_sub with (init := otype) in Hinferref'. rewrite Hinferref' in Ha'0; clear Hinferref'.
    (*inversion Ha'0 as [Hinferref']; clear Ha'0; rewrite -Hinferref'; clear Hinferref Hinferref'.*)
    move : Hmax.
    apply infer_compatible. (* 证明infer的正确性 重要！！ *)
    apply IHtl; try done. *)
    admit. (* None *)
    admit. (* None *)

    rewrite in_cons in Hin; rewrite Ho in Hin; simpl in Hin.
    apply IHod in Hin; clear IHod.
    case Hfindo : (module_graph_vertex_set_p.find o var2exprs) => [expr_seq|]; rewrite Hfindo in Hin; try done.
    specialize inferwidths_a' with (a := o) (v := a) (expr_seq := el) (tmap := tmap) (tmap' := tmap'); intro.
    apply H in Hinfera; clear H; rewrite Ho in Hinfera.
    case Ha0 : (ft_find (o.1, 0%num) tmap) => [checkt|]; rewrite Ha0 in Hinfera; try done.
    case Ha0' : (ft_find (o.1, 0%num) tmap') => [checkt'|]; rewrite Ha0' in Hinfera Hin; try done.
    rewrite -Hinfera in Hin.
    case Ha0new : (ft_find (o.1, 0%num) newtm) => [newcheckt|]; rewrite Ha0new in Hin; try done.
    case Ha : (ft_find_sub o checkt 0) => [otype|]; rewrite Ha in Hin; try done.
    case Hanew : (ft_find_sub o newcheckt 0) => [newotype|]; rewrite Hanew in Hin; try done.
    intros expr Hin'.
    apply Hin in Hin'; clear Hin.
    assert (type_of_e expr tmap' = type_of_e expr tmap).
    admit.
    rewrite -H; done.
    admit. (* None *)

    (* find a var2expr 为 None 时，用(fst a, N0)的连接更新整个 *)

Admitted.

Fixpoint drawg depandencyls (tmap : ft_pmap) (expli_reg : seq ProdVarOrder.t) (newg : ProdVarOrder.t -> seq ProdVarOrder.t) (vertices : seq ProdVarOrder.t) : option ((ProdVarOrder.t -> seq ProdVarOrder.t) * (seq ProdVarOrder.t)) :=
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

Definition InferWidths_transp (p : HiFP.hfport) (tmap : ft_pmap) : option HiFP.hfport :=
  (* changes the type in one port declaration, depending on the information in tmap, to an explicit-width type *)
  match p with
  | Finput v t => if (ftype_not_implicit t) then Some p
                  else (match ft_find v tmap with
                  | Some ft => (* if t has implicit width, update the hfport with ft and change it to explicit width *)
                                Some (Finput v (expli_ftype ft))
                  | _ => None
                  end)
  | Foutput v t => if (ftype_not_implicit t) then Some p
                  else (match ft_find v tmap with
                  | Some ft => (* if t has implicit width, update the hfport with ft and change it to explicit width *)
                                Some (Foutput v (expli_ftype ft))
                  | _ => None
                  end)
  end.

Fixpoint InferWidths_transps (ps : seq HiFP.hfport) (tmap : ft_pmap) : option (seq HiFP.hfport) :=
  (* changes the types in a sequence of port declarations, depending on the information in tmap, to explicit-width types *)
  match ps with
  | nil => Some nil
  | p :: tl => match InferWidths_transp p tmap, InferWidths_transps tl tmap with
                  | Some n, Some nss => Some (n :: nss)
                  | _, _ => None
                  end
  end.

Fixpoint InferWidths_transs (s : HiFP.hfstmt) (tmap : ft_pmap) : option HiFP.hfstmt :=
(* with infered tmap, transform the ports and declarations *)
  match s with
  | Sskip => Some s
  | Swire v t => if (ftype_not_implicit t) then Some s
                  else (match ft_find v tmap with
                  | Some ft => (* if t has implicit width, update the hfstmt with ft and change it to explicit width *)
                                Some (Swire v (expli_ftype ft))
                  | _ => None
                  end)
  | Sreg v r => if (ftype_not_implicit (type r)) then Some s
                else (match ft_find v tmap with
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
with InferWidths_transss (sts : HiFP.hfstmt_seq) (tmap : ft_pmap) : option HiFP.hfstmt_seq :=
  match sts with
  | Qnil => Some (Qnil ProdVarOrder.T)
  | Qcons s ss => match InferWidths_transs s tmap, InferWidths_transss ss tmap with
                  | Some n, Some nss => Some (Qcons n nss)
                  | _, _ => None
                  end
  end.

Definition emptyg : (ProdVarOrder.t -> seq ProdVarOrder.t) := (fun _ => [::]).

Definition InferWidths_m (m : HiFP.hfmodule) : option HiFP.hfmodule :=
  (* input : program, including ports and stmts *)
  match m with
  | FInmod v ps ss => let tmap := List.fold_left (fun tempm tempp => prepro_p tempp tempm) ps ft_empty in (* add variables in ports to ft_map *)
                      match prepro_stmts ss tmap (module_graph_vertex_set_p.empty (seq HiFP.hfexpr)) nil with (* add variables in stmt_dclrs to ft_map *)
                      | Some prepro => 
                                                   (* tmap' : all the expli/uninfered impli aggr&gtyp are stroed here
                                                      var2exprs : every connected elements are stored 
                                                      expli_reg : regs with explicit width, to avoid cyclic denpendency, do not draw its connections in graph *)
                                                   match drawg (module_graph_vertex_set_p.elements prepro.1.2) prepro.1.1 prepro.2 emptyg nil with
                                                   | Some thedraw => (* theg : new drawn graph
                                                                                 vertices : set for topo sort to start with *)
                                                                    match (TopoSort.topo_sort thedraw.2 thedraw.1) with
                                                                    | TopoSort.Sorted inferorder => match InferWidths_fun inferorder prepro.1.2 prepro.1.1 with
                                                                                            | Some newtm => (* newtm : all width infered tmap *)
                                                                                                            match InferWidths_transps ps newtm, InferWidths_transss ss newtm with
                                                                                                            | Some nps, Some nss => Some (FInmod v nps nss)
                                                                                                            | _, _ => None
                                                                                                            end
                                                                                            | None => None
                                                                                            end
                                                                    | _ => None
                                                                    end
                                                    | _ => None
                                                    end
                      | None => None
                      end
  | _ => None
  end.
(*
  (* test InferWidths_transps *)
  Definition p1 : pvar := (N.of_nat 1, N0).
  Definition tmap0 := ft_add p1 (Gtyp (Fuint_implicit 2)) ft_empty.
  Definition prt0 := Finput p1 (Gtyp (Fuint_implicit 0)).
  Compute (InferWidths_transps [:: prt0] tmap0).

  (* test InferWidths_transss *)
  Definition s0 := Swire p1 (Gtyp (Fuint_implicit 0)). (* test reg? *)
  Definition s01 := Sinvalid (Eid p1).
  Compute (InferWidths_transss (Qcons s0 (Qcons s01 (Qnil ProdVarOrder.T))) tmap0).

  (* test InferWidths_fun *)
  Definition ec0 := (HiFP.econst (Fuint 2) [::b1; b0]).
  Definition exprm0 := module_graph_vertex_set_p.add p1 [:: ec0] (module_graph_vertex_set_p.empty (seq HiFP.hfexpr)). 
  Definition tmap1 := ft_add p1 (Gtyp (Fuint_implicit 0)) ft_empty.
  Compute (match InferWidths_fun [:: p1] exprm0 tmap1 with 
          | Some nm => ft_find p1 nm
          | _ => None
          end).

  Definition p11 : pvar := (1%num, 1%num).
  Definition exprm1 := module_graph_vertex_set_p.add p11 [:: ec0] (module_graph_vertex_set_p.empty (seq HiFP.hfexpr)). 
  Definition tmap2 := ft_add p1 (Atyp (Gtyp (Fuint_implicit 0)) 2) ft_empty.
  Compute (match InferWidths_fun [:: p1; p11] exprm1 tmap2 with 
          | Some nm => ft_find p1 nm (* tmap中只存完整的aggr, 不存每个元素的ftype *)
          | _ => None
          end).

  Definition p12 : pvar := (1%num, 2%num).
  Definition exprm2 := module_graph_vertex_set_p.add p12 [:: ec0] (module_graph_vertex_set_p.empty (seq HiFP.hfexpr)). 
  Definition tmap3 := ft_add p1 (Btyp (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 0)) 2) Fnil)) ft_empty.
  Compute (match InferWidths_fun [::p1;p12] exprm2 tmap3 with 
          | Some nm => ft_find p1 nm 
          | _ => None
          end).
  Compute (match InferWidth_ff 2%num (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 0)) 2) Fnil) N0 (exist ftype_not_implicit_width (Gtyp (Fuint 2)) I) with 
          | Some ff => ff
          | _ => Fnil
          end). (* 只能找到field, 如果field里有array？ *)

  Definition tmap4 := ft_add p1 (Btyp (Fflips (2%num) Nflip (Btyp (Fflips (1%num) Nflip (Gtyp (Fuint_implicit 0)) Fnil)) Fnil)) ft_empty.
  Compute (match InferWidths_fun [::p1;p12] exprm2 tmap4 with 
          | Some nm => ft_find p1 nm 
          | _ => Some (Gtyp (Fuint 0))
          end).
  Compute (match InferWidth_ff 2%num (Fflips (2%num) Nflip (Btyp (Fflips (1%num) Nflip (Gtyp (Fuint_implicit 0)) Fnil)) Fnil) N0 (exist ftype_not_implicit_width (Gtyp (Fuint 2)) I) with 
          | Some ff => ff
          | _ => Fnil
          end).
  Compute (size_of_ftype (Btyp (Fflips (2%num) Nflip (Btyp (Fflips (1%num) Nflip (Gtyp (Fuint_implicit 0)) Fnil)) Fnil))).
  Compute (match InferWidth_ff 2%num (Fflips (2%num) Nflip (Btyp (Fflips (1%num) Nflip (Gtyp (Fuint_implicit 0)) Fnil)) Fnil) N0 (exist ftype_not_implicit_width (Gtyp (Fuint 2)) I) with 
          | Some ff => ff
          | _ => Fnil
          end).

  (* test prepro_p/prepro_stmts *)
  Definition p2 : pvar := (N.of_nat 2, N0).
  Definition p3 : pvar := (N.of_nat 3, N0).
  Definition prt1 := Finput p2 (Gtyp (Fuint 2)).
  Definition tmap5 := List.fold_left (fun tempm tempp => prepro_p tempp tempm) [:: prt1] ft_empty.
  Compute (ft_find p2 tmap5).

  Definition s3 := Sreg p1 (mk_freg (Gtyp (Fuint_implicit 0)) ((Econst ProdVarOrder.T) (Fuint 1) [:: b0]) (Rst ((Econst ProdVarOrder.T) (Fuint 1) [:: b1]) (Eprim_binop Badd (Eref (Eid p2)) ((Econst ProdVarOrder.T) (Fuint 1) [:: b1])))).
  Definition s4 := Swire p2 (Gtyp (Fuint_implicit 0)).
  Definition s5 := Sfcnct (Eid p2) ((Econst ProdVarOrder.T) (Fuint 2) [:: b1;b1]).
  Definition ec2 := (HiFP.econst (Fuint 4) [::b0;b1;b0;b1]).
  Definition s6 := Snode p3 ec2.
  Definition s7 := Sfcnct (Eid p1) (Eref (Eid p3)).
  Definition tmap6 := match prepro_stmts (Qcons s3 (Qcons s4 (Qcons s5 (Qcons s6 (Qcons s7 (Qnil ProdVarOrder.T)))))) ft_empty (module_graph_vertex_set_p.empty (seq HiFP.hfexpr)) nil with
                    | Some r => fst (fst r)
                    | _ => ft_empty
                    end.
  Compute (ft_find p3 tmap6).
  Definition em0 := match prepro_stmts (Qcons s3 (Qcons s4 (Qcons s5 (Qcons s6 (Qcons s7 (Qnil ProdVarOrder.T)))))) ft_empty (module_graph_vertex_set_p.empty (seq HiFP.hfexpr)) nil with
                    | Some r => snd (fst r)
                    | _ => module_graph_vertex_set_p.empty (seq HiFP.hfexpr)
                    end.
  Compute (module_graph_vertex_set_p.find p3 em0).
  Compute (module_graph_vertex_set_p.find p1 em0).
  Compute (module_graph_vertex_set_p.find p2 em0).
              
  Definition expreg0 := match prepro_stmts (Qcons s3 (Qcons s4 (Qcons s5 (Qcons s6 (Qcons s7 (Qnil ProdVarOrder.T)))))) ft_empty (module_graph_vertex_set_p.empty (seq HiFP.hfexpr)) nil with
                    | Some r => snd r
                    | _ => nil 
                    end.
  Compute expreg0.

  Definition s8 := Sreg p1 (mk_freg (Btyp (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 0)) 2) Fnil)) ((Econst ProdVarOrder.T) (Fuint 1) [:: b0]) (NRst ProdVarOrder.T)).
  Definition s9 := Swire p2 (Btyp (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint 2)) 2) Fnil)).
  Definition ec3 := (HiFP.econst (Fuint 4) [::b0;b1;b0;b1]).
  Definition s10 := Snode p3 ec3.
  Definition s11 := Sfcnct (Esubindex (Esubfield (Eid p1) 1%num) 1) (Eref (Eid p3)).
  Definition s12 := Sfcnct (Eid p1) (Eref (Eid p2)).
  Definition tmap7 := match prepro_stmts (Qcons s8 (Qcons s9 (Qcons s10 (Qcons s11 (Qcons s12 (Qnil ProdVarOrder.T)))))) ft_empty (module_graph_vertex_set_p.empty (seq HiFP.hfexpr)) nil with
                    | Some r => fst (fst r)
                    | _ => ft_empty
                    end.
  Compute (ft_find p1 tmap7).
  Definition em1 := match prepro_stmts (Qcons s8 (Qcons s9 (Qcons s10 (Qcons s11 (Qcons s12 (Qnil ProdVarOrder.T)))))) ft_empty (module_graph_vertex_set_p.empty (seq HiFP.hfexpr)) nil with
                    | Some r => snd (fst r)
                    | _ => module_graph_vertex_set_p.empty (seq HiFP.hfexpr)
                    end.
  Compute (module_graph_vertex_set_p.find p3 em1).
  Compute (module_graph_vertex_set_p.find p1 em1).
  Compute (module_graph_vertex_set_p.find p2 em1).
  Compute (module_graph_vertex_set_p.find (1%num, 3%num) em1).
              
  Definition expreg1 := match prepro_stmts (Qcons s8 (Qcons s9 (Qcons s10 (Qcons s11 (Qcons s12 (Qnil ProdVarOrder.T)))))) ft_empty (module_graph_vertex_set_p.empty (seq HiFP.hfexpr)) nil with
                    | Some r => snd r
                    | _ => nil 
                    end.
  Compute expreg1.

  (* test drawg *)
  Definition g1 := match drawg (module_graph_vertex_set_p.elements em0) tmap6 expreg0 emptyg nil with
                  | Some g' => fst g'
                  | _ => emptyg
                  end.
  Definition vertices0 := match drawg (module_graph_vertex_set_p.elements em0) tmap6 expreg0 emptyg nil with
                  | Some g' => snd g'
                  | _ => nil
                  end.

  Definition g2 := match drawg (module_graph_vertex_set_p.elements em1) tmap7 expreg1 emptyg nil with
                  | Some g' => fst g'
                  | _ => emptyg
                  end.
  Definition vertices1 := match drawg (module_graph_vertex_set_p.elements em1) tmap7 expreg1 emptyg nil with
                  | Some g' => snd g'
                  | _ => nil
                  end.
  (* test topo_sort *)
  Compute (g1 p3).
  Compute (g1 p2).
  Compute (g1 p1).
  Compute vertices0.
  Compute (TopoSort.topo_sort vertices0 g1).

  Compute (g2 p3).
  Compute (g2 p2).
  Compute (g2 p1).
  Compute vertices1.
  Compute (TopoSort.topo_sort vertices1 g2).

  Definition order0 := match (TopoSort.topo_sort vertices1 g2) with
                      | TopoSort.Sorted or => or
                      | _ => nil
                      end.

  Compute (match InferWidths_fun order0 em1 tmap7 with 
  | Some nm => ft_find p1 nm 
  | _ => None
  end).
*)

Lemma vm2newtm : forall newtm vm'' ps tmap nps, InferWidths_transps ps newtm = Some nps -> Sem_port nps vm'' -> 
                (forall ct' ct vm' ss nss, InferWidths_transss ss newtm = Some nss -> Sem_frag_stmts vm'' ct' nss vm' ct tmap -> 
                      (forall v0 p pv0 ft q, list_lhs_ref_p vm' v0 tmap = Some p -> ref2pvar v0 tmap = Some pv0 -> ft_find (fst pv0, N0) newtm = Some ft -> ft_find_sub pv0 ft N0 = Some q -> p.2 = q)
                    /\(forall e p q, list_rhs_expr_p e vm' ct tmap = Some p -> type_of_e e newtm = Some q -> q = p.1.1.2)).
Proof.
  
Admitted.

Definition vx_le (x y : vertex_type) : bool :=
  match x, y with
  | OutPort i, OutPort j
  | InPort i, InPort j 
  | Node i, Node j
  | Register i, Register j
  | Wire i, Wire j => if (not_implicit j) then true else (sizeof_fgtyp i) <= (sizeof_fgtyp j)
  | RegisterReset a r1, RegisterReset b r2 => if (not_implicit b) then true else ((sizeof_fgtyp a) <= (sizeof_fgtyp b))
  
  (*| Invalid a, Invalid b
  | Cast_UInt a, Cast_UInt b
  | Cast_SInt a, Cast_SInt b
  | Cast_Clock a, Cast_Clock b
  (*| Cast_Reset a, Cast_Reset b*)
  | Cast_Async a, Cast_Async b => (sizeof_fgtyp (explicit_to_fgtyp a)) <= (sizeof_fgtyp (explicit_to_fgtyp b))
  
  | Unop_cvt a, Unop_cvt b
  | Unop_neg a, Unop_neg b
  | Unop_not a, Unop_not b
  | Unop_andr a, Unop_andr b
  | Unop_orr a, Unop_orr b
  | Unop_xorr a, Unop_xorr b
  | Binop_sub a, Binop_sub b
  | Binop_div a, Binop_div b
  | Binop_lt a, Binop_lt b
  | Binop_leq a, Binop_leq b
  | Binop_gt a, Binop_gt b
  | Binop_geq a, Binop_geq b
  | Binop_eq a, Binop_eq b
  | Binop_neq a, Binop_neq b
  | Binop_and a, Binop_and b
  | Binop_or a, Binop_or b
  | Binop_xor a, Binop_xor b
  | Binop_add a, Binop_add b => (sizeof_fgtyp (arithmetic_to_fgtyp a)) <= (sizeof_fgtyp (arithmetic_to_fgtyp b))
  
  | Mux o, Mux w => (sizeof_fgtyp (explicit_to_fgtyp o)) <= (sizeof_fgtyp (explicit_to_fgtyp w))
  | Constant n1 a, Constant n2 b => (n1 == n2) && (a == b)
  | Unop_pad n1 a, Unop_pad n2 b 
  | Unop_shl n1 a, Unop_shl n2 b
  | Unop_shr n1 a, Unop_shr n2 b
  | Unop_head n1 a, Unop_head n2 b
  | Unop_tail n1 a, Unop_tail n2 b => ((sizeof_fgtyp (arithmetic_to_fgtyp a)) <= (sizeof_fgtyp (arithmetic_to_fgtyp b))) && (n1 == n2)
  | Unop_bits n1 n2 a, Unop_bits n3 n4 b => ((sizeof_fgtyp (arithmetic_to_fgtyp a)) <= (sizeof_fgtyp (arithmetic_to_fgtyp b))) && (n1 == n3) && (n2 == n4)
  | Binop_mul a b, Binop_mul c d
  | Binop_rem a b, Binop_rem c d 
  | Binop_cat a b, Binop_cat c d 
  | Binop_dshl a b, Binop_dshl c d
  | Binop_dshr a b, Binop_dshr c d => ((sizeof_fgtyp (arithmetic_to_fgtyp a)) <= (sizeof_fgtyp (arithmetic_to_fgtyp c))) && (b <= d)*)
  | _, _ => true
  end.

(*Definition vm_le (vm : module_graph_vertex_set_p.env) (vm' : module_graph_vertex_set_p.env) : bool := module_graph_vertex_set_p.equal vx_le vm' vm.*)

Lemma InferWidth_fun_eq : forall v el tmap tmap' checkt init ft initt eftl, InferWidth_fun v el tmap = Some tmap' -> 
  ft_find (fst v, N0) tmap' = Some checkt -> ft_find_sub v checkt 0 = Some ft -> 
  ft_find (fst v, N0) tmap = Some init -> ft_find_sub v init 0 = Some initt -> 
  fil_ftlist (map (fun e => type_of_e e tmap(*'*)) el) = Some eftl ->
  ftype_init_implicit initt -> max_ftlist eftl initt = Some ft .
Proof.
  intros v el tmap tmap' checkt init ft initt eftl Hinfer Hfind Hfind' Hinit Hinit' Hftlist.
  rewrite /InferWidth_fun in Hinfer.
  rewrite Hftlist Hinit Hinit' in Hinfer.
  case Hmax : (max_ftlist eftl initt) => [nt|]; rewrite Hmax in Hinfer; try discriminate.
  case Hinferref : (InferWidth_ref v init nt) => [nt0|]; rewrite Hinferref in Hinfer; try discriminate.
  inversion Hinfer; clear Hinfer.
  rewrite -H0 in Hfind.
  rewrite ft_find_add in Hfind.
  rewrite Hfind in Hinferref; clear Hfind.
  intro Himp. 
  rewrite -Hfind'.
  rewrite /InferWidth_ref Hinit' in Hinferref.
  case Hinfer : (infer_implicit initt nt) => [nft|]; rewrite Hinfer in Hinferref; try discriminate.
  apply set_find_sub in Hinferref.
  rewrite Hinferref.

  move : Himp Hinfer.
  admit.
  Search (ftype_equiv).
  apply ft_set_sub_eq with (nt' := nft) (a := v) (n := N0); done.
  Admitted.

(* stop here 
  intro v. 
  elim.
  intros tmap tmap' checkt init ft initt eftl Hinfer Hfind Hfind' Hinit Hinit' Hftlist.
  simpl in Hinfer; simpl in Hftlist.
  inversion Hftlist as [Hftlist']; clear Hftlist.
  simpl.
  inversion Hinfer; clear Hinfer.
  rewrite H0 Hfind in Hinit.
  inversion Hinit; clear Hinit.
  rewrite H1 Hinit' in Hfind'; done.

  intros e el H tmap tmap' checkt init ft initt eftl Hinfer Hfind Hfind' Hinit Hinit' Hftlist.
  simpl in Hinfer.
  case Hinfer' : (InferWidth_fun' v e tmap) => [newtm|]; rewrite Hinfer' in Hinfer; try discriminate.
  specialize H with (tmap := newtm) (tmap' := tmap') (checkt := checkt) (ft := ft).
  simpl in Hftlist.
  case He : (type_of_e e tmap') => [te|]; rewrite He in Hftlist; try discriminate.
  case Hftlist' : (fil_ftlist (map (fun e => type_of_e e tmap') el)) => [eftl'|]; rewrite Hftlist' in Hftlist; try discriminate.
  inversion Hftlist; clear Hftlist H1 eftl.
  simpl.
  case Ht' : (max_ftlist eftl' initt) => [t'|].
  specialize H with (eftl := eftl').
  rewrite /InferWidth_fun' in Hinfer'.
  assert (type_of_e e tmap = Some te). (* 由He *)
  admit.
  rewrite H0 in Hinfer'; clear H0.
  rewrite Hinit in Hinfer'.
  case Hv2 : (v.2 == N0); rewrite Hv2 in Hinfer'.
  move /eqP : Hv2 => Hv2.
  case Hinferi : (infer_implicit init te) => [nt|]; rewrite Hinferi in Hinfer'; try discriminate.
  inversion Hinfer'; clear Hinfer'.
  specialize H with (init := nt) (initt := nt).
  apply H in Hinfer; clear H; try done.
  rewrite -Hinfer.


  rewrite/infer_implicit in Hinferi.
  
  rewrite /InferWidth_fun in Hinfer.
  move : el Hel Hinfer.
  elim.
  admit.
  induction el as [|e tl].
  admit. (* 如果v0 in inferorder，应该有connection到v0，find不为nil *) 
  inversion Hinfer as [Hinfer']; clear Hinfer.
  simpl.
Admitted. *)


Definition vm_le (vm : module_graph_vertex_set_p.env) (vm' : module_graph_vertex_set_p.env) : Prop := 
  forall v, match module_graph_vertex_set_p.find v vm', module_graph_vertex_set_p.find v vm with
            | Some t', Some t => vx_le t' t
            | None, None => true
            | _, _ => false
            end.

Theorem InferWidths_correct :
(* Proves that InferWidth_fun preserves the semantics *)
   forall (F : HiFP.hfmodule) (vm' : module_graph_vertex_set_p.env) (ct : module_graph_connection_trees_p.env),
      match InferWidths_m F with
      | Some F' => Sem F' vm' ct -> (forall vm, Sem F vm ct -> vm_le vm' vm) 
      | _ => True
      end.
Proof.
  intro F. 
  case H : (InferWidths_m F) => [F'|]; try done.
  move => vm' ct Hsem' vm Hsem.
  rewrite /Sem in Hsem'; rewrite /Sem in Hsem.
  case Hm : F => [v pp ss|v' pp' ss'] ; rewrite Hm in H Hsem' Hsem; try done.
  rewrite /InferWidths_m in H.
  (* Inmod case *)
  clear Hm F.
  case Hprepro : (prepro_stmts ss
  (fold_left (fun tempm : ft_pmap => prepro_p^~ tempm) pp ft_empty)
  (module_graph_vertex_set_p.empty (seq HiFP.hfexpr)) [::]) => [prepro|]; rewrite Hprepro in H Hsem; try discriminate.
  case Hdrawg : (drawg (module_graph_vertex_set_p.elements (snd (fst prepro))) (fst (fst prepro)) (snd prepro) emptyg
  [::]) => [drawg|]; rewrite Hdrawg in H; try discriminate.
  case Htopo : (TopoSort.topo_sort drawg.2 drawg.1) => [inferorder||]; rewrite Htopo in H; try discriminate.
  case Hinfer : (InferWidths_fun inferorder prepro.1.2 prepro.1.1) => [newtm|]; rewrite Hinfer in H; try discriminate.
  case Htransp : (InferWidths_transps pp newtm) => [nps|]; rewrite Htransp in H; try discriminate.
  case Htranss : (InferWidths_transss ss newtm) => [nss|]; rewrite Htranss in H; try discriminate.  
  inversion H; rewrite -H1 in Hsem'. 
  clear H H1 F'.
  case Hprepron : (prepro_stmts nss
    (fold_left (fun tempm : ft_pmap => prepro_p^~ tempm) nps ft_empty)
    (module_graph_vertex_set_p.empty (seq HiFP.hfexpr)) [::]) => [prepron|]; rewrite Hprepron in Hsem'; try done.
  move : Hsem => [nvm_port [ct'0 [Hport Hstmts]]].
  move : Hsem' => [nvm_port' [ct' [Hport' Hstmts']]].

  assert (Hsem' : forall v, v \in inferorder -> match module_graph_vertex_set_p.find v prepro.1.2 with
                  | Some el => match ft_find (fst v, N0) newtm, ft_find (fst v, N0) prepro.1.1 with (* 若为implicit *)
                              | Some checkt, Some init => match ft_find_sub v checkt N0, ft_find_sub v init N0, (fil_ftlist (map (fun e => type_of_e e newtm) el)) with
                                          | Some ft, Some initt, Some eftl (* connection lhs的类型，可能subfield，可能agg/gtyp *) 
                                            => ftype_init_implicit initt -> max_ftlist eftl initt = Some ft
                                          | _, _, _ => false
                                          end
                              | _ ,_ => false
                              end
                  | _ => true
                  end).
  clear Hport' Hstmts' ct' nvm_port' Hport Hstmts ct'0 nvm_port Hprepron prepron Htranss nss Htransp nps.
  intros v0 Hin.
  assert (exists order1 order2, inferorder = order1 ++ (v0 :: order2) /\ ~ v0 \in order1 /\ ~ v0 \in order2).
  admit.
  clear Hin.
  move : H => [order1 [order2 [H [Horder1 Horder2]]]].
  rewrite H in Hinfer; rewrite /InferWidths_fun in Hinfer.
  case Hiner1 : (InferWidths_fun order1 prepro.1.2 prepro.1.1) => [tmap'|].
  assert (Hinfer2 : InferWidths_fun (v0 :: order2) prepro.1.2 tmap' = Some newtm).
  admit.
  clear Hinfer.
  simpl in Hinfer2.
  case Hel : (module_graph_vertex_set_p.find v0 prepro.1.2) => [el|]; rewrite Hel in Hinfer2; try done.
  case Hinfer : (InferWidth_fun v0 el tmap') => [newtm'|]; rewrite Hinfer in Hinfer2; try discriminate.
  
  specialize InferWidth_fun_eq; intro.

  specialize H0 with (v := v0) (el := el) (tmap := tmap') (tmap' := newtm').
  case Hfindv0 : (ft_find (v0.1, 0%num) newtm) => [checkt|].
  case Hfindv : (ft_find_sub v0 checkt 0) => [ft|].
  case Hfindv0' : (ft_find (v0.1, 0%num) newtm') => [checkt'|].
  case Hfindv' : (ft_find_sub v0 checkt' 0) => [ft'|].
  apply inferwidths_ls with (a := v0) (checkt := checkt') (checkt' := checkt) in Hinfer2; try done.
  rewrite -Hinfer2 Hfindv' in Hfindv.
  inversion Hfindv; clear Hfindv.
  rewrite -H2; clear H2 Hinfer2 Hfindv0 checkt ft.
  case Hfindv0 : (ft_find (v0.1, 0%num) prepro.1.1) => [checkt|].
  case Hfindv : (ft_find_sub v0 checkt 0) => [ft|].
  case Hfindv0'' : (ft_find (v0.1, 0%num) tmap') => [checkt''|].
  case Hfindv'' : (ft_find_sub v0 checkt'' 0) => [ft''|].
  apply inferwidths_ls with (a := v0) (checkt := checkt) (checkt' := checkt'') in Hiner1; try done.
  rewrite Hiner1 Hfindv'' in Hfindv.
  inversion Hfindv; clear Hfindv.
  rewrite -H2; clear H2 Hiner1 Hfindv0 checkt ft.

  case Hftlist : (fil_ftlist [seq type_of_e e newtm | e <- el]) => [eftl|].
  assert (fil_ftlist [seq type_of_e e newtm | e <- el] = fil_ftlist [seq type_of_e e tmap' | e <- el]).
  admit. 
  rewrite H1 in Hftlist; clear H1.
  apply H0 with (checkt := checkt') (init := checkt''); try done.
  admit. (* None *)
  admit. (* None *)
  admit. (* None *)
  admit. (* None *)
  admit. (* None *)
  admit. (* None *)
  admit. (* None *)
  admit. (* None *)
  admit. (* None *)
  admit. (* None *)


  assert (Hsem : forall v expr, Qin (Sfcnct v expr) ss ->
                 exists lhs, list_lhs_ref_p vm v prepro.1.1 = Some lhs ->
                 exists rhs, list_rhs_expr_p expr vm ct prepro.1.1 = Some rhs ->
                 connect_type_compatible lhs.2 rhs.1.1.2).
  clear Hsem' Hstmts' Hport' ct' nvm_port' Htransp nps Htranss Hprepron nss Htopo inferorder Hdrawg Hinfer drawg vm' newtm prepron Hprepro.
  clear Hport. 
  move : ss prepro nvm_port vm ct'0 ct Hstmts.
  elim. 
  admit.
  intros.
  assert ((Sfcnct v0 expr) = h \/ Qin (Sfcnct v0 expr) h0).
  admit. (* in_cons *)
  clear H0.
  (* case1 fcnct = h *)
  case H0 : ((Sfcnct v0 expr) == h).
  clear H.
  simpl in Hstmts.
  destruct Hstmts as [vm' [ct' [Hstmt _]]].
  move /eqP : H0 => H0.
  rewrite -H0 in Hstmt; clear H1.
  simpl in Hstmt.
  case He : expr; rewrite He in Hstmt.
  rewrite -He in Hstmt; rewrite -He.
  case Hlhs : (list_lhs_ref_p nvm_port v0 prepro.1.1) => [p|]; rewrite Hlhs in Hstmt; try done.
  case Hrhs : (list_rhs_expr_p expr nvm_port ct'0 prepro.1.1) => [q|]; rewrite Hrhs in Hstmt; try done.
  (* 取Hstmt第二项 *)
  exists p. 
  assert (list_lhs_ref_p vm v0 prepro.1.1 = list_lhs_ref_p nvm_port v0 prepro.1.1). (* 从nvm_port到vm不改变v0的type *)
  admit.
  case Hq' : (list_rhs_expr_p expr vm ct'0 prepro.1.1) => [q'|].
  exists q'.
  assert (q.1.1.2 = q'.1.1.2).
  admit.
  rewrite -H2; clear H2.
  admit. (* apply Hstmt *)
  admit. (* None *)
  admit. (* discriminate. Hstmt *)

  admit. (* 除了ref, 其他expr都一样 *)
  admit.
  admit.
  admit.
  admit.
  (* ref *)
  admit. (* implementation 添加ref *)

  (* case2 fcnct in h0 *)
  case H' : (Qin (Sfcnct v0 expr) h0).
  simpl in Hstmts.
  destruct Hstmts as [vm' [ct' [_ Hstmts]]].
  apply H with (nvm_port := vm') (ct'0 := ct'); try done.
  rewrite H' in H1. 
  admit. (* H0 H1 discriminate. *)


  rewrite /vm_le.
  intro ref.
  (*assert (H : module_graph_vertex_set_p.find ref vm = Some (vt ft) -> exists ft', module_graph_vertex_set_p.find ref vm' = Some (vt ft')).*)
  assert (forall vx, module_graph_vertex_set_p.mem vx vm -> ?)

  case Hfind : (module_graph_vertex_set_p.find ref vm) => [t|].
  case Hfind' : (module_graph_vertex_set_p.find ref vm') => [t'|].
    case Ht : t => [ft|||||||||||||||||||||||||||||||||||||||||]. 
    case Ht' : t' => [ft'|||||||||||||||||||||||||||||||||||||||||]; simpl; try done.
    case Himp : (not_implicit ft'); try done.
    (*assert (exists v, ref v中包含ref, 且ss中有v的connection)*)
Admitted.

Theorem InferWidths_correct' :
(* Proves that InferWidth_fun preserves the semantics *)
   forall (F : HiFP.hfmodule) (vm' : module_graph_vertex_set_p.env) (ct : module_graph_connection_trees_p.env),
      match InferWidths_m F with
      | Some F' => Sem F' vm' ct -> Sem F (make_vm_implicit F vm') ct
      
      (*forall (F : HiFP.hfmodule),
      match InferWidths_m F with
      | Some F' => forall vm vm' ct, Sem F vm ct -> Sem F' vm' ct -> 
                    vm' <= vm (* forall v, v in vm /\ v in vm', width v vm' <= width v vm *) *)

      (*exists vm : module_graph_vertex_set_p.env, (* make_vm_implicit vm' F : 找所有implicit declaration, 改 vertex_type *)
                                       Sem F vm ct /\ module_graph_vertex_set_p.Equal vm' (make_vm_explicit vm) *)
      | _ => True
      end.
Proof.
   (* The following initial fragment of a proof is based on Keyin's earlier work.
      David has written it for an old version of the correctness theorem
      (before considering how to split it up). *)
  intro F. 
  case H : (InferWidths_m F) => [F'|]; try done.
  move => vm' ct.
  rewrite /Sem.
  case Hm : F => [v pp ss|v' pp' ss'] ; try (rewrite Hm /InferWidths_m in H ; done).
  (* Inmod case *)

  rewrite Hm /InferWidths_m in H.
  clear Hm F.
  case Hprepro : (prepro_stmts ss
  (fold_left (fun tempm : ft_pmap => prepro_p^~ tempm) pp ft_empty)
  (module_graph_vertex_set_p.empty (seq HiFP.hfexpr)) [::]) => [prepro|]; rewrite Hprepro in H; try discriminate.
  case Hdrawg : (drawg (module_graph_vertex_set_p.elements (snd (fst prepro))) (fst (fst prepro)) (snd prepro) emptyg
  [::]) => [drawg|]; rewrite Hdrawg in H; try discriminate.
  case Htopo : (TopoSort.topo_sort drawg.2 drawg.1) => [inferorder||]; rewrite Htopo in H; try discriminate.
  case Hinfer : (InferWidths_fun inferorder prepro.1.2 prepro.1.1) => [newtm|]; rewrite Hinfer in H; try discriminate.
  case Htransp : (InferWidths_transps pp newtm) => [nps|]; rewrite Htransp in H; try discriminate.
  case Htranss : (InferWidths_transss ss newtm) => [nss|]; rewrite Htranss in H; try discriminate.  
  inversion H.
  clear H H1 F'.
  case Hprepron : (prepro_stmts nss
    (fold_left (fun tempm : ft_pmap => prepro_p^~ tempm) nps ft_empty)
    (module_graph_vertex_set_p.empty (seq HiFP.hfexpr)) [::]) => [prepron|] ; try done.
  move => [nvm_port [ct' [Hport Hstmts]]].
  exists (make_vm_implicit (FInmod v pp (Qnil HiFirrtl.ProdVarOrder.T)) nvm_port).
  exists ct'.
  split.
  clear Hprepro Hstmts Hprepron Hinfer Htranss.
  move : pp newtm nvm_port nps Htransp Hport.
  induction pp.
  - intros newtm nvm_port nps Htransp Hport.
    simpl in Htransp.
    simpl.
    inversion Htransp as [Hnps]; clear Htransp.
    rewrite -Hnps in Hport.
    simpl in Hport; done.
  - intros newtm nvm_port nps Htransp Hport.
    simpl.
    case Ha : a => [var t| var t].
    (* input *)
    apply rwP with (P := Sem_port pp
        (remove_t
          (fold_left make_p_implicit pp
              (make_p_implicit nvm_port
                (Finput (var:=HiFirrtl.ProdVarOrder.T) var t))) var.1
          (size_of_ftype t)) /\
      Sem_inport t var.1 0
        (fold_left make_p_implicit pp
          (make_p_implicit nvm_port
              (Finput (var:=HiFirrtl.ProdVarOrder.T) var t)))).
    apply andP.
    simpl in Htransp.
    case Htransa : (InferWidths_transp a newtm) => [ap|]; rewrite Htransa in Htransp; try discriminate.
    case Htransp' : (InferWidths_transps pp newtm) => [nps'|]; rewrite Htransp' in Htransp; try discriminate.
    inversion Htransp as [Hnps]; clear Htransp.
    rewrite -Hnps in Hport.
    simpl in Hport.
    rewrite Ha in Htransa; simpl in Htransa.
    case Hat : (ftype_not_implicit t); rewrite Hat in Htransa.
      - inversion Htransa as [Hap]; clear Htransa; rewrite -Hap in Hport.
      move /andP : Hport => [Hport Hinport].
      split.
      specialize IHpp with (newtm := newtm) (nvm_port := (remove_t nvm_port var.1 (size_of_ftype t))) (nps := nps').
      assert ((make_vm_implicit
        (FInmod v pp (Qnil HiFirrtl.ProdVarOrder.T))
        (remove_t nvm_port var.1 (size_of_ftype t))) = (remove_t
          (fold_left make_p_implicit pp
            (make_p_implicit nvm_port
                (Finput (var:=HiFirrtl.ProdVarOrder.T) var t))) var.1
          (size_of_ftype t))).
      admit.
      rewrite -H.
      apply IHpp; done.
      admit.
      - case Hfind : (ft_find var newtm) => [ft|]; rewrite Hfind in Htransa; try discriminate.
      inversion Htransa as [Hap]; clear Htransa; rewrite -Hap in Hport.
      move /andP : Hport => [Hport Hinport].
      specialize IHpp with (newtm := newtm) (nvm_port := (remove_t nvm_port var.1 (size_of_ftype (expli_ftype ft)))) (nps := nps').
      (* 基本同上 *)
      admit.
    (* output同上 *)
    admit.
  specialize vm2newtm with (ps := pp) (newtm := newtm) (vm'' := nvm_port) (tmap := prepro.1.1) (nps := nps); intro Hvm'.
  rewrite Htransp Hport in Hvm'.
  clear Hprepro Hprepron Hdrawg Htransp Hport.
  move : ss nvm_port ct' ct nss Htranss Hstmts Hvm'.
  (*elim.*)
  induction ss.
  - simpl.
    intros.
    inversion Htranss as [Hnss]; clear Htranss.
    rewrite -Hnss in Hstmts; simpl in Hstmts.
    admit.
  - intros.
    simpl in Htranss.
    case Htransh : (InferWidths_transs h newtm) => [hs|]; rewrite Htransh in Htranss; try discriminate.
    case Htranss' : (InferWidths_transss ss newtm) => [nss'|]; rewrite Htranss' in Htranss; try discriminate.
    inversion Htranss as [Hnss]; clear Htranss.
    rewrite -Hnss in Hstmts.
    case Hh : h => [|v0 t|v0 r|v0 m|v0 v1|v0 n|v0 e|v0|c s1 s2].
    - simpl.
      rewrite Hh in Htransh; simpl in Htransh.
      inversion Htransh as [Hhs]; clear Htransh.
      rewrite -Hhs in Hstmts; simpl in Hstmts.
      destruct Hstmts as [nvm_port' Hstmts].
      destruct Hstmts as [ct'0 [[Hnvm_port Hct'] Hstmts]].
      exists (fold_left make_p_implicit pp nvm_port).
      exists ct'.
      split; try done.
      rewrite -Hnvm_port -Hct' in Hstmts.
      specialize IHss with (nvm_port := nvm_port) (ct := ct) (nss := nss').
      simpl in IHss; apply IHss; try done.
    - simpl.
      rewrite Hh in Htransh; simpl in Htransh.
      case Hth : (ftype_not_implicit t); rewrite Hth in Htransh.
      (* explicit *)
      inversion Htransh as [Hhs]; clear Htransh.
      generalize Hstmts.
      rewrite -Hhs in Hstmts. simpl in Hstmts.
      destruct Hstmts as [nvm_port' Hstmts].
      destruct Hstmts as [ct'0 [[Hnv0 Hv0] Hstmts]].
      move => Hstmts'.
      exists (fold_left make_p_implicit pp nvm_port'). (* make wire implicit *)
      exists ct'.
      split.
      split.
      (* part1 *)
      clear Hv0 Hstmts.
      intros.
      case Ht : (v1 != v0.1); try done.
      specialize Hnv0 with (v0 := v1) (n0 := n0); rewrite Ht in Hnv0.
      destruct Hnv0 as [Hnv0 _].
      split; try reflexivity.
      admit.
      (* part2 *)
      clear Hnv0 Hstmts.
      split; try reflexivity.
      destruct Hv0 as [Hv0 Hct'0].
      intro.
      specialize Hv0 with (n := n).
      case Hn : (nth_error (vtype_list t [::]) n) => [nv|]; rewrite Hn in Hv0.
        destruct Hv0 as [Hv0vm Hv0ct].
        admit.
        destruct Hv0 as [Hv0vm Hv0ct].
        split; try done.
        admit.
      (* part3 *)
      destruct Hv0 as [Hv0 Hct'0].
      specialize IHss with (nvm_port := nvm_port') (ct := ct) (ct' := ct'0) (nss := nss').
      simpl in IHss.
      apply IHss in Htranss'; try done.
      admit. (* 由Hth, t没有implicit, 故从Htranss'推出相等 *)

      intros.
      apply Hvm' with (vm' := vm'0) (ct' := ct'1) (ct := ct0) (ss := (Qcons h ss0)) (nss := (Qcons hs nss0)); try done.
      simpl; rewrite Hh; simpl; rewrite Hth H1 Hhs; done.
      simpl.
      exists nvm_port'.
      exists ct'1.
      split; try done. 
      (* rewrite -Hhs; simpl.
      split; try done. *) admit. (* 重要！！由hs为dcl知ct'1不变, nvm_port到nvm_port'由Hstmts Hstmts'知 *)

      (* implicit 基本一样 *)
      case Hfindv0 : (ft_find v0 newtm) => [ft|]; rewrite Hfindv0 in Htransh; try discriminate.
      inversion Htransh as [Hhs]; clear Htransh.
      rewrite -Hhs in Hstmts; simpl in Hstmts.
      destruct Hstmts as [nvm_port' Hstmts].
      destruct Hstmts as [ct'0 [[Hnv0 Hv0] Hstmts]].
      exists (fold_left make_p_implicit pp nvm_port'). (* make wire implicit *)
      exists ct'.
      split.
      split.
      (* part1 *)
      clear Hv0 Hstmts.
      intros.
      case Ht : (v1 != v0.1); try done.
      specialize Hnv0 with (v0 := v1) (n0 := n0); rewrite Ht in Hnv0.
      destruct Hnv0 as [Hnv0 _].
      split; try reflexivity.
      admit.
      (* part2 *)
      clear Hnv0 Hstmts.
      split; try reflexivity.
      destruct Hv0 as [Hv0 Hct'0].
      intro.
      specialize Hv0 with (n := n).
      assert ((vtype_list (expli_ftype ft) [::]) = (vtype_list t [::])).
      admit.
      rewrite H in Hv0; clear H.
      case Hn : (nth_error (vtype_list t [::]) n) => [nv|]; rewrite Hn in Hv0.
        destruct Hv0 as [Hv0vm Hv0ct].
        admit.
        destruct Hv0 as [Hv0vm Hv0ct].
        split; try done.
        admit.
      (* part3 *)
      destruct Hv0 as [_ Hct'0].
      clear Hnv0.
      specialize IHss with (nvm_port := nvm_port') (ct := ct) (ct' := ct'0) (nss := nss').
      simpl in IHss.
      apply IHss in Htranss'; try done.
      admit. (* 由Hth, t没有implicit, 故从Htranss'推出相等 *)
      admit.
    - (* reg *)
      admit.
    - (* mem *)
      admit.
    - (* inst *)
      admit.
    - (* node *)
      admit.
    - (* fcnct *)
      rewrite Hh in Htransh; simpl in Htransh.
      inversion Htransh as [Hhs]; clear Htransh.
      rewrite -Hhs in Hstmts.
      generalize Hstmts; simpl in Hstmts.
      destruct Hstmts as [nvm_port' Hstmts].
      destruct Hstmts as [ct'0 [Hv0 Hstmts]].
      intro Hstmts'.
      simpl.
      exists (fold_left make_p_implicit pp nvm_port'). (* 要求这里的vm中这句用到的变量都为newtm中的位宽 *)
      (* nvm_port'比nvm_port添加了rhs expr中的点 *)
      exists ct'0.
      split.
      case He : e => [t c| c e1 | u e1 | op e1 e2 | c e1 e2 | c e1 | r2 ]; rewrite He in Hv0.
      - (* const *)
        rewrite -He; rewrite -He in Hv0.
        case Hlft0 : (list_lhs_ref_p nvm_port v0 prepron.1.1) => [p0|]; rewrite Hlft0 in Hv0; try done.
        assert (list_lhs_ref_p nvm_port v0 prepron.1.1 = Some p0 -> exists p, list_lhs_ref_p (fold_left make_p_implicit pp nvm_port) v0 prepro.1.1 = Some p /\ p.1 = p0.1 (* /\  p0.2的位宽等于p.2的位宽 *)).
        admit.
        apply H in Hlft0; clear H.
        destruct Hlft0 as [p [Hlft0 Hpeq']].
        rewrite Hlft0.
        case Hp0 : p0 => [input_list0 ft_ref0]; rewrite Hp0 in Hv0.
        case Hrght0 : (list_rhs_expr_p e nvm_port ct' prepron.1.1) => [q0|]; rewrite Hrght0 in Hv0; try done.
        case Hp : p => [input_list ft_ref].
        assert (list_rhs_expr_p e nvm_port ct' prepron.1.1 = Some q0 -> 
          exists q, list_rhs_expr_p e (fold_left make_p_implicit pp nvm_port) ct' prepro.1.1 = Some q /\ 
          q.1.1.1 = q0.1.1.1 /\ q.2 = q0.2).
        admit.
        apply H in Hrght0; clear H.
        destruct Hrght0 as [q [Hrght0 [Hqeq' Hqeq2]]].
        rewrite Hrght0.
        case Hq0 : q0 => [[[output_list0 ft_expr0] nvmap0] nctree0]; rewrite Hq0 in Hv0; destruct Hv0 as [Hvm0 [Hft0 [Hct0 Hct1]]].
        case Hq : q => [[[output_list ft_expr] nvmap] nctree].
        split.
        (* subgoal1 *)
        admit. (* nvmap0 nvmap 区别是nvmap0全为explicit, nvmap可能有implicit. 并且前有Heq: Equal nvm_port nvm_port' *)
        split.
        (* subgoal2 *)
        clear Hct0 Hct1 Hvm0 Hft0 Hq0 nctree0 nvmap0 ft_expr0 output_list0 Hqeq' q0 Hp0 input_list0 ft_ref0 Hpeq' Hqeq2 p0.
        (* ft_ref0总为explicit, 故前提中没有关于位宽的有效约束 *)
        specialize InferWidths_fun_correct with (od := inferorder) (var2exprs := prepro.1.2) (tmap := prepro.1.1); intro.
        rewrite Hinfer in H.
        case Hv0ref : (ref2pvar v0 prepro.1.1) => [pv0|].
        specialize H with (o := pv0).
        assert (Hpv0in : pv0 \in inferorder).
        admit.
        apply H in Hpv0in; clear H.
        assert (exists expr_seq, (module_graph_vertex_set_p.find pv0 prepro.1.2 = Some expr_seq /\ 
                e \in expr_seq)).
        (* 因为有Hh : h = Sfcnct v0 e, prepro.1.2 和 prepron.1.2 中一定有expr_seq, 且 e \in expr_seq *)
        admit.
        destruct H as [expr_seq [Hexpr_seq Hein]]; rewrite Hexpr_seq in Hpv0in.
        assert (exists checkt, ft_find (pv0.1, 0%num) prepro.1.1 = Some checkt).
        admit. (* pv0在电路中被连接时, 应该已经被声明 *)
        destruct H as [checkt Hfindv0]; rewrite Hfindv0 in Hpv0in.
        assert (exists newcheckt, ft_find (pv0.1, 0%num) newtm = Some newcheckt).
        admit. (* pv0在电路中被连接时, 应该已经被声明 *)
        destruct H as [newcheckt Hfindv0']; rewrite Hfindv0' in Hpv0in.
        assert (exists otype, ft_find_sub pv0 checkt N0 = Some otype).
        admit. (* pv0在电路中被连接时, 应该已经被声明 *)
        destruct H as [otype Hfindv]; rewrite Hfindv in Hpv0in.
        assert (exists newotype, ft_find_sub pv0 newcheckt N0 = Some newotype).
        admit. (* pv0在电路中被连接时, 应该已经被声明 *)
        destruct H as [newotype Hfindv']; rewrite Hfindv' in Hpv0in.

        specialize Hpv0in with (expr := e).
        apply Hpv0in in Hein; clear Hpv0in.
        assert (exists exprtype, type_of_e e prepro.1.1 = Some exprtype).
        (* type_of_e 有结果, 意味着电路没有类型错误 *)
        admit.
        destruct H as [exprtype Hte]; rewrite Hte in Hein.
        assert (exists newexprtype, type_of_e e newtm = Some newexprtype).
        admit.
        destruct H as [newexprtype Hte']; rewrite Hte' in Hein.
        assert (ft_ref = newotype /\ newexprtype = ft_expr).
        rewrite Hhs in Hstmts'.
        specialize Hvm' with (vm' := vm') (ct' := ct') (ct := ct) (ss := (Qcons h ss)) (nss := (Qcons hs nss')).
        assert (Sem_frag_stmts nvm_port ct' (Qcons hs nss') vm' ct prepro.1.1).
        admit. (* prepro.1.1/prepron.1.1只影响所有aggtype的类型, 故由Hstmts'可证 *)
        clear Hstmts'; apply Hvm' in H; try done; clear Hvm'.
        move : H => [Hvm' Hvm''].
        specialize Hvm' with  (v0 := v0) (p := p) (pv0 := pv0) (ft := newcheckt) (q := newotype).
        specialize Hvm'' with (e := e) (p := q) (q := newexprtype).

        rewrite -Hvm'; try done.
        rewrite Hvm''; try done.
        rewrite Hp Hq; simpl; done.
        admit.
        admit. (* 由Hrght0, Hlft0可证, nvm_port比vm'少了rhs expr中新产生的vertex, 但不影响求解lhs type *)
        simpl; rewrite Hh; simpl; rewrite Htranss'; rewrite Hhs; done.
        move : H => [H1 H2]. 
        rewrite H1 -H2; apply Hein.
        admit. (* 意味着电路无误 *)
        admit. (* 意味着电路无误 *)
        split.
        (* subgoal3 *)
        clear Hct1 Hft0 Hvm0.
        rewrite Hp Hp0 in Hpeq'; simpl in Hpeq'.
        rewrite Hq Hq0 in Hqeq'; simpl in Hqeq'.
        rewrite Hpeq' Hqeq'; done.
        (* subgoal4 *)
        rewrite Hp Hp0 in Hpeq'; simpl in Hpeq'.
        rewrite Hq Hq0 in Hqeq2; simpl in Hqeq2.
        rewrite Hpeq' Hqeq2; done.
      - (* cast *) admit.
      - (* unop *) admit.
      - (* binop *) admit.
      - (* mux *) admit.
      - (* validif *) admit.
      - (* Eref *)
        destruct Hv0 as [Hnvm_port Hv0].
        split.
        admit.
        clear Hnvm_port.
        case Hlft0 : (list_lhs_ref_p nvm_port v0 prepron.1.1) => [p0|]; rewrite Hlft0 in Hv0; try done.
        assert (list_lhs_ref_p nvm_port v0 prepron.1.1 = Some p0 -> exists p, list_lhs_ref_p (fold_left make_p_implicit pp nvm_port) v0 prepro.1.1 = Some p /\ p.1 = p0.1 (* /\  p0.2的位宽等于p.2的位宽 *)).
        admit.
        apply H in Hlft0; clear H.
        destruct Hlft0 as [p [Hlft0 Hpeq']].
        rewrite Hlft0.
        case Hp0 : p0 => [lst_tgt0 ft_tgt0]; rewrite Hp0 in Hv0.
        case Hrght0 : (list_lhs_ref_p nvm_port r2 prepron.1.1) => [q0|]; rewrite Hrght0 in Hv0; try done.
        case Hp : p => [lst_tgt ft_tgt].
        assert (list_lhs_ref_p nvm_port r2 prepron.1.1 = Some q0 -> 
          exists q, list_lhs_ref_p (fold_left make_p_implicit pp nvm_port) r2 prepro.1.1 = Some q /\ 
          q.1 = q0.1).
        admit.
        apply H in Hrght0; clear H.
        destruct Hrght0 as [q [Hrght0 Hqeq']].
        rewrite Hrght0.
        case Hq0 : q0 => [lst_src0 ft_scr0]; rewrite Hq0 in Hv0.
        destruct Hv0 as [Hcnct Hct].
        case Hq : q => [lst_src ft_src].
        split.
        admit. (* 重要！！ *)
        rewrite Hp Hp0 in Hpeq'; simpl in Hpeq'.
        rewrite Hq Hq0 in Hqeq'; simpl in Hqeq'.
        rewrite Hpeq' Hqeq'; done.
      clear Hv0. 
      specialize IHss with (nvm_port := nvm_port') (ct := ct) (ct' := ct'0) (nss := nss').
      simpl in IHss.
      apply IHss in Htranss'; try done. 
      admit. (* 由Heq和Htranss' *)
      
    - (* invalid *)
      admit.
    - (* when *)
      admit.
      
  Admitted.
  (*
  + (* prove that the old ports are the implicit version of the new ports *)
    clear Hstmts Hprepron prepron Htranss nss.
    (*clear Hinfer Htopo inferorder Hdrawg drawg Hprepro prepro ss ct vm'.*)
    move : prepro drawg inferorder newtm nps nvm_port Hprepro Hdrawg Htopo Hinfer Htransp Hport.
    induction pp.
    - intros.
      rewrite /InferWidths_transps in Htransp.
      inversion Htransp as [Htransp'] ; clear Htransp.
      rewrite -Htransp' /Sem_port in Hport.
      rewrite /Sem_port /make_vm_implicit /make_ss_implicit /fold_left.
      exact Hport.
    - intros.
      destruct a as [var t|var t].
      * simpl Sem_port.
        simpl make_vm_implicit in IHpp.
        (* For the second part of this boolean conjunction (Sem_inport ...),
           make_gtyp_implicit will adapt exactly the part corresponding to t in nvm_port
           so as to ensure that these elements have the type prescribed by t.
           So, we change the second part to ``true'' first,
           probably by induction over t of a suitable inductive property. *)

(* Now come a few ideas for what might be suitable assertions to help prove the result. *)

        (* var is contained with type t in nps *)
        assert (ft_find var newtm <> None).
              unfold ft_find.
              admit.
        assert (Finput var t \in nps).
              simpl InferWidths_transps in Htransp.
              destruct (ftype_not_implicit t) eqn: Ht_not_implicit.
              * admit.
              * destruct (ft_find var newtm) as [ft|] eqn: Hft_find ; try done ; clear H.
                destruct (InferWidths_transps pp newtm) as [nss|] eqn: Hiwnewtm ; try done.
        (* var is defined with type t in nvm_port *)
        assert (Sem_inport (expli_ftype t) var.1 0 nvm_port).
        assert (forall n: nat,
                Sem_inport t var.1 n
                           (fold_left make_p_implicit pp
                                      (make_gtyp_implicit (drop n (vtype_list t [::])) n var.1 nvm_port))).
              (*induction t.
              - (* Gtyp f *)
                induction n.
                * rewrite /vtype_list /rcons /drop /make_gtyp_implicit.*)
        (* For the remaining part of the boolean conjunction (Sep_port pp ...),
           remove_t will remove exactly those parts of nvm_port
           that have been changed by make_gtyp_implicit.
           If we can prove that, we can apply IHpp. *)
        assert (remove_t (make_vm_implicit (FInmod v (Finput (var:=HiFirrtl.ProdVarOrder.T) var t :: pp)
                                                   (Qnil HiFirrtl.ProdVarOrder.T))
                                           nvm_port)
                         var.1 (size_of_ftype t) =
                make_vm_implicit (FInmod v pp (Qnil HiFirrtl.ProdVarOrder.T))
                                 (remove_t nvm_port var.1 (size_of_ftype t))).
              admit.
        specialize IHpp with (nvm_port := remove_t nvm_port var.1 (size_of_ftype t)).
  *)
  simpl.
  specialize InferWidths_fun_correct with (od := inferorder) (var2exprs := prepro.1.2) (tmap := prepro.1.1); intro.
  rewrite Hinfer in H.

  
  elim ss.
  simpl.
  rewrite /Sem_frag_stmts.

  (* KY previous version *)
  move => Hn. 
  case Hprepron : (prepro_stmts nss
  (fold_left (fun tempm : ft_pmap => prepro_p^~ tempm) nps
     ft_empty) (module_graph_vertex_set_p.empty (seq HiFP.hfexpr))
  [::]) => [prepron|]; rewrite Hprepron in Hn; try done.

  destruct Hn as [vm' [Hsemp Hsems]].
  exists (List.fold_left make_p_implicit pp vm').

  split.

  move : Hsemp Hm Hprepro Htransp. 
  move : pp F.
  induction pp. 
  - simpl.
    intros.
    inversion Htransp.
    rewrite -H0 in Hsemp.
    simpl in Hsemp; done.
  - intros.
    simpl.
    admit.

  move : Hm Hprepro Htranss.
  move : ss F.
  induction ss. 
  - simpl.
    intros.
    inversion Htranss.
    rewrite -H0 in Hsems.
    simpl in Hsems. 
    admit.
  - intros.
    simpl.
    simpl in Hprepro.
    case Hprepro0 : (prepro_stmt h (fold_left (fun tempm : ft_pmap => prepro_p^~ tempm) pp ft_empty)
    (module_graph_vertex_set_p.empty (seq HiFP.hfexpr)) [::]) => [prepro0|]; rewrite Hprepro0 in Hprepro; try discriminate.
    

  (* version before previous version *)
  move : Hn Hprepron Hinfer Htopo Hprepro Hm.
  move : vm ct F.
  (*move : Hn Hprepron Htranss Htransp Hinfer Htopo Hprepro Hm H vm ct.*)

  induction pp. 
  (* FInmod v [::] ss *)
  - 
  (* move => vm ct F.
    simpl.
    exists (module_graph_vertex_set_p.empty vertex_type).
    split.
    apply module_graph_vertex_set_p.is_empty_1.
    apply module_graph_vertex_set_p.empty_1.*)
    induction ss. 
    (* FInmod v [::] [::] *)
    - simpl.
      exists (module_graph_vertex_set_p.empty vertex_type).
      simpl in Htransp.
      inversion Htransp.
      clear Htransp.

      simpl in Htranss.
      inversion Htranss.
      clear Htranss.

      rewrite -H0 -H2 in Hn.
      simpl in Hn.
      destruct Hn as [vm' [Hempty [Heq1 Heq2]]].
      split; try done.
      split; try done.

      (*
      apply module_graph_vertex_set_p.is_empty_2 in Hempty.
      unfold make_mg_explicit in Heq1.
      unfold module_graph_vertex_set_p.Empty in Hempty.


      apply module_graph_vertex_set_p.F.Empty_m in Heq1.
      apply Heq1 in Hempty.

      
      clear Heq1 Heq2.
      rewrite module_graph_vertex_set_p.F.Empty_m.
      *)
      admit.

    (* FInmod v [::] (Qcons h ss) *)
    - exists (module_graph_vertex_set_p.empty vertex_type).
      split; try done.
      case Hsh : h => [|v0 t|v0 r|v0 m|v0 inst|v0 e|v0 e|v0|c s1 s2]; try simpl.
      (* skip *)
      - exists (module_graph_vertex_set_p.empty vertex_type).
        exists (module_graph_connection_trees_p.empty connection_tree).
        split; try done.
        specialize IHss with (F := FInmod v [::] ss) (vm := vm) (ct := ct).
        apply IHss in Hn; try done.
        destruct Hn as [vm' [Hempty Hfrag]].
        admit.
        rewrite Hsh in Htranss.
        simpl in Htranss.
        case Ht : (InferWidths_transss ss newtm) => [nss'|]; rewrite Ht in Htranss; try discriminate.
        (* 前提要去掉transss *)
        admit.
        rewrite Hsh in Hprepro.
        simpl in Hprepro.
        simpl; done.
      (* wire *)
      - exists (module_graph_connection_trees_p.empty connection_tree).

  admit.
  (* Exmod case *)
  rewrite Hm in H. 
  rewrite /InferWidths_m in H; discriminate.


Admitted.
(*
From firrtl Require Import Firrtl Env HiEnv HiFirrtl InferTypes.


Section InferWidthP.
  (********************************************************************************)

  (** Pass InferWidth *)

  (* Infer unknown width
     Infers the smallest width that is larger than or equal to all assigned widths to a signal
   * Note that this means that dummy assignments that are overwritten by last-connect-semantics
   * can still influence width inference *)

   (* A map to store candidate types *)
   (* Definition wmap := CE.t (seq ftype). *)
   (* Definition empty_wmap : wmap := CE.empty (seq ftype). *)
   (* Definition finds (v:var) (w:wmap) := match CE.find v w with Some t => t | None => [::] end. *)
  Definition def_ftype := Gtyp (Fuint 0).
  Definition wmap := CEP.t (ftype).
  Definition empty_wmap : wmap := CEP.empty (ftype).
  Definition finds (v:pvar) (w:wmap) := match CEP.find v w with Some t => t | None => def_ftype end.

  (* Import HiFP. *)
  (* Definition def_ftype' := Gtyp (Fuint 0). *)
  (* Definition wmap' := CEP.t (seq HiFP.hfexpr). *)
  (* Definition empty_wmap' : wmap' := CEP.empty (seq HiFP.hfexpr). *)
  (* Definition finds' (v:pvar) (w:wmap') := match CEP.find v w with Some t => t | None => ([::]) end. *)

  
   (* access to subfield is represented by the the snd element of pvar *)
  Fixpoint get_field_name (r : HiFP.href) : N :=
    match r with
    | Eid (b, s) => s
    (* should not have following cases *)
    (* | Esubfield r v =>  v *)
    (* | Esubindex r n => get_field_name r *)
    (* | Esubaccess r n => get_field_name r *)
    | _ => 0
    end.

  (* (* store the larger width in wmap *) *)
  (* (*TODO: fix the definition to update the related fields too*) *)
  (*  Definition add_wmap' (p:pvar) t w : wmap' := *)
  (*    match CEP.find p w with *)
  (*    (*already added in wmap, then upd to the larger one*) *)
  (*    | Some t1 => CEP.add p (t::t1) w *)
  (*    (*not in wmap yet, then add it with corresponding def_type*) *)
  (*    | None => CEP.add p [::t] w *)
  (*    end. *)

     (* store the larger width in wmap *)
  (*TODO: fix the definition to update the related fields too*)
   Definition add_wmap (p:pvar) t w : wmap :=
     match CEP.find p w with
     (*already added in wmap, then upd to the larger one*)
     | Some t1 => CEP.add p (HiF.max_width t t1) w
     (*not in wmap yet, then add it with corresponding def_type*)
     | None => CEP.add p t w
     end.

   (* Fixpoint fix_aggr_type (t_o: ftype) (t_s : list ftype) : ftype := *)
   (*   if (ftype_list t_o nil == t_s) then t_o else *)
   (*     match t_o with *)
   (*     | Gtyp t => t_s *)
   (*     | Atyp t n => m. *)
   
   (* Fixpoint update_aggr_type (p : pvar) (t:ftype) (w : wmap) : wmap := *)
   (*   match p with *)
       
   
   (* Fixpoint add_ref_wmap0 r t ce (w:wmap0) : wmap0 := *)
   (*   match r with *)
   (*   | Eid v => *)
   (*     match CE.find v w with *)
   (*     | Some t1 => CE.add v (max_width t t1) w *)
   (*     | None => CE.add v t w *)
   (*     end *)
   (*   | Esubfield r f => *)
   (*     let br := base_ref r in *)
   (*     CE.add br (upd_name_ftype (base_type_of_ref r ce) (v2var f) t) w *)
   (*   | Esubindex rs n => *)
   (*     let br := base_ref rs in *)
   (*     let vt := type_of_cmpnttyp (fst (CE.vtyp br ce)) in *)
   (*     match vt with *)
   (*     | Gtyp gt => w *)
   (*     | Atyp ta na => CE.add br (upd_vectyp vt t) w *)
   (*     | Btyp _ => CE.add br (upd_name_ftype vt (v2var (get_field_name rs)) t) w *)
   (*     end *)
   (*   | Esubaccess rs n => *)
   (*     let br := base_ref rs in *)
   (*     let vt := type_of_cmpnttyp (fst (CE.vtyp br ce)) in *)
   (*     match vt with *)
   (*     | Gtyp gt => w *)
   (*     | Atyp ta na => CE.add br (upd_vectyp vt t) w *)
   (*     | Btyp Fnil => w *)
   (*     | Btyp (Fflips v _ tf fs) => *)
   (*       CE.add br (upd_name_ftype vt (v2var (get_field_name rs)) t) w *)
   (*     end *)
   (*   end. *)

   (*scan statement to find declaration without specific width, & to find protential width accroding to connections*)
   (*ce is the component env after infertype*)
   Fixpoint inferwidth_wmap (s : HiFP.hfstmt) (ce : CEP.env) (w : wmap): wmap :=
     match s with
     (*node declaration, if with default type (zero width) then add node to wmap*)
     (*possible bundle*)
     | Snode v e => if HiF.is_deftyp (HiFP.type_of_hfexpr e ce)
                    then add_wmap v (HiFP.type_of_hfexpr e ce) w else w
     | Swire v t => if HiF.is_deftyp t then add_wmap v t w else w
     | Sreg v r => if HiF.is_deftyp (type r) then add_wmap v (type r) w else w
     | Sfcnct (Eid r1) e =>
         (* if HiF.is_deftyp (HiFP.type_of_hfexpr e ce)  *)
         (* then find which isdef, infer that first *)
         
         let t1 := type_of_cmpnttyp (fst (CEP.vtyp r1 ce)) in
         let te := HiFP.type_of_hfexpr e ce in
         (*t1 is default type, means r1 is declared with zero width, 
          *or r1 is a subfield/subindex that infertype have not registered it in ce*)
         if HiF.is_deftyp t1 then add_wmap r1 te w else w
     (* | Spcnct (Eid r1) e => *)
     (*     let t1 := type_of_cmpnttyp (fst (CEP.vtyp r1 ce)) in *)
     (*     let te := type_of_hfexprP e ce in *)
     (*     if HiF.is_deftyp t1 then add_wmap r1 te w else w *)
     | Swhen c s1 s2 => inferwidth_wmap_sts s2 ce (inferwidth_wmap_sts s1 ce w)
     | Sinst v1 v2 => if HiF.is_deftyp (HiFP.type_of_ref (HiFP.eid v2) ce)
                      then add_wmap v1 (HiFP.type_of_ref (HiFP.eid v2) ce) w else w
     | Sskip
     | Sinvalid _
     | Smem _ _
     (* | Sfcnct (Esubfield _ _) _ *)
     (* | Sfcnct (Esubindex _ _) _ *)
     (* | Sfcnct (Esubaccess _ _) _ *)
     (* | Spcnct (Esubfield _ _) _ *)
     (* | Spcnct (Esubindex _ _) _ *)
     (* | Spcnct (Esubaccess _ _) _ *)
     | _=> w   
     end
   with inferwidth_wmap_sts (s : HiFP.hfstmt_seq) (ce : CEP.env) (w : wmap): wmap :=
          match s with
          | Qnil => w
          | Qcons hd tl => inferwidth_wmap_sts tl ce (inferwidth_wmap hd ce w)
          end.

   (*    Fixpoint inferwidth_wmap' (s : HiFP.hfstmt) (ce : CEP.env) (w : wmap'): wmap' := *)
   (*   match s with *)
   (*   (*node declaration, if with default type (zero width) then add node to wmap*) *)
   (*   (*possible bundle*) *)
   (*   | Snode v e => if HiF.is_deftyp (HiFP.type_of_hfexpr e ce) *)
   (*                  then add_wmap' v e w else w *)
   (*   | Swire v t => if HiF.is_deftyp t then add_wmap' v (HiFP.eref (Eid v)) w else w *)
   (*   | Sreg v r => if HiF.is_deftyp (type r) then add_wmap' v  w else w *)
   (*   | Sfcnct (Eid r1) e => *)
   (*       let t1 := type_of_cmpnttyp (fst (CEP.vtyp r1 ce)) in *)
   (*       let te := HiFP.type_of_hfexpr e ce in *)
   (*       (*t1 is default type, means r1 is declared with zero width,  *)
   (*        *or r1 is a subfield/subindex that infertype have not registered it in ce*) *)
   (*       if HiF.is_deftyp t1 then add_wmap r1 te w else w *)
   (*   (* | Spcnct (Eid r1) e => *) *)
   (*   (*     let t1 := type_of_cmpnttyp (fst (CEP.vtyp r1 ce)) in *) *)
   (*   (*     let te := type_of_hfexprP e ce in *) *)
   (*   (*     if HiF.is_deftyp t1 then add_wmap r1 te w else w *) *)
   (*   | Swhen c s1 s2 => inferwidth_wmap_sts s2 ce (inferwidth_wmap_sts s1 ce w) *)
   (*   | Sinst v1 v2 => if HiF.is_deftyp (HiFP.type_of_ref (HiFP.eid v2) ce) *)
   (*                    then add_wmap v1 (HiFP.type_of_ref (HiFP.eid v2) ce) w else w *)
   (*   | Sskip *)
   (*   | Sinvalid _ *)
   (*   | Smem _ _ *)
   (*   (* | Sfcnct (Esubfield _ _) _ *) *)
   (*   (* | Sfcnct (Esubindex _ _) _ *) *)
   (*   (* | Sfcnct (Esubaccess _ _) _ *) *)
   (*   (* | Spcnct (Esubfield _ _) _ *) *)
   (*   (* | Spcnct (Esubindex _ _) _ *) *)
   (*   (* | Spcnct (Esubaccess _ _) _ *) *)
   (*   | _=> w    *)
   (*   end *)
   (* with inferwidth_wmap_sts (s : HiFP.hfstmt_seq) (ce : CEP.env) (w : wmap): wmap := *)
   (*        match s with *)
   (*        | Qnil => w *)
   (*        | Qcons hd tl => inferwidth_wmap_sts tl ce (inferwidth_wmap hd ce w) *)
   (*        end. *)

   
   (* Fixpoint inferWidth_wmap0 (s : hfstmt) (ce : cenv) (w : wmap0): wmap0 := *)
   (*   match s with *)
   (*   | Snode v e => if is_deftyp (type_of_hfexpr e ce) *)
   (*                    then add_ref_wmap0 (Eid v) (type_of_hfexpr e ce) ce w else w *)
   (*   | Swire v t => if is_deftyp t then add_ref_wmap0 (Eid v) t ce w else w *)
   (*   | Sreg v r => if is_deftyp (type r) then add_ref_wmap0 (Eid v) (type r) ce w else w *)
   (*   | Sfcnct r1 (Eref r2) => *)
   (*     let w1 := add_ref_wmap0 r1 (type_of_ref r2 ce) ce w in *)
   (*     if is_deftyp (type_of_ref r1 ce) then w1 *)
   (*     else w *)
   (*   | Sfcnct r e => *)
   (*     let w1 := add_ref_wmap0 r (type_of_hfexpr e ce) ce w in *)
   (*     if is_deftyp (type_of_ref r ce) then w1 else w *)
   (*   | Spcnct r1 (Eref r2) => *)
   (*     let add1 := add_ref_wmap0 r1 (type_of_ref r2 ce) ce w in *)
   (*     if is_deftyp (type_of_ref r1 ce)  then add1 *)
   (*     else w *)
   (*   | Spcnct r e => *)
   (*     let w1 := add_ref_wmap0 r (type_of_hfexpr e ce) ce w in *)
   (*     if is_deftyp (type_of_ref r ce) then w1 else w *)
   (*   | Swhen c s1 s2 => *)
   (*     let fix aux ss ce w := *)
   (*         match ss with *)
   (*         | nil => w *)
   (*         | s :: ss => aux ss ce (inferWidth_wmap0 s ce w) *)
   (*         end *)
   (*     in *)
   (*     aux s2 ce (aux s1 ce w) *)
   (*   | _ => w *)
   (*   end. *)

   (* Fixpoint inferWidth_stmts_wmap0 (ss : seq hfstmt) ce w: wmap0 := *)
   (*   match ss with *)
   (*   | nil => w *)
   (*   | cons s sts => inferWidth_stmts_wmap0 sts ce (inferWidth_wmap0 s ce w) *)
   (*   end. *)

   Definition add_width_2_cenv (w : option ftype) (t : option (cmpnt_init_typs ProdVarOrder.T * fcomponent)) :=
     match w, t with
     | Some w, Some (Aggr_typ ta, c) => if HiF.is_deftyp ta then Some (HiFP.aggr_typ w, c) else t
     | Some w, Some (Reg_typ r, c) =>
       if HiF.is_deftyp (type r) then Some (HiFP.reg_typ (mk_freg (w) (clock r) (reset r)), c) else t
     | Some w, Some (Mem_typ m, c) =>
       if HiF.is_deftyp (data_type m) then Some (HiFP.mem_typ (mk_fmem w (depth m) (reader m) (writer m) (read_latency m) (write_latency m) (read_write m)), c)
       else t
     | _, t => t
     end.

   (* overwrite type widths in ce by wmap with the same index *)

   Definition wmap_map2_cenv w (ce:CEP.env) : CEP.env :=
     CEP.map2 add_width_2_cenv w ce.

   Definition inferWidth_fun ss ce : CEP.env :=
     wmap_map2_cenv (inferwidth_wmap_sts ss ce empty_wmap) ce.

   (* Parameter new_v_wmap_none: *)
   (*   forall v, *)
   (*   new_comp_name v -> *)
   (*   forall w: wmap0, CE.find v w = None. *)
   
   (**** infer width semantics in pred **)

   (*Begin : new one*)
   Inductive inferWidth_sstmt_sem' : HiFP.hfstmt -> CEP.env -> CEP.env -> Prop :=
   | inferWidth_sskip_sem ce0 :
       (*do nothing*)
       inferWidth_sstmt_sem' (HiFP.sskip) ce0 ce0
   | inferWidth_snode_sem v e ce0 ce1 :
       (*doesn't produce new width for v*)
       CEP.find v ce0 = CEP.find v ce1 ->
       inferWidth_sstmt_sem' (HiFP.snode v e) ce0 ce1
   | inferWidth_sinvalid_sem v ce0 ce1 :
       (*doesn't produce new width for v*)
       CEP.find v ce0 = CEP.find v ce1 ->
       inferWidth_sstmt_sem' (HiFP.sinvalid (HiFP.eid v)) ce0 ce1
   | inferWidth_smem_sem v m ce0 ce1 :
       (*doesn't produce new width for v*)
       CEP.find v ce0 = CEP.find v ce1 ->
       inferWidth_sstmt_sem' (HiFP.smem v m) ce0 ce1
   | inferWidth_sinst_sem v m ce0 ce1 :
       (*doesn't produce new width for v*)
       CEP.find v ce0 = CEP.find v ce1 ->
       inferWidth_sstmt_sem' (HiFP.sinst v m) ce0 ce1 
   | inferWidth_swire_sem v t ce0 ce1 :
       (*doesn't produce new width for v*)
       CEP.find v ce0 = CEP.find v ce1 ->
       inferWidth_sstmt_sem' (HiFP.swire v t) ce0 ce1
   | inferWidth_sreg_sem v r ce0 ce1 :
       (*doesn't produce new width for v*)
       CEP.find v ce0 = CEP.find v ce1 ->
       inferWidth_sstmt_sem' (Sreg v r) ce0 ce1
   | inferWidth_sfcnct_ftype_sem r e tr tr' te c ce0 ce1  :
       (*type of r is tr in ce0*)
       CEP.find (r) ce0 = Some (tr, c) ->
       (*type of expression e is te in ce0*)
       HiFP.type_of_hfexpr e ce0 = te ->
       (*te in e0 and e1 are same*)
       HiFP.type_of_hfexpr e ce0 = HiFP.type_of_hfexpr e ce1 ->
       (*tr is implicit*)
       HiF.is_deftyp (type_of_cmpnttyp tr) ->
       (*tr and te type equiv*)
       ftype_equiv (type_of_cmpnttyp tr) te ->
       (*infer a "possible" larger width for r*)
       CEP.find (r) ce1 = add_width_2_cenv (Some (HiF.max_width tr' te)) (Some (tr, c)) ->
       inferWidth_sstmt_sem' (Sfcnct (HiFP.eid r) e) ce0 ce1
   | inferWidth_sfcnct_ftype_lt_sem r e tr tr' te c ce0 ce1 :
       (*type of r is tr in ce0*)
       CEP.find (r) ce0 = Some (tr, c) ->
       (*type of expression e is te in ce0*)
       HiFP.type_of_hfexpr e ce0 = te ->
       (*te in e0 and e1 are same*)
       HiFP.type_of_hfexpr e ce0 = HiFP.type_of_hfexpr e ce1 ->
       (*tr is implicit*)
       HiF.is_deftyp (type_of_cmpnttyp tr) ->
       (*tr and te type equiv*)
       ftype_equiv (type_of_cmpnttyp tr) te ->
       (*tr has smaller width than te*)
       ~~ HiF.typeConstraintsGe (type_of_cmpnttyp tr) te ->
       (*new width for r*)
       CEP.find r ce1 = Some (tr', c) ->
       type_of_cmpnttyp tr' = te ->
       inferWidth_sstmt_sem' (Sfcnct (HiFP.eid r) e) ce0 ce1
   | inferWidth_sfcnct_ftype_ge_sem r e tr te c ce0 ce1  :
       (*type of r is tr in ce0*)
       CEP.find (r) ce0 = Some (tr, c) ->
       (*type of expression e is te in ce0*)
       HiFP.type_of_hfexpr e ce0 = te ->
       (*te in e0 and e1 are same*)
       HiFP.type_of_hfexpr e ce0 = HiFP.type_of_hfexpr e ce1 ->
       (*tr is implicit*)
       HiF.is_deftyp (type_of_cmpnttyp tr) ->
       (*tr and te type equiv*)
       ftype_equiv (type_of_cmpnttyp tr) te ->
       (*tr has larger width than te*)
       HiF.typeConstraintsGe (type_of_cmpnttyp tr) te ->
       (*keep old width for r*)
       CEP.find (r) ce1 = Some (tr, c) ->
       inferWidth_sstmt_sem' (Sfcnct (HiFP.eid r) e) ce0 ce1
   (* | inferWidth_spcnct_ftype_lt_sem r e tr te c ce0 ce1 : *)
   (*     (*type of r is tr in ce0*) *)
   (*     CEP.find (r) ce0 = Some (tr, c) -> *)
   (*     (*type of expression e is te in ce0*) *)
   (*     HiFP.type_of_hfexpr e ce0 = type_of_cmpnttyp te -> *)
   (*     (*te in e0 and e1 are same*) *)
   (*     HiFP.type_of_hfexpr e ce0 = HiFP.type_of_hfexpr e ce1 -> *)
   (*     (*tr is implicit*) *)
   (*     HiF.is_deftyp (type_of_cmpnttyp tr) -> *)
   (*     (*tr and te weak type equiv*) *)
   (*     ftype_equiv (type_of_cmpnttyp tr) (type_of_cmpnttyp te) -> *)
   (*     (*tr has smaller width than te*) *)
   (*     ~~ HiF.typeConstraintsGe (type_of_cmpnttyp tr) (type_of_cmpnttyp te) -> *)
   (*     (*new width for r*) *)
   (*     CEP.find (r) ce1 = Some (te, c) -> *)
   (*     inferWidth_sstmt_sem' (Spcnct (HiFP.eid r) e) ce0 ce1 *)
   (* | inferWidth_spcnct_ftype_ge_sem r e tr te c ce0 ce1 : *)
   (*     (*type of r is tr in ce0*) *)
   (*     CEP.find (r) ce0 = Some (tr, c) -> *)
   (*     (*type of expression e is te in ce0*) *)
   (*     HiFP.type_of_hfexpr e ce0 = te -> *)
   (*     (*te in e0 and e1 are same*) *)
   (*     HiFP.type_of_hfexpr e ce0 = HiFP.type_of_hfexpr e ce1 -> *)
   (*     (*tr is implicit*) *)
   (*     HiF.is_deftyp (type_of_cmpnttyp tr) -> *)
   (*     (*tr and te type equiv*) *)
   (*     ftype_equiv (type_of_cmpnttyp tr) (te) -> *)
   (*     (*tr has larger width than te*) *)
   (*     HiF.typeConstraintsGe (type_of_cmpnttyp tr) (te) -> *)
   (*     (*keep old width for r*) *)
   (*     CEP.find (r) ce1 = Some (tr, c) -> *)
   (*     inferWidth_sstmt_sem' (Spcnct (HiFP.eid r) e) ce0 ce1 *)
   | inferWidth_sfcnct_nodef_sem r e tr c ce0 ce1 :
       (*type of r is tr in ce0*)
       CEP.find (r) ce0 = Some (tr, c) ->
       (*tr is explicit*)
       ~~ HiF.is_deftyp (type_of_cmpnttyp tr) ->
       (*unchange for r*)
       CEP.find (r) ce0 = CEP.find (r) ce1 ->
       inferWidth_sstmt_sem' (Sfcnct (HiFP.eid r) e) ce0 ce1
   (* | inferWidth_spcnct_nodef_sem r e tr c ce0 ce1 : *)
   (*     (*type of r is tr in ce0*) *)
   (*     CEP.find (r) ce0 = Some (tr, c) -> *)
   (*     (*tr is explicit*) *)
   (*     ~~ HiF.is_deftyp (type_of_cmpnttyp tr) -> *)
   (*     (*unchange for r*) *)
   (*     CEP.find (r) ce0 = CEP.find (r) ce1 -> *)
   (*     inferWidth_sstmt_sem' (Spcnct (HiFP.eid r) e) ce0 ce1 *)
   | inferWidth_swhen_sem ce0 ce1 ce2 c s1 s2:
       inferWidth_stmts_sem' (s1) ce0 ce1 ->
       inferWidth_stmts_sem' (s2) ce1 ce2 ->
       inferWidth_sstmt_sem' (Swhen c s1 s2) ce0 ce2
   with
     inferWidth_stmts_sem' : HiFP.hfstmt_seq -> CEP.env -> CEP.env -> Prop :=
   | inferWidth_stmts_nil_sem ce :
         inferWidth_stmts_sem' HiFP.qnil ce ce
   | inferWidth_stmts_cons st sts (ce0 ce1 ce2 ce3 : CEP.env) :
       inferType_stmtsP (Qcons st sts) ce0 ce1 ->
       inferWidth_sstmt_sem' st ce1 ce2 ->
       inferWidth_stmts_sem' sts ce2 ce3 ->
       inferWidth_stmts_sem' (Qcons st sts) ce1 ce3.

   (*End : new one*)

   Definition new_ident s (ce : wmap) :=
     match s with
     | Snode v _
     | Swire v _
     | Sreg v _
     | Smem v _
     | Sinst v _ => CEP.find v ce = None
     | Sfcnct (Eid v) _ 
     (* | Spcnct (Eid v) _ => ~ (CEP.find v ce = None) *)
     | Sinvalid (Eid v) => ~ (CEP.find v ce = None)
     | Sfcnct _ _ => False
     (* | Spcnct _ _ => False *)
     | Sinvalid _ => False
     | Swhen _ _ _ => False
     | Sskip => True
     end.
   
   Lemma inferWidth_snode_sem_conform:
     forall v e wm0 wm1 ce1 ce2,
       CEP.find v ce1 = Some (HiFP.aggr_typ (HiFP.type_of_hfexpr e ce1), Node) ->
       new_ident (Snode v e) wm0 ->
       wm1 = inferwidth_wmap (Snode v e) ce1 wm0 ->
       ce2 = wmap_map2_cenv wm1 ce1 ->
       inferWidth_sstmt_sem' (Snode v e) ce1 ce2.
   Proof.
     intros. 
     have Hnone : (add_width_2_cenv None None = None) by done.
     move : (HiFP.PCELemmas.map2_1bis wm1 ce1 v Hnone) => Hint.
     apply inferWidth_snode_sem.
     rewrite H2 Hint.
     rewrite H1/=.
     case Hdf : (HiF.is_deftyp (HiFP.type_of_hfexpr e ce1)).
     rewrite /add_wmap H0/=. 
     rewrite (HiFP.PCELemmas.add_eq_o _ _ (eq_refl v)).
     rewrite H/= Hdf//.
     rewrite H0//.
   Qed.

   Lemma inferWidth_swire_sem_conform:
     forall v t wm0 wm1 ce1 ce2,
       CEP.find v ce1 = Some (HiFP.aggr_typ t, Wire) ->
       new_ident (Swire v t) wm0 ->
       (* CEP.find v wm0  = None -> *)
       wm1 = inferwidth_wmap (Swire v t) ce1 wm0 ->
       ce2 = wmap_map2_cenv wm1 ce1 ->
       inferWidth_sstmt_sem' (Swire v t) ce1 ce2.
   Proof.
     intros.
     have Hnone : (add_width_2_cenv None None = None) by done.
     move : (HiFP.PCELemmas.map2_1bis wm1 ce1 v Hnone) => Hint.
     apply inferWidth_swire_sem.
     rewrite H2 Hint.
     rewrite H1/=.
     case Hdf : (HiF.is_deftyp t).
     rewrite /add_wmap H0/=.
     rewrite (HiFP.PCELemmas.add_eq_o _ _ (eq_refl v)).
     rewrite H/= Hdf//.
     rewrite H0//.
   Qed.

   Lemma inferWidth_sreg_sem_conform:
     forall v t wm0 wm1 ce1 ce2,
       CEP.find v ce1 = Some (HiFP.reg_typ t, Register) ->
       (* CEP.find v wm0  = None -> *)
       new_ident (Sreg v t) wm0 ->
       wm1 = inferwidth_wmap (Sreg v t) ce1 wm0 ->
       ce2 = wmap_map2_cenv wm1 ce1 ->
       inferWidth_sstmt_sem' (Sreg v t) ce1 ce2.
   Proof.
     intros.
     have Hnone : (add_width_2_cenv None None = None) by done.
     move : (HiFP.PCELemmas.map2_1bis wm1 ce1 v Hnone) => Hint.
     apply inferWidth_sreg_sem.
     rewrite H2 Hint.
     rewrite H1/=.
     case Hdf : (HiF.is_deftyp (type t)).
     rewrite /add_wmap H0/=.
     rewrite (HiFP.PCELemmas.add_eq_o _ _ (eq_refl v)).
     rewrite H/= Hdf. by case t.
     rewrite H0//.
   Qed.

   Lemma inferWidth_smem_sem_conform:
     forall v t wm0 wm1 ce1 ce2,
       CEP.find v ce1 = Some (HiFP.mem_typ t, Memory) ->
       (* CEP.find v wm0  = None -> *)
       new_ident (Smem v t) wm0 ->
       wm1 = inferwidth_wmap (Smem v t) ce1 wm0 ->
       ce2 = wmap_map2_cenv wm1 ce1 ->
       inferWidth_sstmt_sem' (Smem v t) ce1 ce2.
   Proof.
     intros.
     have Hnone : (add_width_2_cenv None None = None) by done.
     move : (HiFP.PCELemmas.map2_1bis wm1 ce1 v Hnone) => Hint.
     apply inferWidth_smem_sem.
     rewrite H2 Hint.
     rewrite H1/=.
     rewrite H0 //.
   Qed.

   Lemma inferWidth_sinst_sem_conform:
     forall v v' wm0 wm1 ce1 ce2,
       CEP.find v ce1 = Some (HiFP.aggr_typ (type_of_cmpnttyp (CEP.vtyp v' ce1).1), Instanceof) ->
       (* CEP.find v wm0  = None -> *)
       new_ident (Sinst v v') wm0 ->
       wm1 = inferwidth_wmap (Sinst v v') ce1 wm0 ->
       ce2 = wmap_map2_cenv wm1 ce1 ->
       inferWidth_sstmt_sem' (Sinst v v') ce1 ce2.
   Proof.
     intros.
     have Hnone : (add_width_2_cenv None None = None) by done.
     move : (HiFP.PCELemmas.map2_1bis wm1 ce1 v Hnone) => Hint.
     apply inferWidth_sinst_sem.
     rewrite H2 Hint H1/=.
     case Hdf : (HiF.is_deftyp (type_of_cmpnttyp (CEP.vtyp v' ce1).1)).
     rewrite /add_wmap H0/=.
     rewrite (HiFP.PCELemmas.add_eq_o _ _ (eq_refl v)).
     rewrite H /= Hdf//. 
     rewrite H0//.
   Qed.

   Lemma ftype_equiv_symmetry t1 t2 :
     ftype_equiv t1 t2 -> ftype_equiv t2 t1
   with ffield_equiv_symmetry f1 f2 :
          fbtyp_equiv f1 f2 -> fbtyp_equiv f2 f1.
   Proof.
     elim: t1 t2 => [f1| f1 H1 n1| n1 ]  [f2| f2 n2| n2 ]//.
     - elim: f1 f2; try done.
     - rewrite /= => /andP [Heq Hfeq]. rewrite (eqP Heq)/= eq_refl andTb.
         by apply H1.
     - rewrite /=. apply ffield_equiv_symmetry.
     elim: f1 f2 => [|v1 flp1 f1 fs1 IH1 ] [|v2 flp2 f2 fs2 ] .
     - done.
     - rewrite /=//.
     - rewrite /=; case flp1; done.
     - elim: flp1 flp2 => [|] [|] /=//.
       + move => /andP [/andP [Heq Heqf] Heqb].
         rewrite (eqP Heq) eq_refl andTb.
         apply /andP. split.
         by apply ftype_equiv_symmetry.
         exact : (IH1 fs2 Heqb).
       + move => /andP [/andP [Heq Heqf] Heqb].
         rewrite (eqP Heq) eq_refl andTb.
         apply /andP. split.
         by apply ftype_equiv_symmetry.
         exact : (IH1 fs2 Heqb).
   Qed.
   
   Lemma max_width_symmetry t1 t2 :
     HiF.max_width (t1) (t2) = HiF.max_width (t2) (t1).
   Proof.
   Admitted.

   Parameter ftype_equiv_trans : forall t1 t2 t3,
       ftype_equiv t1 t2 -> ftype_equiv t2 t3 ->
       ftype_equiv t1 t3.
   Parameter ffield_equiv_trans : forall f1 f2 f3,
       fbtyp_equiv f1 f2 -> fbtyp_equiv f2 f3 ->
       fbtyp_equiv f1 f3.
   
   Parameter typeConstraints_max_width :forall t1 t2,
     ftype_equiv t1 t2 ->
     HiF.typeConstraintsGe t1 t2 ->
     HiF.max_width t1 t2 = t1.

   Parameter typeConstraintsGe_deftyp : forall t1 t2,
       HiF.is_deftyp t1 ->
       ftype_equiv t1 t2 ->
       HiF.typeConstraintsGe t2 t1.

   Parameter typeConstraintsGe_isdeftyp : forall t1 t2,
       HiF.is_deftyp t1 ->
       ftype_equiv t1 t2 ->
       HiF.typeConstraintsGe t1 t2 ->
       HiF.is_deftyp t2.

   Parameter typeConstraintsGe_trans : forall t1 t2 t3,
       ftype_equiv t1 t2 ->
       ftype_equiv t2 t3 ->
       HiF.typeConstraintsGe t1 t2 ->
       HiF.typeConstraintsGe t2 t3 ->
       HiF.typeConstraintsGe t1 t3.

   Definition contain_no_v_ref v (r : HiFP.href) :=
     match r with
     | Eid v' => ~ (v = v')
     | _ => False
     end.
   
   Fixpoint contain_no_v v (e : HiFP.hfexpr) :=
     match e with
     | Econst _ _ => True
     | Ecast c e1 => contain_no_v v e1
     | Eprim_unop u e1 => contain_no_v v e1
     | Eprim_binop b e1 e2 => contain_no_v v e1 /\ contain_no_v v e2
     | Emux m e1 e2 =>  contain_no_v v e1 /\ contain_no_v v e2 /\ contain_no_v v m
     (* | Evalidif c e1 =>  contain_no_v v c /\ contain_no_v v e1 *)
     | Eref r => contain_no_v_ref v r
     end.

   Parameter contain_no_v_hfexpr_type_same :
     forall v t f e (wm : wmap) (ce1 ce2 : CEP.env),
       contain_no_v v e ->
       ce2 = CEP.map2 f (CEP.add v t wm) ce1  ->
       HiFP.type_of_hfexpr e ce1 = HiFP.type_of_hfexpr e ce2.
   
   Lemma inferWidth_sfcnct_ftype_sem_conform :
     forall (r:pvar) e c1 t0 t1 t2 wm1 wm2 (ce1 ce2 : CEP.env) ,
       ftype_equiv t1 t2 ->
       ftype_equiv (type_of_cmpnttyp t0) t2 ->
       CEP.find r ce1 =  Some (t0, c1) ->
       contain_no_v r e ->
       HiF.is_deftyp (type_of_cmpnttyp t0) ->
       HiFP.type_of_hfexpr e ce1 = t2 ->
       CEP.find r wm1 = Some t1 ->
       wm2 = inferwidth_wmap (Sfcnct (Eid r) e) ce1 wm1 ->
       ce2 = wmap_map2_cenv wm2 ce1 ->
       inferWidth_sstmt_sem' (Sfcnct (Eid r) e) ce1 ce2.
   Proof.
     intros.
     apply inferWidth_sfcnct_ftype_sem with t0 t1 t2 c1; try done.
     apply contain_no_v_hfexpr_type_same with r (HiF.max_width t2 t1) add_width_2_cenv wm1; try done.
     move : H7.
     rewrite H6/=(CEP.find_some_vtyp H1)/= H3 H4.
     rewrite /add_wmap H5.
     rewrite /wmap_map2_cenv//.
     rewrite H7 H6 (lock add_width_2_cenv)/= (CEP.find_some_vtyp H1) H3 H4.     
     rewrite /add_wmap H5 /wmap_map2_cenv.
     have Hnone : (add_width_2_cenv None None = None) by done.
     rewrite (HiFP.PCELemmas.map2_1bis (CEP.add r (HiF.max_width t2 t1) wm1) ce1 r Hnone)/=.
     rewrite (HiFP.PCELemmas.add_eq_o _ _ (eq_refl r)) H1 -lock max_width_symmetry//.
   Qed.     
   
(*    (*Begin : old one*) *)
(*    Inductive inferWidth_sstmt_sem : hfstmt -> wmap0 -> wmap0 -> cenv -> cenv -> Prop := *)
(*    | inferWidth_sskip wm1 wm2 ce1 ce2 : *)
(*        (forall v t c, *)
(*        CE.find v ce1 = Some (t, c) -> *)
(*        CE.find v wm1 = Some (type_of_cmpnttyp t) -> *)
(*        CE.find v wm1 = CE.find v wm2 -> *)
(*        CE.find v ce1 = CE.find v ce2)   -> *)
(*        inferWidth_sstmt_sem (sskip) wm1 wm2 ce1 ce2 *)
(*    | inferWidth_sstop wm1 wm2 ce1 ce2 ss1 ss2 n : *)
(*        (forall v t c , *)
(*        CE.find v ce1 = Some (t, c) -> *)
(*        CE.find v wm1 = Some (type_of_cmpnttyp t) -> *)
(*        CE.find v wm1 = CE.find v wm2 -> *)
(*        CE.find v ce1 = CE.find v ce2) -> *)
(*        inferWidth_sstmt_sem (sstop ss1 ss2 n) wm1 wm2 ce1 ce2 *)
(*    | inferWidth_sinvalid wm1 wm2 ce1 ce2 : *)
(*        forall v, (forall t c, *)
(*          CE.find (base_ref v) ce1 = Some (t, c) -> *)
(*          CE.find (base_ref v) wm1 = Some (type_of_cmpnttyp t) -> *)
(*          CE.find (base_ref v) wm1 = CE.find (base_ref v) wm2 -> *)
(*          CE.find (base_ref v) ce1 = CE.find (base_ref v) ce2) -> *)
(*          inferWidth_sstmt_sem (sinvalid v) wm1 wm2 ce1 ce2 *)
(*    | inferWidth_smem v m wm1 wm2 ce1 ce2 : *)
(*        forall t , *)
(*          CE.find (v) ce1 = Some (t, Memory) -> *)
(*          new_comp_name v -> *)
(*          CE.find v wm1 = CE.find v wm2 -> *)
(*          CE.find v ce1 = CE.find v ce2 -> *)
(*        inferWidth_sstmt_sem (smem v m) wm1 wm2 ce1 ce2 *)
(*    | inferWidth_sinst v m wm1 wm2 ce1 ce2 : *)
(*        forall t c, *)
(*          CE.find (v) ce1 = Some (t, c) -> *)
(*          new_comp_name v -> *)
(*          CE.find v wm1 = CE.find v wm2 -> *)
(*          CE.find v ce1 = CE.find v ce2 -> *)
(*        inferWidth_sstmt_sem (sinst v m) wm1 wm2 ce1 ce2 *)
(*    | inferWidth_snode_exp v e ce0 ce1 (wm : wmap0) : *)
(*        CE.find (v) ce0 = Some (aggr_typ (type_of_hfexpr e ce0), Node) -> *)
(*        ~~ is_deftyp (type_of_hfexpr e ce0) -> *)
(*        new_comp_name v -> *)
(*        CE.find v ce0 = CE.find v ce1 -> *)
(*        inferWidth_sstmt_sem (Snode v e) wm wm ce0 ce1 *)
(*    | inferWidth_snode_imp v e ce0 ce1 (wm0 wm1 : wmap0) : *)
(*        is_deftyp ((type_of_hfexpr e ce0)) -> *)
(*        CE.find (v) ce0 = Some (aggr_typ (type_of_hfexpr e ce0), Node) -> *)
(*        new_comp_name v -> *)
(*        CE.find v wm1 = Some (type_of_hfexpr e ce0) -> *)
(*        CE.find v ce0 = CE.find v ce1 -> *)
(*        inferWidth_sstmt_sem (Snode v e) wm0 wm1 ce0 ce1 *)
(*    | inferWidth_swire_exp v t ce0 ce1 wm : *)
(*        new_comp_name v -> *)
(*        ~~ is_deftyp (t) -> *)
(*        CE.find (v) ce0 = Some (aggr_typ t, Wire) -> *)
(*        CE.find v ce0 = CE.find v ce1 -> *)
(*        inferWidth_sstmt_sem (Swire v t) wm wm ce0 ce1 *)
(*    | inferWidth_swire_imp v t ce0 ce1 wm0 wm1 : *)
(*        is_deftyp t -> *)
(*        CE.find (v) ce0 = Some (aggr_typ t, Wire) -> *)
(*        new_comp_name v -> *)
(*        CE.find v wm1 = Some t -> *)
(*        CE.find v ce0 = CE.find v ce1 -> *)
(*        inferWidth_sstmt_sem (Swire v t) wm0 wm1 ce0 ce1 *)
(*    | inferWidth_sreg_exp v r ce0 ce1 wm : *)
(*        ~~ is_deftyp (type r) -> *)
(*        CE.find (v) ce0 = Some (reg_typ r, Register) -> *)
(*        new_comp_name v -> *)
(*        CE.find v ce0 = CE.find v ce1 -> *)
(*        inferWidth_sstmt_sem (Sreg v r) wm wm ce0 ce1 *)
(*    | inferWidth_sreg_imp v r ce0 ce1 wm0 wm1 : *)
(*        is_deftyp (type r) -> *)
(*        CE.find (v) ce0 = Some (reg_typ r, Register) -> *)
(*        new_comp_name v -> *)
(*        CE.find v wm1 = Some (type r) -> *)
(*        CE.find v ce0 = CE.find v ce1 -> *)
(*        inferWidth_sstmt_sem (Sreg v r) wm0 wm1 ce0 ce1 *)
(*    | inferWidth_sfcnct_ftype_gt r e t0 t1 t3 c ce0 ce1 wm0 wm1 : *)
(*        CE.find (base_ref r) wm0 = Some t1 -> *)
(*        CE.find (base_ref r) wm1 = Some (type_of_cmpnttyp t3) -> *)
(*        type_of_hfexpr e ce0 = type_of_cmpnttyp t3 -> *)
(*        CE.vtyp (base_ref r) ce0 = (t0, c) -> *)
(*        is_deftyp (type_of_cmpnttyp t0) -> *)
(*        CE.vtyp (base_ref r) ce1 = (t3, c) -> *)
(*        ftype_equiv t1 (type_of_cmpnttyp t3) -> *)
(*        ~~ typeConstraintsGe t1 (type_of_cmpnttyp t3) -> *)
(*        inferWidth_sstmt_sem (Sfcnct r e) wm0 wm1 ce0 ce1 *)
(*    | inferWidth_sfcnct_ftype_le r e t0 t1 t3 c ce0 ce1 wm0 wm1 : *)
(*        CE.find (base_ref r) wm0 = Some (type_of_cmpnttyp t1) -> *)
(*        CE.find (base_ref r) wm1 = Some (type_of_cmpnttyp t1) -> *)
(*        type_of_hfexpr e ce0 = t3 -> *)
(*        CE.vtyp (base_ref r) ce0 = (t0, c) -> *)
(*        is_deftyp (type_of_cmpnttyp t0) -> *)
(*        CE.vtyp (base_ref r) ce1 = (t1, c) -> *)
(*        ftype_equiv (type_of_cmpnttyp t1) t3-> *)
(*        typeConstraintsGe (type_of_cmpnttyp t1) (t3) -> *)
(*        inferWidth_sstmt_sem (Sfcnct r e) wm0 wm1 ce0 ce1 *)
(*    | inferWidth_spcnct_ftype_gt r e t0 t1 t3 c ce0 ce1 wm0 wm1 : *)
(*        CE.find (base_ref r) wm0 = Some t1 -> *)
(*        CE.find (base_ref r) wm1 = Some (type_of_cmpnttyp t3) -> *)
(*        type_of_hfexpr e ce0 = type_of_cmpnttyp t3 -> *)
(*        CE.vtyp (base_ref r) ce0 = (t0, c) -> *)
(*        is_deftyp (type_of_cmpnttyp t0) -> *)
(*        CE.vtyp (base_ref r) ce1 = (t3, c) -> *)
(*        ftype_weak_equiv t1 (type_of_cmpnttyp t3) -> *)
(*        ~~ typeConstraintsGe t1 (type_of_cmpnttyp t3) -> *)
(*        inferWidth_sstmt_sem (Spcnct r e) wm0 wm1 ce0 ce1 *)
(*    | inferWidth_spcnct_ftype_le r e t0 t1 t3 c ce0 ce1 wm0 wm1 : *)
(*        CE.find (base_ref r) wm0 = Some (type_of_cmpnttyp t1) -> *)
(*        CE.find (base_ref r) wm1 = Some (type_of_cmpnttyp t1) -> *)
(*        type_of_hfexpr e ce0 = t3 -> *)
(*        CE.vtyp (base_ref r) ce0 = (t0, c) -> *)
(*        is_deftyp (type_of_cmpnttyp t0) -> *)
(*        CE.vtyp (base_ref r) ce1 = (t1, c) -> *)
(*        ftype_weak_equiv (type_of_cmpnttyp t1) t3 -> *)
(*        typeConstraintsGe (type_of_cmpnttyp t1) (t3) -> *)
(*        inferWidth_sstmt_sem (Spcnct r e) wm0 wm1 ce0 ce1 *)
(*    | inferWidth_sfcnct_tmp r e t0 wm0 wm1 ce0 ce1 : *)
(*        type_of_ref r ce0 = t0 -> *)
(*        CE.find (base_ref r) wm0 = CE.find (base_ref r) wm1 -> *)
(*        CE.find (base_ref r) ce0 = CE.find (base_ref r) ce1 -> *)
(*        ~~ is_deftyp t0 -> *)
(*        inferWidth_sstmt_sem (Sfcnct r e) wm0 wm1 ce0 ce1 *)
(*    | inferWidth_spcnct_tmp r e t0 wm0 wm1 ce0 ce1 : *)
(*        type_of_ref r ce0 = t0 -> *)
(*        CE.find (base_ref r) wm0 = CE.find (base_ref r) wm1 -> *)
(*        CE.find (base_ref r) ce0 = CE.find (base_ref r) ce1 -> *)
(*        ~~ is_deftyp t0 -> *)
(*        inferWidth_sstmt_sem (Spcnct r e) wm0 wm1 ce0 ce1 *)
(*    | inferWidth_swhen_t wm0 wm1 ce0 ce1 ce2 c s1 s2: *)
(*        inferWidth_stmts_sem (s1) ce0 ce1 -> *)
(*        inferWidth_stmts_sem (s2) ce1 ce2 -> *)
(*        inferWidth_sstmt_sem (Swhen c s1 s2) wm0 wm1 ce0 ce2 *)
(*    with *)
(*      inferWidth_stmts_sem : seq hfstmt -> cenv -> cenv -> Prop := *)
(*    | inferWidth_stmts_nil ce : *)
(*          inferWidth_stmts_sem nil ce ce *)
(*    | inferWidth_stmts_cons st sts (ce0 ce0' ce1 ce2 ce3 : cenv) : *)
(*        (inferType_stmts (st::sts) ce0 ce0' /\ forall v, CE.find v ce0' = CE.find v ce1) -> *)
(*        (exists wm1 wm2 , *)
(*        inferWidth_sstmt_sem st wm1 wm2 ce1 ce2) -> *)
(*        inferWidth_stmts_sem sts ce2 ce3 -> *)
(*        inferWidth_stmts_sem (st :: sts) ce1 ce3. *)
(*    (*End: old one*) *)

   
(*    Lemma inferWidth_snode_sem_conform : *)
(*      forall v e wm0 wm1 ce1 ce2, *)
(*        CE.find v ce1 = Some (aggr_typ (type_of_hfexpr e ce1), Node) -> *)
(*        wm1 = inferWidth_wmap0 (Snode v e) ce1 wm0 -> *)
(*        ce2 = wmap_map2_cenv wm1 ce1 -> *)
(*        inferWidth_sstmt_sem (Snode v e) wm0 wm1 ce1 ce2. *)
(*    Proof. *)
(*      intros. *)
(*      have Hin : (is_init (Snode v e)) by done. *)
(*      move : (init_new_comp_name Hin v) => Hnv. *)
(*      move : (new_v_wmap_none Hnv wm0) => Hn. *)
(*      rewrite H1/= H0. *)
(*      move : H0. *)
(*      rewrite /= Hn => Heqw01. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      move : (CELemmas.map2_1bis wm1 ce1 v Hnone). *)
(*      rewrite Heqw01 /=. *)
(*      move : Heqw01; case Hdf : (is_deftyp (type_of_hfexpr e ce1)). *)
(*      - move => Hwm1. *)
(*        move : (CELemmas.add_eq_o wm0 (type_of_hfexpr e ce1) (eq_refl v)) => Hwm01. *)
(*        rewrite Hwm01 -Hwm1 -/(wmap_map2_cenv wm1 ce1) -H1. *)
(*        move => Ht01.  *)
(*        apply inferWidth_snode_imp; try done. *)
(*        rewrite Hwm1 //.  *)
(*        rewrite Ht01 H /add_width_2_cenv/= Hdf//. *)
(*      - move => Hwm01. *)
(*        rewrite Hn -/(wmap_map2_cenv wm0 ce1) -Hwm01 -H1/= => Hce01. *)
(*        apply inferWidth_snode_exp; [done | rewrite(negbT Hdf)//|done | done ]. *)
(*    Qed. *)

(*    Lemma inferWidth_swire_exp_sem_conform : *)
(*      forall v t wm1 wm2 ce1 ce2, *)
(*        ~~ is_deftyp t -> *)
(*        CE.find v ce1 = Some (aggr_typ t, Wire) ->  *)
(*        wm2 = inferWidth_wmap0 (Swire v t) ce1 wm1 -> *)
(*        ce2 = wmap_map2_cenv wm2 ce1 -> *)
(*        inferWidth_sstmt_sem (Swire v t) wm1 wm2 ce1 ce2. *)
(*    Proof. *)
(*      intros. *)
(*      rewrite H2/=. *)
(*      have Hin : (is_init (Swire v t)) by done.  *)
(*      move : (init_new_comp_name Hin v) => Hnv. *)
(*      move : H1. rewrite /= (negbTE H) => Heqw12. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      move : (CELemmas.map2_1bis wm1 ce1 v Hnone). *)
(*      rewrite H0/= (new_v_wmap_none Hnv wm1). *)
(*      rewrite -/(wmap_map2_cenv wm1 ce1) -Heqw12 -H2/= => Hfm. *)
(*      apply inferWidth_swire_exp; try done. *)
(*      rewrite Hfm//. *)
(*    Qed. *)
   
(*    Lemma inferWidth_swire_imp_sem_conform : *)
(*      forall v t wm1 wm2 ce1 ce2, *)
(*        is_deftyp t -> *)
(*        CE.find v ce1 = Some (aggr_typ t, Wire) -> *)
(*        wm2 = inferWidth_wmap0 (Swire v t) ce1 wm1 -> *)
(*        ce2 = wmap_map2_cenv wm2 ce1 -> *)
(*        inferWidth_sstmt_sem (Swire v t) wm1 wm2 ce1 ce2. *)
(*    Proof.  *)
(*      intros. *)
(*      have Hin : (is_init (Swire v t)) by done. *)
(*      move : (init_new_comp_name Hin v) => Hnv. *)
(*      move : (new_v_wmap_none Hnv wm1) => Hn. *)
(*      rewrite H1 /= H Hn. *)
(*      move : H1. rewrite /= H Hn => Hw2. *)
(*      apply inferWidth_swire_imp; try done. *)
(*      - exact : (CELemmas.add_eq_o _ _ (eq_refl v)). *)
(*      - *)
(*        rewrite H2 /wmap_map2_cenv. *)
(*        have Hnone : (add_width_2_cenv None None = None) by done. *)
(*        rewrite (CELemmas.map2_1bis _ _ _ Hnone) . *)
(*        rewrite Hw2 (CELemmas.add_eq_o _ _ (eq_refl v)) H0. *)
(*        rewrite /add_width_2_cenv/= H//. *)
(*    Qed. *)

(*    Lemma inferWidth_swire_sem_conform : *)
(*      forall v t wm1 wm2 ce1 ce2, *)
(*        CE.find v ce1 = Some (aggr_typ t, Wire) -> *)
(*        wm2 = inferWidth_wmap0 (Swire v t) ce1 wm1 -> *)
(*        ce2 = wmap_map2_cenv wm2 ce1 -> *)
(*        CE.find v wm1 = None -> *)
(*        inferWidth_sstmt_sem (Swire v t) wm1 wm2 ce1 ce2. *)
(*    Proof. *)
(*      intros. *)
(*      have Hin : (is_init (Swire v t)) by done. *)
(*      move :(init_new_comp_name Hin v) => Hnv. *)
(*      move : (new_v_wmap_none Hnv wm1) => Hn. *)
(*      case Hdf : (is_deftyp t). *)
(*      apply inferWidth_swire_imp_sem_conform; try done. *)
(*      apply inferWidth_swire_exp_sem_conform ; try done. *)
(*      rewrite Hdf//. *)
(*    Qed. *)
   
(*    Lemma inferWidth_sreg_exp_sem_conform : *)
(*      forall v r wm1 wm2 ce2 ce3, *)
(*        ~~ is_deftyp (type r) -> *)
(*        CE.find v ce2 = Some (reg_typ r, Register) -> *)
(*        wm2 = inferWidth_wmap0 (Sreg v r) ce2 wm1 -> *)
(*        ce3 = wmap_map2_cenv wm2 ce2 -> *)
(*        inferWidth_sstmt_sem (Sreg v r) wm1 wm2 ce2 ce3. *)
(*    Proof. *)
(*      intros. rewrite H1.  *)
(*      move : H1. *)
(*      have Hin : (is_init (Sreg v r)) by done.  *)
(*      move : (init_new_comp_name Hin v) => Hnv. *)
(*      move : (new_v_wmap_none Hnv wm1) => Hn. *)
(*      rewrite/= Hn (negbTE H) => Heqw12. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      move : (CELemmas.map2_1bis wm1 ce2 v Hnone). *)
(*      rewrite Hn /=. rewrite -/(wmap_map2_cenv wm1 ce2) -Heqw12 -H2. *)
(*      move => Hfeq. symmetry in Hfeq. *)
(*      apply inferWidth_sreg_exp; done. *)
(*    Qed. *)

(*    Lemma inferWidth_sreg_imp_sem_conform : *)
(*      forall v r wm1 wm2 ce2 ce3, *)
(*        is_deftyp (type r) -> *)
(*        CE.find v ce2 = Some (reg_typ r, Register) -> *)
(*        wm2 = inferWidth_wmap0 (Sreg v r) ce2 wm1 -> *)
(*        ce3 = wmap_map2_cenv wm2 ce2 -> *)
(*        inferWidth_sstmt_sem (Sreg v r) wm1 wm2 ce2 ce3. *)
(*    Proof. *)
(*      intros. *)
(*      have Hin : (is_init (Sreg v r)) by done.  *)
(*      move : (init_new_comp_name Hin v) => Hnv. *)
(*      move : (new_v_wmap_none Hnv wm1) => Hn. *)
(*      rewrite H1 /= H Hn. *)
(*      move : H1. rewrite /= H Hn => Hw2. *)
(*      apply inferWidth_sreg_imp; [ done| done| done| |]. *)
(*      - exact : (CELemmas.add_eq_o _ _ (eq_refl v)). *)
(*      - rewrite H2 /wmap_map2_cenv. *)
(*        have Hnone : (add_width_2_cenv None None = None) by done. *)
(*        rewrite (CELemmas.map2_1bis _ _ _ Hnone) . *)
(*        rewrite Hw2 (CELemmas.add_eq_o _ _ (eq_refl v)) H0. *)
(*        rewrite /add_width_2_cenv/=. *)
(*        case (is_deftyp (type r)); try done. *)
(*        case r; done. *)
(*    Qed. *)

(*    Lemma inferWidth_sreg_sem_conform : *)
(*      forall v t wm1 wm2 ce2 ce3, *)
(*        CE.find v ce2 = Some (reg_typ t, Register) -> *)
(*        wm2 = inferWidth_wmap0 (Sreg v t) ce2 wm1 -> *)
(*        ce3 = wmap_map2_cenv wm2 ce2 -> *)
(*        inferWidth_sstmt_sem (Sreg v t) wm1 wm2 ce2 ce3. *)
(*    Proof. *)
(*      intros. *)
(*      case Hdf : (is_deftyp (type t)). *)
(*      apply inferWidth_sreg_imp_sem_conform; try done. *)
(*      apply inferWidth_sreg_exp_sem_conform; try done. *)
(*      rewrite Hdf//. *)
(*    Qed. *)

(*    Lemma inferWidth_smem_sem_conform : *)
(*      forall v m wm1 wm2 ce2 ce3, *)
(*        CE.find v ce2 = Some (mem_typ m, Memory) -> *)
(*        wm2 = inferWidth_wmap0 (Smem v m) ce2 wm1 -> *)
(*        ce3 = wmap_map2_cenv wm2 ce2 -> *)
(*        inferWidth_sstmt_sem (Smem v m) wm1 wm2 ce2 ce3. *)
(*    Proof. *)
(*      intros. *)
(*      have Hin : (is_init (Smem v m)) by done.  *)
(*      move : (init_new_comp_name Hin v) => Hnv. *)
(*      move : (new_v_wmap_none Hnv wm1) => Hn. *)
(*      rewrite H1 H0/=. *)
(*      apply inferWidth_smem with (mem_typ m); try done. *)
(*      intros. *)
(*      rewrite /wmap_map2_cenv. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      rewrite (CELemmas.map2_1bis _ _ _ Hnone) Hn/=//. *)
(*    Qed. *)

(*    Lemma inferWidth_sinst_sem_conform : *)
(*      forall v t m wm1 wm2 ce2 ce3, *)
(*        CE.find v ce2 = Some (t, Instanceof) -> *)
(*        wm2 = inferWidth_wmap0 (Sinst v m) ce2 wm1 -> *)
(*        ce3 = wmap_map2_cenv wm2 ce2 -> *)
(*        inferWidth_sstmt_sem (Sinst v m) wm1 wm2 ce2 ce3. *)
(*    Proof. *)
(*      intros. *)
(*      have Hin : (is_init (Sinst v m)) by done.  *)
(*      move : (init_new_comp_name Hin v) => Hnv. *)
(*      move : (new_v_wmap_none Hnv wm1) => Hn. *)
(*      rewrite H1 H0/=. *)
(*      apply inferWidth_sinst with t Instanceof; try done. *)
(*      rewrite /wmap_map2_cenv. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      rewrite (CELemmas.map2_1bis _ _ _ Hnone)/= Hn//. *)
(*    Qed. *)
   
(*    Lemma sizeof_fgtyp_lt_max_width t1 t2 : *)
(*      ftype_equiv (Gtyp t1) (Gtyp t2) -> *)
(*      sizeof_fgtyp t1 <= sizeof_fgtyp t2 -> *)
(*      max_width (Gtyp t1) (Gtyp t2) = Gtyp t2. *)
(*    Proof. *)
(*      elim t1; elim t2; rewrite /=; intros; *)
(*        try (rewrite (maxn_idPr H0)//|| discriminate|| done). *)
(*    Qed. *)

(*    Parameter typeConstraints_max_width :forall t1 t2, *)
(*      ftype_equiv t1 t2 -> *)
(*      typeConstraintsGe t1 t2 -> *)
(*      max_width t1 t2 = t1. *)
(*    Parameter typeConstraints_weak_max_width: forall t1 t2 , *)
(*      ftype_weak_equiv t1 t2 -> *)
(*      typeConstraintsGe t1 t2 -> *)
(*      max_width t1 t2 = t1. *)
(*    Parameter max_width_typeConstraints: forall t1 t2, *)
(*      ftype_equiv t1 t2 -> *)
(*      max_width t1 t2 = t1 -> *)
(*      typeConstraintsGe t1 t2. *)

(*    Lemma max_width_weak_typeConstraints t1 t2 :  *)
(*      ftype_weak_equiv t1 t2 -> *)
(*      max_width t1 t2 = t1 -> *)
(*      typeConstraintsGe t1 t2. *)
(*    Proof. Admitted. *)
     
(*    Lemma neg_typeConstraints_max_width t1 t2 : *)
(*      ftype_equiv t1 t2 -> *)
(*      ~~ (typeConstraintsGe t1 t2) -> *)
(*      max_width t1 t2 = t2. *)
(*    Proof. *)
(*    Admitted. *)
        
(*    Lemma neg_typeConstraints_weak_max_width t1 t2 : *)
(*      ftype_weak_equiv t1 t2 -> *)
(*      ~~ (typeConstraintsGe t1 t2) -> *)
(*      max_width t1 t2 = t2. *)
(*    Proof. Admitted. *)
 
(*    Lemma add_ref_wmap0_max_width r t1 t2 ce wm : *)
(*      CE.find (base_ref r) wm = Some t1 -> *)
(*      CE.find (base_ref r) (add_ref_wmap0 r t2 ce wm) = Some (max_width t1 t2). *)
(*    Proof. Admitted. *)

(*    Lemma inferWidth_sfcnct_ftype_sem_conform : *)
(*      forall r e c1 t0 t1 t2 wm1 ce1 wm2 ce2 , *)
(*        ftype_equiv t1 t2 -> *)
(*        CE.find (base_ref r) ce1 =  Some (t0, c1) -> *)
(*        type_of_ref r ce1 = type_of_cmpnttyp t0 -> *)
(*        is_deftyp (type_of_cmpnttyp t0) -> *)
(*        type_of_hfexpr e ce1 = t2 -> *)
(*        CE.find (base_ref r) wm1 = Some t1 -> *)
(*        wm2 = inferWidth_wmap0 (Sfcnct r e) ce1 wm1 -> *)
(*        ce2 = wmap_map2_cenv wm2 ce1 -> *)
(*        ~~ find_unknown (base_ref r) ce1  -> *)
(*        inferWidth_sstmt_sem (Sfcnct r e) wm1 wm2 ce1 ce2. *)
(*    Proof. *)
(*      intros. rewrite H6 H5 /= H1 H3 H2. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      move : (CE.find_some_vtyp H0) => Hv. *)
(*      move : H0 H1 H2 Hv. *)
(*      case : t0; rewrite /= ; intros. *)
(*      - case Hmax : (typeConstraintsGe t1 t2). *)
(*        + move : (typeConstraints_max_width H Hmax) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*            try (apply inferWidth_sfcnct_ftype_le with (aggr_typ f) (aggr_typ t1) t2 c1; *)
(*                 [ done *)
(*                 | rewrite -Hmw (add_ref_wmap0_max_width _ _ H4) /=Hmw// *)
(*                 | done| done| done *)
(*                 | apply (CE.find_some_vtyp); *)
(*                   rewrite /wmap_map2_cenv/= (CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*                 |done *)
(*                 | done]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_sfcnct_ftype_le with (aggr_typ f) (aggr_typ t1) t2 c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. *)
(*          rewrite /wmap_map2_cenv /=(CELemmas.map2_1bis _ _ _ Hnone) (add_ref_wmap0_max_width _ _ H4). *)
(*          rewrite Hmw H0/= H2//. *)
(*        + move : (neg_typeConstraints_max_width H (negbT Hmax)) => Hmw. *)
(*          move : H3 H6. *)
(*          case e; intros; *)
(*           try (apply inferWidth_sfcnct_ftype_gt with (aggr_typ f) t1 (aggr_typ t2) c1; *)
(*               [ done *)
(*               | rewrite (add_ref_wmap0_max_width _ _ H4) Hmw// *)
(*               | done| done | done  *)
(*               | apply CE.find_some_vtyp; rewrite /wmap_map2_cenv(CELemmas.map2_1bis _ _ _ Hnone); *)
(*                 rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*               | done *)
(*               | rewrite Hmax//]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_sfcnct_ftype_gt with (aggr_typ f) t1 (aggr_typ t2) c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//. *)
(*          rewrite /= Hmax//. *)
(*      - case Hmax : (typeConstraintsGe t1 t2). *)
(*        + move : (typeConstraints_max_width H Hmax) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*             try (apply inferWidth_sfcnct_ftype_le with (reg_typ h) (reg_typ (mk_freg t1 (clock h) (reset h))) t2 c1; *)
(*                 [ done *)
(*                 | rewrite -Hmw (add_ref_wmap0_max_width _ _ H4) /=Hmw// *)
(*                 | done| done| done *)
(*                 | apply (CE.find_some_vtyp); *)
(*                   rewrite /wmap_map2_cenv/= (CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*                 | done *)
(*                 | done]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_sfcnct_ftype_le with (reg_typ h) (reg_typ (mk_freg t1 (clock h) (reset h))) t2 c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. *)
(*          rewrite /wmap_map2_cenv /=(CELemmas.map2_1bis _ _ _ Hnone) (add_ref_wmap0_max_width _ _ H4). *)
(*          rewrite Hmw H0/= H2//. *)
(*        + move : (neg_typeConstraints_max_width H (negbT Hmax)) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*            try (apply inferWidth_sfcnct_ftype_gt with (reg_typ h) t1 (reg_typ (mk_freg t2 (clock h) (reset h))) c1; *)
(*                 [ done *)
(*                 | rewrite (add_ref_wmap0_max_width _ _ H4) Hmw// *)
(*                 | done| done | done *)
(*                 | apply CE.find_some_vtyp; rewrite /wmap_map2_cenv(CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*                 | done *)
(*                 | rewrite Hmax//]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_sfcnct_ftype_gt with (reg_typ h) t1 (reg_typ (mk_freg t2 (clock h) (reset h))) c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//. *)
(*          rewrite /= Hmax//. *)
(*      - case Hmax : (typeConstraintsGe t1 t2). *)
(*        + move : (typeConstraints_max_width H Hmax) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*          try (apply inferWidth_sfcnct_ftype_le with *)
(*              (mem_typ h) (mem_typ (mk_fmem t1 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) t2 c1; *)
(*                 [ done *)
(*                 | rewrite -Hmw (add_ref_wmap0_max_width _ _ H4) /=Hmw// *)
(*                 | done| done| done *)
(*                 | apply (CE.find_some_vtyp); *)
(*                   rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*                 | done *)
(*                 | done]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_sfcnct_ftype_le with (mem_typ h) (mem_typ (mk_fmem t1 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) t2 c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//. *)
(*        + move : (neg_typeConstraints_max_width H (negbT Hmax)) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*            try (apply inferWidth_sfcnct_ftype_gt with (mem_typ h) t1 (mem_typ (mk_fmem t2 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) c1; *)
(*                 [ done *)
(*                 | rewrite (add_ref_wmap0_max_width _ _ H4) Hmw// *)
(*                 | done| done | done *)
(*                 | apply CE.find_some_vtyp; rewrite /wmap_map2_cenv(CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*                 | done *)
(*                 | rewrite Hmax//]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_sfcnct_ftype_gt with (mem_typ h) t1 (mem_typ (mk_fmem t2 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//. *)
(*          rewrite /= Hmax//. *)
(*      - rewrite /find_unknown H0 in H7.  discriminate. *)
(*    Qed. *)

(*    Lemma inferWidth_spcnct_ftype_sem_conform : *)
(*      forall r e c1 t0 t1 t2 wm1 ce1 wm2 ce2 , *)
(*        ftype_weak_equiv t1 t2 -> *)
(*        CE.find (base_ref r) ce1 =  Some (t0, c1) -> *)
(*        type_of_ref r ce1 = type_of_cmpnttyp t0 -> *)
(*        is_deftyp (type_of_cmpnttyp t0) -> *)
(*        type_of_hfexpr e ce1 = t2 -> *)
(*        CE.find (base_ref r) wm1 = Some t1 -> *)
(*        wm2 = inferWidth_wmap0 (Spcnct r e) ce1 wm1 -> *)
(*        ce2 = wmap_map2_cenv wm2 ce1 -> *)
(*        ~~ find_unknown (base_ref r) ce1 -> *)
(*        inferWidth_sstmt_sem (Spcnct r e) wm1 wm2 ce1 ce2. *)
(*    Proof. *)
(*      intros. rewrite H6 H5 /= H1 H3 H2. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      move : (CE.find_some_vtyp H0) => Hv. *)
(*      move : H0 H1 H2 Hv. *)
(*      case : t0; rewrite /= ; intros. *)
(*      - case Hmax : (typeConstraintsGe t1 t2). *)
(*        + move : (typeConstraints_weak_max_width H Hmax) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*            try (apply inferWidth_spcnct_ftype_le with (aggr_typ f) (aggr_typ t1) t2 c1; *)
(*                 [ done *)
(*                 | rewrite -Hmw (add_ref_wmap0_max_width _ _ H4) /=Hmw// *)
(*                 | done| done| done *)
(*                 | apply (CE.find_some_vtyp); *)
(*                   rewrite /wmap_map2_cenv/= (CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*                 | done *)
(*                 | done]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_spcnct_ftype_le with (aggr_typ f) (aggr_typ t1) t2 c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. *)
(*          rewrite /wmap_map2_cenv /=(CELemmas.map2_1bis _ _ _ Hnone) (add_ref_wmap0_max_width _ _ H4). *)
(*          rewrite Hmw H0/= H2//. *)
(*        + move : (neg_typeConstraints_weak_max_width H (negbT Hmax)) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*          try (apply inferWidth_spcnct_ftype_gt with (aggr_typ f) t1 (aggr_typ t2) c1; *)
(*               [ done *)
(*               | rewrite (add_ref_wmap0_max_width _ _ H4) Hmw// *)
(*               | done| done | done *)
(*               | apply CE.find_some_vtyp; rewrite /wmap_map2_cenv(CELemmas.map2_1bis _ _ _ Hnone); *)
(*                 rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*               | done *)
(*               | rewrite Hmax//]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_spcnct_ftype_gt with (aggr_typ f) t1 (aggr_typ t2) c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//. *)
(*          rewrite /= Hmax//. *)
(*      - case Hmax : (typeConstraintsGe t1 t2). *)
(*        + move : (typeConstraints_weak_max_width H Hmax) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*             try (apply inferWidth_spcnct_ftype_le with (reg_typ h) (reg_typ (mk_freg t1 (clock h) (reset h))) t2 c1; *)
(*                 [ done *)
(*                 | rewrite -Hmw (add_ref_wmap0_max_width _ _ H4) /=Hmw// *)
(*                 | done| done| done *)
(*                 | apply (CE.find_some_vtyp); *)
(*                   rewrite /wmap_map2_cenv/= (CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*                 | done *)
(*                 | done]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_spcnct_ftype_le with (reg_typ h) (reg_typ (mk_freg t1 (clock h) (reset h))) t2 c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. *)
(*          rewrite /wmap_map2_cenv /=(CELemmas.map2_1bis _ _ _ Hnone) (add_ref_wmap0_max_width _ _ H4). *)
(*          rewrite Hmw H0/= H2//. *)
(*        + move : (neg_typeConstraints_weak_max_width H (negbT Hmax)) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*            try (apply inferWidth_spcnct_ftype_gt with (reg_typ h) t1 (reg_typ (mk_freg t2 (clock h) (reset h))) c1; *)
(*                 [ done *)
(*                 | rewrite (add_ref_wmap0_max_width _ _ H4) Hmw// *)
(*                 | done| done | done *)
(*                 | apply CE.find_some_vtyp; rewrite /wmap_map2_cenv(CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*                 | done *)
(*                 | rewrite Hmax//]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_spcnct_ftype_gt with (reg_typ h) t1 (reg_typ (mk_freg t2 (clock h) (reset h))) c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//. *)
(*          rewrite /= Hmax//. *)
(*      - case Hmax : (typeConstraintsGe t1 t2). *)
(*        + move : (typeConstraints_weak_max_width H Hmax) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*          try (apply inferWidth_spcnct_ftype_le with *)
(*              (mem_typ h) (mem_typ (mk_fmem t1 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) t2 c1; *)
(*                 [ done *)
(*                 | rewrite -Hmw (add_ref_wmap0_max_width _ _ H4) /=Hmw// *)
(*                 | done| done| done *)
(*                 | apply (CE.find_some_vtyp); *)
(*                   rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*                 | done *)
(*                 | done]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_spcnct_ftype_le with (mem_typ h) (mem_typ (mk_fmem t1 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) t2 c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//. *)
(*        + move : (neg_typeConstraints_weak_max_width H (negbT Hmax)) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*            try (apply inferWidth_spcnct_ftype_gt with (mem_typ h) t1 (mem_typ (mk_fmem t2 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) c1; *)
(*                 [ done *)
(*                 | rewrite (add_ref_wmap0_max_width _ _ H4) Hmw// *)
(*                 | done| done | done *)
(*                 | apply CE.find_some_vtyp; rewrite /wmap_map2_cenv(CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*                 | done *)
(*                 | rewrite Hmax//]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_spcnct_ftype_gt with (mem_typ h) t1 (mem_typ (mk_fmem t2 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//. *)
(*          rewrite /= Hmax//. *)
(*      - rewrite /find_unknown H0 in H7. discriminate. *)
(*    Qed. *)

(*    Lemma inferWidth_sskip_sem_conform : *)
(*      forall wm1 wm2 ce1 ce2, *)
(*        wm2 = inferWidth_wmap0 sskip ce1 wm1 -> *)
(*        ce2 = wmap_map2_cenv wm2 ce1 -> *)
(*        inferWidth_sstmt_sem (sskip) wm1 wm2 ce1 ce2. *)
(*    Proof. *)
(*      move => wm1 wm2 ce1 ce2 H H1. rewrite /= in H. *)
(*      apply inferWidth_sskip. intros. *)
(*      rewrite H1 H. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*      rewrite H0 H2. *)
(*      case t; rewrite /=; intros; try done. *)
(*      case (is_deftyp f); done. *)
(*      case (is_deftyp (type h)); try done. *)
(*      case h; intros; rewrite /=//. *)
(*      case (is_deftyp (data_type h)); try done. *)
(*      case h; intros; rewrite //. *)
(*    Qed. *)

(*    Lemma inferWidth_sstop_sem_conform : *)
(*      forall wm1 wm2 ce1 ce2 ss1 ss2 n, *)
(*        wm2 = inferWidth_wmap0 (sstop ss1 ss2 n) ce1 wm1 -> *)
(*        ce2 = wmap_map2_cenv wm2 ce1 -> *)
(*        inferWidth_sstmt_sem (sstop ss1 ss2 n) wm1 wm2 ce1 ce2. *)
(*    Proof. *)
(*      move => wm1 wm2 ce1 ce2 ss1 ss2 n H H1. rewrite /= in H. *)
(*      apply inferWidth_sstop. intros. *)
(*      rewrite H1 H. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*      rewrite H0 H2. *)
(*      case t; rewrite /=; intros; try done. *)
(*      case (is_deftyp f); done. *)
(*      case (is_deftyp (type h)); try done. *)
(*      case h; intros; rewrite /=//. *)
(*      case (is_deftyp (data_type h)); try done. *)
(*      case h; intros; rewrite //. *)
(*    Qed. *)

(*    Lemma inferWidth_sinvalid_sem_conform : *)
(*      forall wm1 wm2 ce1 ce2 v, *)
(*        wm2 = inferWidth_wmap0 (sinvalid v) ce1 wm1 -> *)
(*        ce2 = wmap_map2_cenv wm2 ce1 -> *)
(*        inferWidth_sstmt_sem (sinvalid v) wm1 wm2 ce1 ce2. *)
(*    Proof. *)
(*      move => wm1 wm2 ce1 ce2 v H H1. rewrite /= in H. *)
(*      apply inferWidth_sinvalid. intros. *)
(*      rewrite H1 H. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*      rewrite H0 H2. *)
(*      case t; rewrite /=; intros; try done. *)
(*      case (is_deftyp f); done. *)
(*      case (is_deftyp (type h)); try done. *)
(*      case h; intros; rewrite /=//. *)
(*      case (is_deftyp (data_type h)); try done. *)
(*      case h; intros; rewrite //. *)
(*    Qed. *)
     
(*    Parameter cefind_eq_eq_width : *)
(*      forall v (ce1 ce2 : cenv) t1 t2 c, *)
(*        CE.find v ce1 = Some (t1, c) -> *)
(*        CE.find v ce2 = Some (t2, c) -> *)
(*        CE.find v ce1 = CE.find v ce2 -> *)
(*        typeConstraintsGe (type_of_cmpnttyp t2) (type_of_cmpnttyp t1). *)

(*    Parameter infer_stmt_lst: forall st ss ce1 wm1 , *)
(*        wm1 = inferWidth_wmap0 st ce1 empty_wmap0 -> *)
(*        inferWidth_fun (cons st ss) ce1 = inferWidth_fun ss (wmap_map2_cenv wm1 ce1). *)

(*    Lemma inferType_stmts_hd ss sts ce0 ce1 : *)
(*      inferType_stmts (cons ss sts) ce0 ce1 -> *)
(*      inferType_stmt ss ce0 ce1. *)
(*    Proof. *)
(*    Admitted. *)

(*    Parameter type_of_hexpr_cefind : forall r ce t, *)
(*      CE.find (base_ref r) ce = Some t -> *)
(*      type_of_ref (r) ce = type_of_cmpnttyp (fst t). *)

(*    Definition is_inital (s : hfstmt) : bool := *)
(*      match s with *)
(*      | Spcnct _ _ | Sfcnct _ _ | Sinvalid _ | Swhen _ _ _ *)
(*      | Sstop _ _ _ | Sskip => false *)
(*      | _ => true *)
(*      end. *)

(*    Fixpoint is_inital_all_t (s : seq hfstmt) : bool := *)
(*      match (s) with *)
(*      | nil => true *)
(*      | cons h t => if (is_inital h) then is_inital_all_t t else false *)
(*      end. *)

(*    Fixpoint not_inital_all (s : seq hfstmt) : bool := *)
(*      match s with *)
(*      | nil => true *)
(*      | cons h t => if (is_inital h) then false else not_inital_all t *)
(*      end. *)

(*    Parameter not_init_wmfind_some : *)
(*      forall s, ~~ is_init s -> forall v (wm:wmap0) t, CE.find v wm = Some t. *)
(*    Parameter infer_types_no_unknown_type : *)
(*      forall sts ce0 ce1, inferType_stmts sts ce0 ce1 -> forall v c, ~ (CE.find v ce1 = Some (unknown_typ, c)). *)
(*    Parameter infer_type_no_unknown_type : *)
(*      forall st ce0 ce1, inferType_stmt st ce0 ce1 -> forall v c, ~ (CE.find v ce1 = Some (unknown_typ, c)). *)

(*    Parameter find_same_ce_wmap2ce : *)
(*      forall v (ce1 ce2: cenv) wm1, *)
(*      CE.find v ce1 = CE.find v ce2 -> *)
(*      wmap_map2_cenv wm1 ce1 = wmap_map2_cenv wm1 ce2. *)

(*    Parameter typeof_same_ce : *)
(*      forall v e (ce1 ce2: cenv) , *)
(*      CE.find v ce1 = CE.find v ce2 -> *)
(*      type_of_hfexpr e ce1 = type_of_hfexpr e ce2. *)
(*    Parameter typeofr_same_ce : *)
(*      forall v e (ce1 ce2: cenv) , *)
(*      CE.find v ce1 = CE.find v ce2 -> *)
(*      type_of_ref e ce1 = type_of_ref e ce2. *)
(*    Parameter add_wmap_same_ce : *)
(*      forall h t (ce1 ce2: cenv) wm, *)
(*      CE.find (base_ref h) ce1 = CE.find (base_ref h) ce2 -> *)
(*      add_ref_wmap0 h t ce1 wm = *)
(*    add_ref_wmap0 h t ce2 wm. *)
   

(*    Parameter wmap_empty : forall ce, *)
(*        (wmap_map2_cenv empty_wmap0 ce) = ce. *)

(*    Parameter inferType_hd_tl : forall ss st ce0 ce1, *)
(*        inferType_stmts (st::ss) ce0 ce1 -> *)
(*        inferType_stmts ss (inferType_stmt_fun st ce0) ce1. *)

(*    Parameter wmap2_same : forall v wm ce, *)
(*        CE.find v wm = None -> *)
(*        CE.find v (wmap_map2_cenv wm ce) = CE.find v ce. *)

(*    Parameter inferWidth_unfold_swhen : *)
(*      forall ce1 wm1 h l l0, *)
(*        inferWidth_wmap0 (Swhen h l l0) ce1 wm1 = *)
(*        inferWidth_stmts_wmap0 (cat l l0) ce1 wm1. *)

(*    Parameter inferWidth_list_cat : *)
(*      forall ce1 wm1 l l0, *)
(*        inferWidth_stmts_wmap0 (l ++ l0) ce1 wm1 = *)
(*        inferWidth_stmts_wmap0 l0 ce1 (inferWidth_stmts_wmap0 l ce1 wm1). *)

(*    Parameter inferWidth_fun_list : *)
(*      forall ce1 wm1 l l0, *)
(*        wmap_map2_cenv (inferWidth_stmts_wmap0 l0 ce1 (inferWidth_stmts_wmap0 l ce1 wm1)) ce1 = *)
(*        wmap_map2_cenv (inferWidth_stmts_wmap0 l0 (wmap_map2_cenv (inferWidth_stmts_wmap0 l ce1 wm1) ce1) (inferWidth_stmts_wmap0 l ce1 wm1)) ce1. *)

(*    Parameter inferWidth_list_fold : *)
(*      forall l l0 ce1 wm1, *)
(*      wmap_map2_cenv (inferWidth_stmts_wmap0 l (wmap_map2_cenv (inferWidth_stmts_wmap0 l0 ce1 wm1) ce1) (inferWidth_stmts_wmap0 l0 ce1 wm1)) ce1 = *)
(*      inferWidth_fun l (inferWidth_fun l0 ce1). *)
   
(*    Lemma inferWidth_sstmt_stmts_sem_conform : *)
(*      forall st sts wm1 wm2 ce ce' ce0 ce0' ce1 ce2, *)
       
(*        ((forall st wm1 wm2 ce1 ce2, inferWidth_sstmt_sem st wm1 wm2 ce1 ce2 ) -> *)
(*         inferType_stmts sts ce ce' -> *)
(*         (forall v, CE.find v ce' = CE.find v ce1) -> *)
(*         inferWidth_stmts_sem (sts) ce1 (inferWidth_fun (sts) ce1)) *)
(*        /\ *)
(*        ((forall ce1 sts, inferWidth_stmts_sem (sts) ce1 (inferWidth_fun (sts) ce1)) -> *)
(*         inferType_stmt st ce0 ce0' -> *)
(*         (forall v, CE.find v ce0' = CE.find v ce1) -> *)
(*         wm2 = inferWidth_wmap0 st ce1 wm1 -> *)
(*         ce2 = wmap_map2_cenv wm2 ce1 -> *)
(*         inferWidth_sstmt_sem st wm1 wm2 ce1 ce2). *)
(*    Proof. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      split. *)
(*      move : sts ce ce' ce1 ce2.  *)
(*      elim => [ cece' ce1 ce2 Hce12 Hit Hwm1 Hce2 | s ss Hm ce ce' ce1 ce3 Hms Hit Hce12]. *)
(*      - rewrite /inferWidth_fun/= wmap_empty; apply inferWidth_stmts_nil.  *)
(*      - *)
(*        have Hin : ((is_init s) \/ ~~(is_init s)) by (case (is_init s); [by left| by right]). *)
(*        move : Hin => [Hin | Hin]. *)
(*        rewrite /inferWidth_fun. *)
(*        apply inferWidth_stmts_cons with ce ce' (wmap_map2_cenv (inferWidth_wmap0 s ce1 empty_wmap0) ce1) ; *)
(*          try done. *)
(*        exists wm1; exists wm2. apply Hms. *)
(*        rewrite -/(inferWidth_fun (s :: ss) ce1). *)
(*        erewrite infer_stmt_lst; try done. *)
(*        apply Hm with (inferType_stmt_fun s ce) ce'; try done. *)
(*        by apply inferType_hd_tl. *)
(*        intros. symmetry. rewrite (Hce12 v) . apply wmap2_same. *)
(*        apply new_v_wmap_none. by apply init_new_comp_name with s. *)
(*        rewrite /inferWidth_fun. *)
(*        apply inferWidth_stmts_cons with ce ce' (wmap_map2_cenv (inferWidth_wmap0 s ce1 empty_wmap0) ce1) ; *)
(*          try done. *)
(*        exists wm1; exists wm2. apply Hms. *)
(*        rewrite -/(inferWidth_fun (s :: ss) ce1). *)
(*        erewrite infer_stmt_lst; try done. *)
(*        apply Hm with (inferType_stmt_fun s ce) ce'; try done. *)
(*        by apply inferType_hd_tl. *)
(*        intros. *)
(*        move : (not_init_cefind_some Hin v (wmap_map2_cenv (inferWidth_wmap0 s ce1 empty_wmap0) ce1) (CE.vtyp v ce1)) => Haux. *)
(*        rewrite Haux. *)
(*        exact : (not_init_cefind_some Hin v ce' (CE.vtyp v ce1)). *)

(*        have Hin : ((is_init st) \/ ~~(is_init st)) by (case (is_init st); [by left| by right]). *)
(*        move : st wm1 wm2 ce0 ce0' ce1 ce2 Hin. *)
(*        elim . *)
(*        + (*skip*) *)
(*          intros.  *)
(*          apply inferWidth_sskip_sem_conform; try done. *)
(*        + (*swire*) *)
(*          move => s f wm1 wm2 ce0 ce0' ce1 ce2 Hin Hm Hit Hce12 Hwm2 Hce2. *)
(*          move : Hin => [Hin | Hin]; try rewrite //. *)
(*          move : (init_new_comp_name Hin s) => Hns. *)
(*          move : (new_v_wmap_none Hns wm1) => Hnv. *)
(*          apply inferWidth_swire_sem_conform; try done.  *)
(*          inversion Hit; subst. *)
(*          rewrite -H4 (Hce12 s)//. *)
(*        + (*reg*) *)
(*          intros. *)
(*          apply inferWidth_sreg_sem_conform; try done. *)
(*          inversion H0; subst. *)
(*          rewrite -H9 (H1 s)//. *)
(*        + (*mem*) *)
(*          intros. *)
(*          apply inferWidth_smem_sem_conform; try done. *)
(*          inversion H0; subst. *)
(*          rewrite -H9 (H1 s)//. *)
(*        + (*inst*) *)
(*          intros. *)
(*          apply inferWidth_sinst_sem_conform with (fst (CE.vtyp s0 ce0)); try done. *)
(*          inversion H0; subst. *)
(*          rewrite -H10  (H1 s)//. *)
(*        + (*node*) *)
(*          intros. *)
(*          apply inferWidth_snode_sem_conform; try done. *)
(*          inversion H0; subst. *)
(*          rewrite -(typeof_same_ce h (H1 s)) -H7 -H1//. *)
(*        + (*fcnct*) *)
(*          intros. *)
(*          move : Hin => [Hin|Hin]; try done. *)
(*          move : H0 => Hitc.  *)
(*          inversion Hitc; subst. *)
(*          move : H7 => [Hit1 [Hit2 Hit3]]. *)
(*          move : (not_init_wmfind_some Hin (base_ref h) wm1 (type_of_cmpnttyp t)) => Haux. *)
(*          case Hde : (is_deftyp (type_of_cmpnttyp t)). *)
(*          apply inferWidth_sfcnct_ftype_sem_conform with c t (type_of_cmpnttyp t) t'; try done. *)
(*          rewrite -(H1 (base_ref h))//. *)
(*          rewrite <-(typeofr_same_ce _ (H1 (base_ref h))).  *)
(*          rewrite (type_of_hexpr_cefind Hit1)//. *)
(*          rewrite <-(typeof_same_ce _ (H1 (base_ref h))). done. *)
(*          move : (infer_type_no_unknown_type Hitc) => Hfu. *)
(*          rewrite /find_unknown. move : (Hfu (base_ref h) c ). *)
(*          rewrite -(H1 (base_ref h)). *)
(*          rewrite Hit1. case t; try done. *)
(*          have Hit1' : CE.find (base_ref h) ce1 = Some (t, c) by rewrite -(H1 (base_ref h))//. *)
(*          apply inferWidth_sfcnct_tmp with (type_of_cmpnttyp t). *)
(*          rewrite (type_of_hexpr_cefind Hit1')//. *)
(*          rewrite /=(type_of_hexpr_cefind Hit1')/= Hde; case h0; done. *)
(*          rewrite /= -(H1 (base_ref h))/= (type_of_hexpr_cefind Hit1') /= Hde; case h0; intros; move : Hde; *)
(*            rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone) Haux Hit1 Hit1'; *)
(*            case t; rewrite /=; intros; try (rewrite Hde//|| discriminate). *)
(*          rewrite Hde//.          *)
(*        + (*pcnct*) *)
(*          intros. *)
(*          move : Hin => [Hin|Hin]; try done. *)
(*          move : H0 => Hitc.  *)
(*          inversion Hitc; subst. *)
(*          move : H7 => [Hit1 [Hit2 Hit3]]. *)
(*          move : (not_init_wmfind_some Hin (base_ref h) wm1 (type_of_cmpnttyp t)) => Haux. *)
(*          case Hde : (is_deftyp (type_of_cmpnttyp t)). *)
(*          apply inferWidth_spcnct_ftype_sem_conform with c t (type_of_cmpnttyp t) t'; try done. *)
(*          rewrite -(H1 (base_ref h))//. *)
(*          rewrite <-(typeofr_same_ce _ (H1 (base_ref h))).  *)
(*          rewrite (type_of_hexpr_cefind Hit1)//. *)
(*          rewrite <-(typeof_same_ce _ (H1 (base_ref h))). done. *)
(*          move : (infer_type_no_unknown_type Hitc) => Hfu. *)
(*          rewrite /find_unknown. move : (Hfu (base_ref h) c ). *)
(*          rewrite -(H1 (base_ref h)). *)
(*          rewrite Hit1. case t; try done. *)
(*          have Hit1' : CE.find (base_ref h) ce1 = Some (t, c) by rewrite -(H1 (base_ref h))//. *)
(*          apply inferWidth_spcnct_tmp with (type_of_cmpnttyp t). *)
(*          rewrite (type_of_hexpr_cefind Hit1')//. *)
(*          rewrite /=(type_of_hexpr_cefind Hit1')/= Hde; case h0; done. *)
(*          rewrite /= -(H1 (base_ref h))/= (type_of_hexpr_cefind Hit1') /= Hde; case h0; intros; move : Hde; *)
(*            rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone) Haux Hit1 Hit1'; *)
(*            case t; rewrite /=; intros; try (rewrite Hde//|| discriminate). *)
(*          rewrite Hde//. *)
(*        + (*invalid*) *)
(*          intros. *)
(*          apply inferWidth_sinvalid_sem_conform; try done. *)
(*        + (*when*) *)
(*          intros. *)
(*          apply inferWidth_swhen_t with (inferWidth_fun l ce1); try done. *)
(*          rewrite H3 H2. *)
(*          rewrite inferWidth_unfold_swhen inferWidth_list_cat. *)
(*          rewrite inferWidth_fun_list inferWidth_list_fold. *)
(*          apply H. *)
(*        + (* stop *) *)
(*          intros. *)
(*          apply inferWidth_sstop_sem_conform; try done. *)
(*    Qed. *)
     
(*    (* Lemma inferWidth_stmts_sem_conform' : *) *)
(*    (*   forall (sts:seq hfstmt) ce0 ce1 ce2 , *) *)
(*    (*     inferType_stmts sts ce0 ce1-> (forall v, CE.find v ce1 = CE.find v ce2) -> *) *)
(*    (*     inferWidth_stmts_sem (sts) ce2 (inferWidth_fun (sts) ce2). *) *)
(*    (* Proof. *) *)
(*    (*   have Hnone : (add_width_2_cenv None None = None) by done. *) *)
(*    (*   elim => [ce0 ce1 ce2 Hif Hfv | st ss Hm ce0 ce1 ce2 Hif Hce12]. *) *)
(*    (*   - rewrite /inferWidth_fun/= wmap_empty. apply inferWidth_stmts_nil.  *) *)
(*    (*   - *) *)
(*    (*     have Hin : ((is_init st) \/ ~~(is_init st)) by (case (is_init st); [by left| by right]). *) *)
(*    (*     rewrite /inferWidth_fun. *) *)
(*    (*     apply inferWidth_stmts_cons with ce0 ce1 (wmap_map2_cenv (inferWidth_wmap0 st ce2 empty_wmap0) ce2); try done. *) *)
(*    (*     inversion Hif; subst. *) *)
(*    (*     exists empty_wmap0 . exists (inferWidth_wmap0 st ce2 empty_wmap0). *) *)
(*    (*     move : Hif H1 Hin. *) *)
(*    (*     elim st. *) *)
(*    (*     + (*skip*) *) *)
(*    (*       intros.  *) *)
(*    (*       apply inferWidth_sskip_sem_conform; try done. *) *)
(*    (*     + (*swire*) *) *)
(*    (*       move => s f Hit Hits. move => [Hin | Hin]; try rewrite //. *) *)
(*    (*       move : (init_new_comp_name Hin s) => Hns. *) *)
(*    (*       move : (new_v_wmap_none Hns empty_wmap0) => Hnv. *) *)
(*    (*       apply inferWidth_swire_sem_conform'; try done.  *) *)
(*    (*       move : (inferType_stmts_hd Hit) => Hhd. inversion Hhd; subst. *) *)
(*    (*       rewrite -H5 (Hce12 s)//. *) *)
(*    (*     + (*reg*) *) *)
(*    (*       intros. *) *)
(*    (*       apply inferWidth_sreg_sem_conform'; try done. *) *)
(*    (*       move : (inferType_stmts_hd Hif) => Hhd. inversion Hhd; subst. *) *)
(*    (*       rewrite -H6 (Hce12 s)//. *) *)
(*    (*     + (*mem*) *) *)
(*    (*       intros. *) *)
(*    (*       apply inferWidth_smem_sem_conform'; try done. *) *)
(*    (*       move : (inferType_stmts_hd Hif) => Hhd. inversion Hhd; subst. *) *)
(*    (*       rewrite -H6 (Hce12 s)//. *) *)
(*    (*     + (*inst*) *) *)
(*    (*       intros. *) *)
(*    (*       apply inferWidth_sinst_sem_conform' with (fst (CE.vtyp s0 ce0)); try done. *) *)
(*    (*       move : (inferType_stmts_hd Hif) => Hhd. inversion Hhd; subst. *) *)
(*    (*       rewrite -H7 (Hce12 s)//. *) *)
(*    (*     + (*node*) *) *)
(*    (*       intros. *) *)
(*    (*       apply inferWidth_snode_sem_conform'; try done. *) *)
(*    (*       move : (inferType_stmts_hd Hif) => Hhd. inversion Hhd; subst. *) *)
(*    (*       rewrite -(typeof_same_ce h (Hce12 s)) -H3 -H7//. *) *)
(*    (*     + (*fcnct*) *) *)
(*    (*       intros. *) *)
(*    (*       move : Hin => [Hin|Hin]; try done. *) *)
(*    (*       move : (inferType_stmts_hd Hif) => Hitc.  *) *)
(*    (*       inversion Hitc; subst. *) *)
(*    (*       move : H5 => [Hit1 [Hit2 Hit3]]. *) *)
(*    (*       move : (not_init_wmfind_some Hin (base_ref h) empty_wmap0 (type_of_cmpnttyp t)) => Haux. *) *)
(*    (*       case Hde : (is_deftyp (type_of_cmpnttyp t)). *) *)
(*    (*       apply inferWidth_sfcnct_ftype_sem_conform with c t (type_of_cmpnttyp t) t'; try done. *) *)
(*    (*       rewrite -(Hce12 (base_ref h))//. *) *)
(*    (*       rewrite <-(typeofr_same_ce _ (Hce12 (base_ref h))).  *) *)
(*    (*       rewrite (type_of_hexpr_cefind Hit1)//. *) *)
(*    (*       rewrite <-(typeof_same_ce _ (Hce12 (base_ref h))). done. *) *)
(*    (*       rewrite /=.  *) *)
(*    (*       move : (infer_type_no_unknown_type H1) => Hfu. *) *)
(*    (*       rewrite /find_unknown. move : (Hfu (base_ref h) c ). *) *)
(*    (*       rewrite -(Hce12 (base_ref h)). *) *)
(*    (*       rewrite Hit1. case t; try done. *) *)
(*    (*       have Hit1' : CE.find (base_ref h) ce2 = Some (t, c) by rewrite -(Hce12 (base_ref h))//. *) *)
(*    (*       apply inferWidth_sfcnct_tmp with (type_of_cmpnttyp t). *) *)
(*    (*       rewrite (type_of_hexpr_cefind Hit1')//. *) *)
(*    (*       rewrite /=(type_of_hexpr_cefind Hit1')/= Hde; case h0; done. *) *)
(*    (*       rewrite /= -(Hce12 (base_ref h))/= (type_of_hexpr_cefind Hit1') /= Hde; case h0; intros; move : Hde; *) *)
(*    (*         rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone) Haux Hit1 Hit1'; *) *)
(*    (*         case t; rewrite /=; intros; try (rewrite Hde//|| discriminate). *) *)
(*    (*       rewrite Hde//.          *) *)
(*    (*     + (*pcnct*) *) *)
(*    (*       intros. *) *)
(*    (*       move : Hin => [Hin|Hin]; try done. *) *)
(*    (*       move : (inferType_stmts_hd Hif) => Hitc.  *) *)
(*    (*       inversion Hitc; subst. *) *)
(*    (*       move : H5 => [Hit1 [Hit2 Hit3]]. *) *)
(*    (*       move : (not_init_wmfind_some Hin (base_ref h) empty_wmap0 (type_of_cmpnttyp t)) => Haux. *) *)
(*    (*       case Hde : (is_deftyp (type_of_cmpnttyp t)). *) *)
(*    (*       apply inferWidth_spcnct_ftype_sem_conform with c t (type_of_cmpnttyp t) t'; try done. *) *)
(*    (*       rewrite -(Hce12 (base_ref h))//. *) *)
(*    (*       rewrite <-(typeofr_same_ce _ (Hce12 (base_ref h))).  *) *)
(*    (*       rewrite (type_of_hexpr_cefind Hit1)//. *) *)
(*    (*       rewrite <-(typeof_same_ce _ (Hce12 (base_ref h))). done. *) *)
(*    (*       rewrite /=.  *) *)
(*    (*       move : (infer_type_no_unknown_type Hif) => Hfu. *) *)
(*    (*       rewrite /find_unknown. move : (Hfu (base_ref h) c ). *) *)
(*    (*       rewrite -(Hce12 (base_ref h)). *) *)
(*    (*       rewrite Hit1. case t; try done. *) *)
(*    (*       have Hit1' : CE.find (base_ref h) ce2 = Some (t, c) by rewrite -(Hce12 (base_ref h))//. *) *)
(*    (*       apply inferWidth_spcnct_tmp with (type_of_cmpnttyp t). *) *)
(*    (*       rewrite (type_of_hexpr_cefind Hit1')//. *) *)
(*    (*       rewrite /=(type_of_hexpr_cefind Hit1')/= Hde; case h0; done. *) *)
(*    (*       rewrite /= -(Hce12 (base_ref h))/= (type_of_hexpr_cefind Hit1') /= Hde; case h0; intros; move : Hde; *) *)
(*    (*         rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone) Haux Hit1 Hit1'; *) *)
(*    (*         case t; rewrite /=; intros; try (rewrite Hde//|| discriminate). *) *)
(*    (*       rewrite Hde//. *) *)
(*    (*     + (*invalid*) *) *)
(*    (*       intros. *) *)
(*    (*       apply inferWidth_sinvalid_sem_conform; try done. *) *)
(*    (*     + (*when*) *) *)
(*    (*       intros.  *) *)
(*    (*       apply inferWidth_swhen_sem_conform_tmp; try done. *) *)
(*    (*     + (*stop*) *) *)
(*    (*       intros. *) *)
(*    (*       apply inferWidth_sstop_sem_conform; try done. *) *)
(*    (*   - move : Hin => [Hin | Hin]. *) *)
(*    (*     rewrite -/(inferWidth_fun (st :: ss) ce2). *) *)
(*    (*     set wm1 := (inferWidth_wmap0 st ce2 empty_wmap0). *) *)
(*    (*     erewrite infer_stmt_lst; try done. *) *)
(*    (*     apply Hm with (inferType_stmt_fun st ce0) ce1 . *) *)
(*    (*     by apply inferType_hd_tl. *) *)
(*    (*     intros. symmetry. rewrite (Hce12 v) . apply wmap2_same. *) *)
(*    (*     apply new_v_wmap_none. by apply init_new_comp_name with st.  *) *)
(*    (*     rewrite -/(inferWidth_fun (st :: ss) ce2). *) *)
(*    (*     set wm1 := (inferWidth_wmap0 st ce2 empty_wmap0). *) *)
(*    (*     erewrite infer_stmt_lst; try done. *) *)
(*    (*     apply Hm with (inferType_stmt_fun st ce0) ce1 . *) *)
(*    (*     by apply inferType_hd_tl. *) *)
(*    (*     intros. *) *)
(*    (*     move : (not_init_cefind_some Hin v (wmap_map2_cenv (inferWidth_wmap0 st ce2 empty_wmap0) ce2) (CE.vtyp v ce1)) => Haux. *) *)
(*    (*     rewrite Haux. *) *)
(*    (*     exact : (not_init_cefind_some Hin v ce1 (CE.vtyp v ce1)). *) *)
(*    (* Qed. *) *)

(*   (** Pass InferWidth *) *)

(*   (* Infer unknown width *)
(*      Infers the smallest width that is larger than or equal to all assigned widths to a signal *)
(*    * Note that this means that dummy assignments that are overwritten by last-connect-semantics *)
(*    * can still influence width inference *) *)


(*    (* A map to store candidate types *) *)
(*    Definition wmap := CE.t (seq ftype). *)
(*    Definition empty_wmap : wmap := CE.empty (seq ftype). *)
(*    Definition finds (v:var) (w:wmap) := match CE.find v w with Some t => t | None => [::] end. *)

(*    Definition wmap0 := CE.t (ftype). *)
(*    Definition empty_wmap0 : wmap0 := CE.empty (ftype). *)
(*    Definition finds0 (v:var) (w:wmap0) := match CE.find v w with Some t => t | None => def_ftype end. *)

(*    Fixpoint get_field_name r : V.t := *)
(*      match r with *)
(*      | Eid v => v *)
(*      | Esubfield r v =>  v *)
(*      | Esubindex r n => get_field_name r *)
(*      | Esubaccess r n => get_field_name r *)
(*      end. *)

(*    (* store the larger width *) *)
(*    Fixpoint add_ref_wmap0 r t ce (w:wmap0) : wmap0 := *)
(*      match r with *)
(*      | Eid v => *)
(*        match CE.find v w with *)
(*        | Some t1 => CE.add v (max_width t t1) w *)
(*        | None => CE.add v t w *)
(*        end *)
(*      | Esubfield r f => *)
(*        let br := base_ref r in *)
(*        CE.add br (upd_name_ftype (base_type_of_ref r ce) (v2var f) t) w *)
(*      | Esubindex rs n => *)
(*        let br := base_ref rs in *)
(*        let vt := type_of_cmpnttyp (fst (CE.vtyp br ce)) in *)
(*        match vt with *)
(*        | Gtyp gt => w *)
(*        | Atyp ta na => CE.add br (upd_vectyp vt t) w *)
(*        | Btyp _ => CE.add br (upd_name_ftype vt (v2var (get_field_name rs)) t) w *)
(*        end *)
(*      | Esubaccess rs n => *)
(*        let br := base_ref rs in *)
(*        let vt := type_of_cmpnttyp (fst (CE.vtyp br ce)) in *)
(*        match vt with *)
(*        | Gtyp gt => w *)
(*        | Atyp ta na => CE.add br (upd_vectyp vt t) w *)
(*        | Btyp Fnil => w *)
(*        | Btyp (Fflips v _ tf fs) => *)
(*          CE.add br (upd_name_ftype vt (v2var (get_field_name rs)) t) w *)
(*        end *)
(*      end. *)


(*    (* Require Import FunInd. *) *)

(*    Fixpoint inferWidth_wmap0 (s : hfstmt) (ce : cenv) (w : wmap0): wmap0 := *)
(*      match s with *)
(*      | Snode v e => if is_deftyp (type_of_hfexpr e ce) *)
(*                       then add_ref_wmap0 (Eid v) (type_of_hfexpr e ce) ce w else w *)
(*      | Swire v t => if is_deftyp t then add_ref_wmap0 (Eid v) t ce w else w *)
(*      | Sreg v r => if is_deftyp (type r) then add_ref_wmap0 (Eid v) (type r) ce w else w *)
(*      (* | Sreg v (mk_freg t cl (Rst (Eref rs) e)) => *) *)
(*      (*   let w1 w := add_ref_wmap0 (Eid v) (type_of_hfexpr e ce) ce w in *) *)
(*      (*   let w2 w:= add_ref_wmap0 rs (Gtyp (Fuint 1)) ce w in  *) *)
(*      (*   if (is_deftyp t) && (is_deftyp (type_of_ref rs ce)) then (w2 (w1 w)) *) *)
(*      (*   else if (is_deftyp t) then (w1 w) *) *)
(*      (*        else if (is_deftyp (type_of_ref rs ce)) then (w2 w) else w *) *)
(*      | Sfcnct r1 (Eref r2) => *)
(*        let w1 w := add_ref_wmap0 r1 (type_of_ref r2 ce) ce w in *)
(*        let w2 w := add_ref_wmap0 r2 (type_of_ref r1 ce) ce w in *)
(*        if is_deftyp (type_of_ref r1 ce) (*&& (is_deftyp (type_of_ref r2 ce))*) then ((w1 w)) *)
(*        (*else if ~~ is_deftyp (type_of_ref r1 ce) then w1 w*) else w *)
(*      | Sfcnct r e => *)
(*        let w1 := add_ref_wmap0 r (type_of_hfexpr e ce) ce w in *)
(*        if is_deftyp (type_of_ref r ce) then w1 else w *)
(*      | Spcnct r1 (Eref r2) => *)
(*        let add1 wx := add_ref_wmap0 r1 (type_of_ref r2 ce) ce wx in *)
(*        let add2 wx := add_ref_wmap0 r2 (type_of_ref r2 ce) ce wx in *)
(*        if is_deftyp (type_of_ref r1 ce) (*&& (is_deftyp (type_of_ref r2 ce))*) then ((add1 w)) *)
(*        (*else if is_deftyp (type_of_ref r1 ce) then add1 w*) *)
(*             (*else if is_deftyp (type_of_ref r2 ce) then w2 w*) else w *)
(*      | Spcnct r e => *)
(*        let w1 := add_ref_wmap0 r (type_of_hfexpr e ce) ce w in *)
(*        if is_deftyp (type_of_ref r ce) then w1 else w *)
(*      (* | Swhen (Eref rs) s1 s2 => *) *)
(*      (*   let w1 w := add_ref_wmap0 rs (Gtyp (Fuint 1)) ce w in *) *)
(*      (*   let fix aux ss ce w := *) *)
(*      (*       match ss with *) *)
(*      (*       | nil => w *) *)
(*      (*       | s :: ss => aux ss ce (inferWidth_wmap0 s ce w) *) *)
(*      (*       end *) *)
(*      (*   in *) *)
(*      (*   if (is_deftyp (type_of_ref rs ce)) *) *)
(*      (*   then aux s2 ce (aux s1 ce (w1 w)) *) *)
(*      (*   else aux s2 ce (aux s1 ce w) *) *)
(*      | _ => w *)
(*      end *)
(*    . *)

(*    (* store a list of types, and compare width later *) *)
(*    (* Fixpoint add_ref_wmap r t ce w : wmap := *) *)
(*    (*   match r with *) *)
(*    (*   | Eid v => CE.add v (cons t (finds v w)) w *) *)
(*    (*   | Esubfield r f => *) *)
(*    (*     let br := base_ref r in *) *)
(*    (*     CE.add br (cons (upd_name_ftype (base_type_of_ref r ce) (v2var f) t) (finds br w)) w *) *)
(*    (*   | Esubindex rs n => *) *)
(*    (*     let br := base_ref rs in *) *)
(*    (*     let vt := type_of_cmpnttyp (fst (CE.vtyp br ce)) in *) *)
(*    (*     match vt with *) *)
(*    (*     | Gtyp gt => w *) *)
(*    (*     | Atyp ta na => CE.add br (cons (upd_vectyp vt t) (finds br w)) w *) *)
(*    (*     | Btyp _ => CE.add br (cons (upd_name_ftype vt (v2var (get_field_name rs)) t) (finds br w)) w *) *)
(*    (*     end *) *)
(*    (*   | Esubaccess rs n =>  *) *)
(*    (*     let br := base_ref rs in *) *)
(*    (*     let vt := type_of_cmpnttyp (fst (CE.vtyp br ce)) in *) *)
(*    (*     match vt with *) *)
(*    (*     | Gtyp gt => w *) *)
(*    (*     | Atyp ta na => CE.add br (cons (upd_vectyp vt t) (finds br w)) w *) *)
(*    (*     | Btyp Fnil => w *) *)
(*    (*     | Btyp (Fflips v _ tf fs) => *) *)
(*    (*       CE.add br (cons (upd_name_ftype vt (v2var (get_field_name rs)) t) (finds br w)) w *) *)
(*    (*     end *) *)
(*    (*   end. *) *)

(*    (* Fixpoint inferWidth_wmap (s : hfstmt) (ce : cenv) (w : wmap) : wmap := *) *)
(*    (*   match s with *) *)
(*    (*   | Snode v e => w *) *)
(*    (*   | Swire v t => if is_deftyp t then add_ref_wmap (Eid v) t ce w else w *) *)
(*    (*   | Sreg v (mk_freg t cl (Rst (Eref rs) e)) => *) *)
(*    (*     let w1 w := add_ref_wmap (Eid v) (type_of_hfexpr e ce) ce w in *) *)
(*    (*     let w2 w:= add_ref_wmap rs (Gtyp (Fuint 1)) ce w in  *) *)
(*    (*     if (is_deftyp t) && (is_deftyp (type_of_ref rs ce)) then (w2 (w1 w)) *) *)
(*    (*     else if (is_deftyp t) then (w1 w) *) *)
(*    (*          else if (is_deftyp (type_of_ref rs ce)) then (w2 w) else w *) *)
(*    (*   | Sfcnct r e => *) *)
(*    (*     let w1 := add_ref_wmap r (type_of_hfexpr e ce) ce w in *) *)
(*    (*     if is_deftyp (type_of_ref r ce) then w1 else w *) *)
(*    (*   | Spcnct r e =>  *) *)
(*    (*     let w1 := add_ref_wmap r (type_of_hfexpr e ce) ce w in *) *)
(*    (*     if is_deftyp (type_of_ref r ce) then w1 else w *) *)
(*    (*   | Swhen (Eref rs) s1 s2 => *) *)
(*    (*     let w1 w := add_ref_wmap rs (Gtyp (Fuint 1)) ce w in *) *)
(*    (*     if (is_deftyp (type_of_ref rs ce)) *) *)
(*    (*     then inferWidth_wmap s2 ce (inferWidth_wmap s1 ce (w1 w)) *) *)
(*    (*     else w *) *)
(*    (*   | _ => w  *) *)
(*    (*   end *) *)
(*    (* . *) *)

(*    (* Fixpoint inferWidth_stmts_wmap ss ce w: wmap := *) *)
(*    (*   match ss with *) *)
(*    (*   | nil => w *) *)
(*    (*   | s :: sts => inferWidth_stmts_wmap sts ce (inferWidth_wmap s ce w) *) *)
(*    (*   end. *) *)

(*    (* Definition max_width_of_wmap ts : ftype := *) *)
(*    (*   List.fold_left max_width ts (Gtyp (Fuint 0)). *) *)

(*    (* Definition map_max_width_wmap (w : wmap) : wmap0 := *) *)
(*    (*   CE.map max_width_of_wmap w . *) *)

(*    (* Lemma inferWidth_deftyp : *) *)
(*    (*   forall s ce w w', *) *)
(*    (*     inferWidth_wmap0 s ce w = w' -> *) *)
(*    (*     forall v, ~~ is_deftyp (finds0 v w). *) *)
(*    (* Proof. *) *)
(*    (* Admitted. *) *)

(*    Fixpoint inferWidth_stmts_wmap0 (ss : hfstmt_seq) ce w: wmap0 := *)
(*      match ss with *)
(*      | Qnil => w *)
(*      | Qcons s sts => inferWidth_stmts_wmap0 sts ce (inferWidth_wmap0 s ce w) *)
(*      end. *)

(*    Definition add_width_2_cenv (w : option ftype) (t : option (cmpnt_init_typs * fcomponent)) := *)
(*      match w, t with *)
(*      | Some w, Some (Aggr_typ ta, c) => if is_deftyp ta then Some (aggr_typ w, c) else t *)
(*      | Some w, Some (Reg_typ r, c) => *)
(*        if is_deftyp (type r) then Some (reg_typ (mk_freg (w) (clock r) (reset r)), c) else t *)
(*      | Some w, Some (Mem_typ m, c) => *)
(*        if is_deftyp (data_type m) then Some (mem_typ (mk_fmem w (depth m) (reader m) (writer m) (read_latency m) (write_latency m) (read_write m)), c) *)
(*        else t *)
(*      | _, t => t *)
(*      end. *)

(*    (* overwrite type widths in ce by wmap with the same index *) *)

(*    Definition wmap_map2_cenv w (ce:cenv) : cenv := *)
(*      CE.map2 add_width_2_cenv w ce. *)

(*    Definition inferWidth_fun ss ce : cenv := *)
(*      wmap_map2_cenv (inferWidth_stmts_wmap0 ss ce empty_wmap0) ce. *)

(*    (**** infer width semantics in pred **) *)

(*    Parameter new_v_wmap_none: *)
(*      forall v, *)
(*      new_comp_name v -> *)
(*      forall w: wmap0, CE.find v w = None. *)

(*    Inductive inferWidth_sstmt_sem : hfstmt -> wmap0 -> wmap0 -> cenv -> cenv -> Prop := *)
(*    | inferWidth_sskip wm1 wm2 ce1 ce2 : *)
(*        (forall v t c, *)
(*        CE.find v ce1 = Some (t, c) -> *)
(*        CE.find v wm1 = Some (type_of_cmpnttyp t) -> *)
(*        CE.find v wm1 = CE.find v wm2 /\ *)
(*        CE.find v ce1 = CE.find v ce2) -> *)
(*        inferWidth_sstmt_sem (sskip) wm1 wm2 ce1 ce2 *)
(*    (* | inferWidth_sstop wm1 wm2 ce1 ce2 ss1 ss2 n : *) *)
(*    (*     (forall v t c , *) *)
(*    (*     CE.find v ce1 = Some (t, c) -> *) *)
(*    (*     CE.find v wm1 = Some (type_of_cmpnttyp t) -> *) *)
(*    (*     CE.find v wm1 = CE.find v wm2 /\ *) *)
(*    (*     CE.find v ce1 = CE.find v ce2) -> *) *)
(*    (*     inferWidth_sstmt_sem (sstop ss1 ss2 n) wm1 wm2 ce1 ce2 *) *)
(*    | inferWidth_sinvalid wm1 wm2 ce1 ce2 : *)
(*        forall v, (forall t c, *)
(*          CE.find (base_ref v) ce1 = Some (t, c) -> *)
(*          CE.find (base_ref v) wm1 = Some (type_of_cmpnttyp t) -> *)
(*          CE.find (base_ref v) wm1 = CE.find (base_ref v) wm2 /\ *)
(*          CE.find (base_ref v) ce1 = CE.find (base_ref v) ce2) -> *)
(*          inferWidth_sstmt_sem (sinvalid v) wm1 wm2 ce1 ce2 *)
(*    | inferWidth_swhen wm1 wm2 ce1 ce2 c ss1 ss2: *)
(*        (forall v t c , *)
(*          CE.find (v) ce1 = Some (t, c) -> *)
(*          CE.find (v) wm1 = Some (type_of_cmpnttyp t) -> *)
(*          CE.find (v) wm1 = CE.find (v) wm2 /\ *)
(*          CE.find (v) ce1 = CE.find (v) ce2) -> *)
(*          inferWidth_sstmt_sem (swhen c ss1 ss2) wm1 wm2 ce1 ce2 *)
(*    | inferWidth_smem v m wm1 wm2 ce1 ce2 : *)
(*        (forall t , *)
(*            CE.find (v) ce1 = Some (t, Memory) -> *)
(*            (* CE.find v wm1 = None -> *) *)
(*            new_comp_name v -> *)
(*            CE.find v wm1 = CE.find v wm2 /\ *)
(*            CE.find v ce1 = CE.find v ce2) -> *)
(*        inferWidth_sstmt_sem (smem v m) wm1 wm2 ce1 ce2 *)
(*    | inferWidth_smem_repeatv v m wm1 ce1 : *)
(*        (forall t , *)
(*            CE.find v wm1 = Some t) -> *)
(*        inferWidth_sstmt_sem (smem v m) wm1 wm1 ce1 ce1 *)
(*    | inferWidth_sinst v m wm1 wm2 ce1 ce2 : *)
(*        (forall t c, *)
(*            CE.find (v) ce1 = Some (t, c) -> *)
(*            (* CE.find v wm1 = None -> *) *)
(*            new_comp_name v -> *)
(*            CE.find v wm1 = CE.find v wm2 /\ *)
(*            CE.find v ce1 = CE.find v ce2) -> *)
(*        inferWidth_sstmt_sem (sinst v m) wm1 wm2 ce1 ce2 *)
(*    | inferWidth_snode_exp v e ce0 ce1 (wm : wmap0) : *)
(*        CE.find (v) ce0 = Some (aggr_typ (type_of_hfexpr e ce0), Node) -> *)
(*        ~~ is_deftyp (type_of_hfexpr e ce0) -> *)
(*        (* CE.find v wm = None -> *) *)
(*        new_comp_name v -> *)
(*        CE.find v ce0 = CE.find v ce1 -> *)
(*        inferWidth_sstmt_sem (Snode v e) wm wm ce0 ce1 *)
(*    | inferWidth_snode_imp v e ce0 ce1 (wm0 wm1 : wmap0) : *)
(*        is_deftyp ((type_of_hfexpr e ce0)) -> *)
(*        CE.find (v) ce0 = Some (aggr_typ (type_of_hfexpr e ce0), Node) -> *)
(*        (* CE.find v wm0 = None -> *) *)
(*        new_comp_name v -> *)
(*        CE.find v wm1 = Some (type_of_hfexpr e ce0) -> *)
(*        CE.find v ce0 = CE.find v ce1 -> *)
(*        inferWidth_sstmt_sem (Snode v e) wm0 wm1 ce0 ce1 *)
(*    | inferWidth_swire_exp v t ce0 ce1 wm : *)
(*        ~~ is_deftyp (t) -> *)
(*        CE.find (v) ce0 = Some (aggr_typ t, Wire) -> *)
(*        (* CE.find v wm = None -> *) *)
(*        new_comp_name v -> *)
(*        CE.find v ce0 = CE.find v ce1 -> *)
(*        inferWidth_sstmt_sem (Swire v t) wm wm ce0 ce1 *)
(*    | inferWidth_swire_imp v t ce0 ce1 wm0 wm1 : *)
(*        is_deftyp t -> *)
(*        CE.find (v) ce0 = Some (aggr_typ t, Wire) -> *)
(*        (* CE.find v wm0 = None -> *) *)
(*        new_comp_name v -> *)
(*        CE.find v wm1 = Some t -> *)
(*        CE.find v ce0 = CE.find v ce1 -> *)
(*        inferWidth_sstmt_sem (Swire v t) wm0 wm1 ce0 ce1 *)
(*    | inferWidth_sreg_exp v r ce0 ce1 wm : *)
(*        ~~ is_deftyp (type r) -> *)
(*        CE.find (v) ce0 = Some (reg_typ r, Register) -> *)
(*        (* CE.find v wm = None -> *) *)
(*        new_comp_name v -> *)
(*        CE.find v ce0 = CE.find v ce1 -> *)
(*        inferWidth_sstmt_sem (Sreg v r) wm wm ce0 ce1 *)
(*    | inferWidth_sreg_imp v r ce0 ce1 wm0 wm1 : *)
(*        is_deftyp (type r) -> *)
(*        CE.find (v) ce0 = Some (reg_typ r, Register) -> *)
(*        (* CE.find v wm0 = None -> *) *)
(*        new_comp_name v -> *)
(*        CE.find v wm1 = Some (type r) -> *)
(*        CE.find v ce0 = CE.find v ce1 -> *)
(*        inferWidth_sstmt_sem (Sreg v r) wm0 wm1 ce0 ce1 *)
(*    | inferWidth_sfcnct_gtyp_gt v e c t0 t1 t2 ce0 ce1 wm0 wm1 : *)
(*        CE.find v wm0 = Some (Gtyp t1) -> *)
(*        CE.find v wm1 = Some (Gtyp t2) -> *)
(*        type_of_hfexpr e ce0 = Gtyp t2 -> *)
(*        CE.find v ce0 = Some (aggr_typ (Gtyp t0), c) -> *)
(*        is_deftyp (Gtyp t0) -> *)
(*        CE.find v ce1 = Some (aggr_typ (Gtyp t2), c) -> *)
(*        sizeof_fgtyp t1 < sizeof_fgtyp t2 -> *)
(*        inferWidth_sstmt_sem (Sfcnct ((eid v)) e) wm0 wm1 ce0 ce1 *)
(*    | inferWidth_sfcnct_gtyp_le v e c t0 t1 t2 ce0 ce1 wm0 wm1 : *)
(*        CE.find v wm0 = Some (Gtyp t1) -> *)
(*        CE.find v wm1 = Some (Gtyp t1) -> *)
(*        type_of_hfexpr e ce0 = Gtyp t2 -> *)
(*        CE.find v ce0 = Some (aggr_typ (Gtyp t0), c) -> *)
(*        is_deftyp (Gtyp t0)-> *)
(*        CE.find v ce1 = Some (aggr_typ (Gtyp t1), c) -> *)
(*        sizeof_fgtyp t2 <= sizeof_fgtyp t1 -> *)
(*        inferWidth_sstmt_sem (Sfcnct ((eid v)) e) wm0 wm1 ce0 ce1 *)
(*    | inferWidth_sfcnct_ftype_gt r e t0 t1 t3 c ce0 ce1 wm0 wm1 : *)
(*        CE.find (base_ref r) wm0 = Some t1 -> *)
(*        CE.find (base_ref r) wm1 = Some (type_of_cmpnttyp t3) -> *)
(*        type_of_hfexpr e ce0 = type_of_cmpnttyp t3 -> *)
(*        CE.vtyp (base_ref r) ce0 = (t0, c) -> *)
(*        is_deftyp (type_of_cmpnttyp t0) -> *)
(*        CE.vtyp (base_ref r) ce1 = (t3, c) -> *)
(*        ~~ typeConstraintsGe t1 (type_of_cmpnttyp t3) -> *)
(*        inferWidth_sstmt_sem (Sfcnct r e) wm0 wm1 ce0 ce1 *)
(*    | inferWidth_sfcnct_ftype_le r e t0 t1 t3 c ce0 ce1 wm0 wm1 : *)
(*        CE.find (base_ref r) wm0 = Some (type_of_cmpnttyp t1) -> *)
(*        CE.find (base_ref r) wm1 = Some (type_of_cmpnttyp t1) -> *)
(*        type_of_hfexpr e ce0 = t3 -> *)
(*        CE.vtyp (base_ref r) ce0 = (t0, c) -> *)
(*        is_deftyp (type_of_cmpnttyp t0) -> *)
(*        CE.vtyp (base_ref r) ce1 = (t1, c) -> *)
(*        typeConstraintsGe (type_of_cmpnttyp t1) (t3) -> *)
(*        inferWidth_sstmt_sem (Sfcnct r e) wm0 wm1 ce0 ce1 *)
(*    | inferWidth_spcnct_ftype_gt r e t0 t1 t3 c ce0 ce1 wm0 wm1 : *)
(*        CE.find (base_ref r) wm0 = Some t1 -> *)
(*        CE.find (base_ref r) wm1 = Some (type_of_cmpnttyp t3) -> *)
(*        type_of_hfexpr e ce0 = type_of_cmpnttyp t3 -> *)
(*        CE.vtyp (base_ref r) ce0 = (t0, c) -> *)
(*        is_deftyp (type_of_cmpnttyp t0) -> *)
(*        CE.vtyp (base_ref r) ce1 = (t3, c) -> *)
(*        ~~ typeConstraintsGe t1 (type_of_cmpnttyp t3) -> *)
(*        inferWidth_sstmt_sem (Spcnct r e) wm0 wm1 ce0 ce1 *)
(*    | inferWidth_spcnct_ftype_le r e t0 t1 t3 c ce0 ce1 wm0 wm1 : *)
(*        CE.find (base_ref r) wm0 = Some (type_of_cmpnttyp t1) -> *)
(*        CE.find (base_ref r) wm1 = Some (type_of_cmpnttyp t1) -> *)
(*        type_of_hfexpr e ce0 = t3 -> *)
(*        CE.vtyp (base_ref r) ce0 = (t0, c) -> *)
(*        is_deftyp (type_of_cmpnttyp t0) -> *)
(*        CE.vtyp (base_ref r) ce1 = (t1, c) -> *)
(*        typeConstraintsGe (type_of_cmpnttyp t1) (t3) -> *)
(*        inferWidth_sstmt_sem (Spcnct r e) wm0 wm1 ce0 ce1 *)
(*    | inferWidth_sfcnct_tmp r e t0 wm0 wm1 ce0 ce1 : *)
(*        type_of_ref r ce0 = t0 -> *)
(*        CE.find (base_ref r) wm0 = CE.find (base_ref r) wm1 -> *)
(*        CE.find (base_ref r) ce0 = CE.find (base_ref r) ce1 -> *)
(*        ~~ is_deftyp t0 -> *)
(*        inferWidth_sstmt_sem (Sfcnct r e) wm0 wm1 ce0 ce1 *)
(*    | inferWidth_spcnct_tmp r e t0 wm0 wm1 ce0 ce1 : *)
(*        type_of_ref r ce0 = t0 -> *)
(*        CE.find (base_ref r) wm0 = CE.find (base_ref r) wm1 -> *)
(*        CE.find (base_ref r) ce0 = CE.find (base_ref r) ce1 -> *)
(*        ~~ is_deftyp t0 -> *)
(*        inferWidth_sstmt_sem (Spcnct r e) wm0 wm1 ce0 ce1 *)
(*    . *)

(*    Lemma inferWidth_snode_sem_conform : *)
(*      forall v e wm0 ce0 wm1 ce1 ce2, *)
(*        inferType_stmt (Snode v e) ce0 ce1 -> *)
(*        (* CE.find v wm0 = None -> *) *)
(*        new_comp_name v -> *)
(*        wm1 = inferWidth_wmap0 (Snode v e) ce1 wm0 -> *)
(*        ce2 = wmap_map2_cenv wm1 ce1 -> *)
(*        inferWidth_sstmt_sem (Snode v e) wm0 wm1 ce1 ce2. *)
(*    Proof. *)
(*      intros. rewrite H2/= H1. *)
(*      move : H1. *)
(*      move : (new_v_wmap_none H0 wm0) => Hn. *)
(*      rewrite /= Hn => Heqw01. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      move : (CELemmas.map2_1bis wm1 ce1 v Hnone). *)
(*      rewrite Heqw01 /=. *)
(*      move : Heqw01; case Hdf : (is_deftyp (type_of_hfexpr e ce1)). *)
(*      - move => Hwm1. *)
(*        move : (CELemmas.add_eq_o wm0 (type_of_hfexpr e ce1) (eq_refl v)) => Hwm01. *)
(*        rewrite Hwm01 -Hwm1 -/(wmap_map2_cenv wm1 ce1) -H2. *)
(*        inversion H. *)
(*        move => Ht01. *)
(*        apply inferWidth_snode_imp; try done. *)
(*        rewrite -H5//. *)
(*        rewrite Hwm1 (CELemmas.add_eq_o _ _ (eq_refl v))//. *)
(*        rewrite Ht01 H8 /add_width_2_cenv/= H5 Hdf//. *)
(*      - move => Hwm01. *)
(*        rewrite Hn -/(wmap_map2_cenv wm0 ce1) -Hwm01 -H2/= => Hce01. *)
(*        apply inferWidth_snode_exp; [ | rewrite(negbT Hdf)//|done | done ]. *)
(*        rewrite -Hce01 H2 /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*        rewrite Hwm01 Hn/=. *)
(*        inversion H. rewrite -H5 //. *)
(*    Qed. *)

(*    Lemma inferWidth_snode_sem_conform' : *)
(*      forall v e wm0 wm1 ce1 ce2, *)
(*        CE.find v ce1 = Some (aggr_typ (type_of_hfexpr e ce1), Node) -> *)
(*        wm1 = inferWidth_wmap0 (Snode v e) ce1 wm0 -> *)
(*        ce2 = wmap_map2_cenv wm1 ce1 -> *)
(*        inferWidth_sstmt_sem (Snode v e) wm0 wm1 ce1 ce2. *)
(*    Proof. *)
(*      intros. *)
(*      have Hin : (is_init (Snode v e)) by done. *)
(*      move : (init_new_comp_name Hin v) => Hnv. *)
(*      move : (new_v_wmap_none Hnv wm0) => Hn. *)
(*      rewrite H1/= H0. *)
(*      move : H0. *)
(*      rewrite /= Hn => Heqw01. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      move : (CELemmas.map2_1bis wm1 ce1 v Hnone). *)
(*      rewrite Heqw01 /=. *)
(*      move : Heqw01; case Hdf : (is_deftyp (type_of_hfexpr e ce1)). *)
(*      - move => Hwm1. *)
(*        move : (CELemmas.add_eq_o wm0 (type_of_hfexpr e ce1) (eq_refl v)) => Hwm01. *)
(*        rewrite Hwm01 -Hwm1 -/(wmap_map2_cenv wm1 ce1) -H1. *)
(*        move => Ht01. *)
(*        apply inferWidth_snode_imp; try done. *)
(*        rewrite Hwm1 //. *)
(*        rewrite Ht01 H /add_width_2_cenv/= Hdf//. *)
(*      - move => Hwm01. *)
(*        rewrite Hn -/(wmap_map2_cenv wm0 ce1) -Hwm01 -H1/= => Hce01. *)
(*        apply inferWidth_snode_exp; [done | rewrite(negbT Hdf)//|done | done ]. *)
(*    Qed. *)

(*    Lemma inferWidth_swire_exp_sem_conform : *)
(*      forall v t wm1 ce1 wm2 ce2 ce3, *)
(*        ~~ is_deftyp t -> *)
(*        inferType_stmt (Swire v t) ce1 ce2 -> *)
(*        (* CE.find v wm0 = None -> *) *)
(*        new_comp_name v -> *)
(*        wm2 = inferWidth_wmap0 (Swire v t) ce1 wm1 -> *)
(*        ce3 = wmap_map2_cenv wm2 ce2 -> *)
(*        inferWidth_sstmt_sem (Swire v t) wm1 wm2 ce2 ce3. *)
(*    Proof. *)
(*      intros. rewrite H2/=. *)
(*      move : (new_v_wmap_none H1 wm1) => Hn. *)
(*      move : H2. rewrite /= (negbTE H) => Heqw12. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      move : (CELemmas.map2_1bis wm1 ce2 v Hnone). *)
(*      rewrite Hn /=. rewrite -/(wmap_map2_cenv wm1 ce2) -Heqw12 -H3. *)
(*      move => Hfeq. symmetry in Hfeq. *)
(*      apply inferWidth_swire_exp; [ done | | done |done]. *)
(*      inversion H0; subst. done. *)
(*    Qed. *)


(*    Lemma inferWidth_swire_exp_sem_conform' : *)
(*      forall v t wm1 wm2 ce2 ce3, *)
(*        ~~ is_deftyp t -> *)
(*        CE.find v ce2 = Some (aggr_typ t, Wire) -> *)
(*        wm2 = inferWidth_wmap0 (Swire v t) ce2 wm1 -> *)
(*        ce3 = wmap_map2_cenv wm2 ce2 -> *)
(*        inferWidth_sstmt_sem (Swire v t) wm1 wm2 ce2 ce3. *)
(*    Proof. *)
(*      intros. *)
(*      rewrite H2/=. *)
(*      have Hin : (is_init (Swire v t)) by done. *)
(*      move : (init_new_comp_name Hin v) => Hnv. *)
(*      move : (new_v_wmap_none Hnv wm1) => Hn. *)
(*      move : H1. rewrite /= (negbTE H) => Heqw12. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      move : (CELemmas.map2_1bis wm1 ce2 v Hnone). *)
(*      rewrite Hn /=. rewrite -/(wmap_map2_cenv wm1 ce2) -Heqw12 -H2. *)
(*      move => Hfeq. symmetry in Hfeq. *)
(*      apply inferWidth_swire_exp; [ done | | done |done]. *)
(*      inversion H0; subst. done. *)
(*    Qed. *)

(*    Lemma inferWidth_swire_imp_sem_conform : *)
(*      forall v t wm1 ce1 wm2 ce2 ce3, *)
(*        is_deftyp t -> *)
(*        inferType_stmt (Swire v t) ce1 ce2 -> *)
(*        (* CE.find v wm0 = None -> *) *)
(*        new_comp_name v -> *)
(*        wm2 = inferWidth_wmap0 (Swire v t) ce1 wm1 -> *)
(*        ce3 = wmap_map2_cenv wm2 ce2 -> *)
(*        inferWidth_sstmt_sem (Swire v t) wm1 wm2 ce2 ce3. *)
(*    Proof. *)
(*      intros. *)
(*      move : (new_v_wmap_none H1 wm1) => Hn. *)
(*      rewrite H2 /= H Hn. *)
(*      move : H2. rewrite /= H Hn => Hw2. *)
(*      inversion H0; subst. *)
(*      apply inferWidth_swire_imp; [done| done|done | |]. *)
(*      - exact : (CELemmas.add_eq_o _ _ (eq_refl v)). *)
(*      - *)
(*        rewrite /wmap_map2_cenv. *)
(*        have Hnone : (add_width_2_cenv None None = None) by done. *)
(*        rewrite (CELemmas.map2_1bis _ _ _ Hnone) . *)
(*        rewrite (CELemmas.add_eq_o _ _ (eq_refl v)) H8. *)
(*        inversion H0; subst. rewrite /add_width_2_cenv/=. *)
(*        case (is_deftyp t); done. *)
(*    Qed. *)

(*    Lemma inferWidth_swire_imp_sem_conform' : *)
(*      forall v t wm1 wm2 ce2 ce3, *)
(*        is_deftyp t -> *)
(*        CE.find v ce2 = Some (aggr_typ t, Wire) -> *)
(*        wm2 = inferWidth_wmap0 (Swire v t) ce2 wm1 -> *)
(*        ce3 = wmap_map2_cenv wm2 ce2 -> *)
(*        inferWidth_sstmt_sem (Swire v t) wm1 wm2 ce2 ce3. *)
(*    Proof. *)
(*      intros. *)
(*      have Hin : (is_init (Swire v t)) by done. *)
(*      move : (init_new_comp_name Hin v) => Hnv. *)
(*      move : (new_v_wmap_none Hnv wm1) => Hn. *)
(*      rewrite H1 /= H Hn. *)
(*      move : H1. rewrite /= H Hn => Hw2. *)
(*      apply inferWidth_swire_imp; [done| done|done | |]. *)
(*      - exact : (CELemmas.add_eq_o _ _ (eq_refl v)). *)
(*      - *)
(*        rewrite H2 /wmap_map2_cenv. *)
(*        have Hnone : (add_width_2_cenv None None = None) by done. *)
(*        rewrite (CELemmas.map2_1bis _ _ _ Hnone) . *)
(*        rewrite Hw2 (CELemmas.add_eq_o _ _ (eq_refl v)) H0. *)
(*        rewrite /add_width_2_cenv/=. *)
(*        case (is_deftyp t); try done. *)
(*    Qed. *)

(*    Lemma inferWidth_swire_sem_conform : *)
(*      forall v t wm1 ce1 wm2 ce2 ce3, *)
(*        inferType_stmt (Swire v t) ce1 ce2 -> *)
(*        (* CE.find v wm0 = None -> *) *)
(*        new_comp_name v -> *)
(*        wm2 = inferWidth_wmap0 (Swire v t) ce1 wm1 -> *)
(*        ce3 = wmap_map2_cenv wm2 ce2 -> *)
(*        inferWidth_sstmt_sem (Swire v t) wm1 wm2 ce2 ce3. *)
(*    Proof. *)
(*      intros. *)
(*      case Hdf : (is_deftyp t). *)
(*      apply inferWidth_swire_imp_sem_conform with ce1; try done. *)
(*      apply inferWidth_swire_exp_sem_conform with ce1; try done. *)
(*      rewrite Hdf//. *)
(*    Qed. *)

(*    Lemma inferWidth_swire_sem_conform' : *)
(*      forall v t wm1 wm2 ce2 ce3, *)
(*        CE.find v ce2 = Some (aggr_typ t, Wire) -> *)
(*        wm2 = inferWidth_wmap0 (Swire v t) ce2 wm1 -> *)
(*        ce3 = wmap_map2_cenv wm2 ce2 -> *)
(*        inferWidth_sstmt_sem (Swire v t) wm1 wm2 ce2 ce3. *)
(*    Proof. *)
(*      intros. *)
(*      case Hdf : (is_deftyp t). *)
(*      apply inferWidth_swire_imp_sem_conform' ; try done. *)
(*      apply inferWidth_swire_exp_sem_conform' ; try done. *)
(*      rewrite Hdf//. *)
(*    Qed. *)

(*    Lemma inferWidth_sreg_exp_sem_conform : *)
(*      forall v r wm1 ce1 wm2 ce2 ce3, *)
(*        ~~ is_deftyp (type r) -> *)
(*        inferType_stmt (Sreg v r) ce1 ce2 -> *)
(*        (* CE.find v wm0 = None -> *) *)
(*        new_comp_name v -> *)
(*        wm2 = inferWidth_wmap0 (Sreg v r) ce1 wm1 -> *)
(*        ce3 = wmap_map2_cenv wm2 ce2 -> *)
(*        inferWidth_sstmt_sem (Sreg v r) wm1 wm2 ce2 ce3. *)
(*    Proof. *)
(*      intros. rewrite H2. *)
(*      move : H2. *)
(*      move : (new_v_wmap_none H1 wm1) => Hn. *)
(*      rewrite/= Hn (negbTE H) => Heqw12. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      move : (CELemmas.map2_1bis wm1 ce2 v Hnone). *)
(*      rewrite Hn /=. rewrite -/(wmap_map2_cenv wm1 ce2) -Heqw12 -H3. *)
(*      move => Hfeq. symmetry in Hfeq. *)
(*      apply inferWidth_sreg_exp; [ done | | done |done]. *)
(*      inversion H0; subst. *)
(*      done. *)
(*    Qed. *)

(*    Lemma inferWidth_sreg_exp_sem_conform' : *)
(*      forall v r wm1 wm2 ce2 ce3, *)
(*        ~~ is_deftyp (type r) -> *)
(*        CE.find v ce2 = Some (reg_typ r, Register) -> *)
(*        wm2 = inferWidth_wmap0 (Sreg v r) ce2 wm1 -> *)
(*        ce3 = wmap_map2_cenv wm2 ce2 -> *)
(*        inferWidth_sstmt_sem (Sreg v r) wm1 wm2 ce2 ce3. *)
(*    Proof. *)
(*      intros. rewrite H1. *)
(*      move : H1. *)
(*      have Hin : (is_init (Sreg v r)) by done. *)
(*      move : (init_new_comp_name Hin v) => Hnv. *)
(*      move : (new_v_wmap_none Hnv wm1) => Hn. *)
(*      rewrite/= Hn (negbTE H) => Heqw12. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      move : (CELemmas.map2_1bis wm1 ce2 v Hnone). *)
(*      rewrite Hn /=. rewrite -/(wmap_map2_cenv wm1 ce2) -Heqw12 -H2. *)
(*      move => Hfeq. symmetry in Hfeq. *)
(*      apply inferWidth_sreg_exp; done. *)
(*    Qed. *)

(*    Lemma inferWidth_sreg_imp_sem_conform : *)
(*      forall v r wm1 ce1 wm2 ce2 ce3, *)
(*        is_deftyp (type r) -> *)
(*        inferType_stmt (Sreg v r) ce1 ce2 -> *)
(*        (* CE.find v wm1 = None -> *) *)
(*        new_comp_name v -> *)
(*        wm2 = inferWidth_wmap0 (Sreg v r) ce1 wm1 -> *)
(*        ce3 = wmap_map2_cenv wm2 ce2 -> *)
(*        inferWidth_sstmt_sem (Sreg v r) wm1 wm2 ce2 ce3. *)
(*    Proof. *)
(*      intros. *)
(*      move : (new_v_wmap_none H1 wm1) => Hn. *)
(*      rewrite H2 /= H Hn. *)
(*      move : H2. rewrite /= H Hn => Hw2. *)
(*      inversion H0; subst. *)
(*      apply inferWidth_sreg_imp; [ done| done| done| |]. *)
(*      - exact : (CELemmas.add_eq_o _ _ (eq_refl v)). *)
(*      - rewrite  /wmap_map2_cenv. *)
(*        have Hnone : (add_width_2_cenv None None = None) by done. *)
(*        rewrite (CELemmas.map2_1bis _ _ _ Hnone) . *)
(*        rewrite (CELemmas.add_eq_o _ _ (eq_refl v)) H8. *)
(*        rewrite /add_width_2_cenv/=. *)
(*        case (is_deftyp (type r)). case r; done. *)
(*        done. *)
(*    Qed. *)

(*    Lemma inferWidth_sreg_imp_sem_conform' : *)
(*      forall v r wm1 wm2 ce2 ce3, *)
(*        is_deftyp (type r) -> *)
(*        CE.find v ce2 = Some (reg_typ r, Register) -> *)
(*        wm2 = inferWidth_wmap0 (Sreg v r) ce2 wm1 -> *)
(*        ce3 = wmap_map2_cenv wm2 ce2 -> *)
(*        inferWidth_sstmt_sem (Sreg v r) wm1 wm2 ce2 ce3. *)
(*    Proof. *)
(*      intros. *)
(*      have Hin : (is_init (Sreg v r)) by done. *)
(*      move : (init_new_comp_name Hin v) => Hnv. *)
(*      move : (new_v_wmap_none Hnv wm1) => Hn. *)
(*      rewrite H1 /= H Hn. *)
(*      move : H1. rewrite /= H Hn => Hw2. *)
(*      apply inferWidth_sreg_imp; [ done| done| done| |]. *)
(*      - exact : (CELemmas.add_eq_o _ _ (eq_refl v)). *)
(*      - rewrite H2 /wmap_map2_cenv. *)
(*        have Hnone : (add_width_2_cenv None None = None) by done. *)
(*        rewrite (CELemmas.map2_1bis _ _ _ Hnone) . *)
(*        rewrite Hw2 (CELemmas.add_eq_o _ _ (eq_refl v)) H0. *)
(*        rewrite /add_width_2_cenv/=. *)
(*        case (is_deftyp (type r)); try done. *)
(*        case r; done. *)
(*    Qed. *)

(*    Lemma inferWidth_sreg_sem_conform : *)
(*      forall v t wm1 ce1 wm2 ce2 ce3, *)
(*        inferType_stmt (Sreg v t) ce1 ce2 -> *)
(*        (* CE.find v wm1 = None -> *) *)
(*        new_comp_name v -> *)
(*        wm2 = inferWidth_wmap0 (Sreg v t) ce1 wm1 -> *)
(*        ce3 = wmap_map2_cenv wm2 ce2 -> *)
(*        inferWidth_sstmt_sem (Sreg v t) wm1 wm2 ce2 ce3. *)
(*    Proof. *)
(*      intros. *)
(*      case Hdf : (is_deftyp (type t)). *)
(*      apply inferWidth_sreg_imp_sem_conform with ce1; try done. *)
(*      apply inferWidth_sreg_exp_sem_conform with ce1; try done. *)
(*      rewrite Hdf//. *)
(*    Qed. *)

(*    Lemma inferWidth_sreg_sem_conform' : *)
(*      forall v t wm1 wm2 ce2 ce3, *)
(*        CE.find v ce2 = Some (reg_typ t, Register) -> *)
(*        wm2 = inferWidth_wmap0 (Sreg v t) ce2 wm1 -> *)
(*        ce3 = wmap_map2_cenv wm2 ce2 -> *)
(*        inferWidth_sstmt_sem (Sreg v t) wm1 wm2 ce2 ce3. *)
(*    Proof. *)
(*      intros. *)
(*      case Hdf : (is_deftyp (type t)). *)
(*      apply inferWidth_sreg_imp_sem_conform'; try done. *)
(*      apply inferWidth_sreg_exp_sem_conform'; try done. *)
(*      rewrite Hdf//. *)
(*    Qed. *)

(*    Lemma inferWidth_smem_sem_conform : *)
(*      forall v m wm1 ce1 wm2 ce2 ce3, *)
(*        inferType_stmt (Smem v m) ce1 ce2 -> *)
(*        (* CE.find v wm1 = None -> *) *)
(*        new_comp_name v -> *)
(*        wm2 = inferWidth_wmap0 (Smem v m) ce1 wm1 -> *)
(*        ce3 = wmap_map2_cenv wm2 ce2 -> *)
(*        inferWidth_sstmt_sem (Smem v m) wm1 wm2 ce2 ce3. *)
(*    Proof. *)
(*      intros. *)
(*      rewrite H2 H1/=. *)
(*      apply inferWidth_smem; try done. *)
(*      intros. *)
(*      rewrite /wmap_map2_cenv. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      rewrite (CELemmas.map2_1bis _ _ _ Hnone) (new_v_wmap_none H0 wm1)/=. *)
(*      done. *)
(*    Qed. *)

(*    Lemma inferWidth_smem_sem_conform' : *)
(*      forall v m wm1 wm2 ce2 ce3, *)
(*        CE.find v ce2 = Some (mem_typ m, Memory) -> *)
(*        wm2 = inferWidth_wmap0 (Smem v m) ce2 wm1 -> *)
(*        ce3 = wmap_map2_cenv wm2 ce2 -> *)
(*        inferWidth_sstmt_sem (Smem v m) wm1 wm2 ce2 ce3. *)
(*    Proof. *)
(*      intros. *)
(*      have Hin : (is_init (Smem v m)) by done. *)
(*      move : (init_new_comp_name Hin v) => Hnv. *)
(*      move : (new_v_wmap_none Hnv wm1) => Hn. *)
(*      rewrite H1 H0/=. *)
(*      apply inferWidth_smem; try done. *)
(*      intros. *)
(*      rewrite /wmap_map2_cenv. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      rewrite (CELemmas.map2_1bis _ _ _ Hnone) Hn/=//. *)
(*    Qed. *)

(*    Lemma inferWidth_sinst_sem_conform : *)
(*      forall v m wm1 ce1 wm2 ce2 ce3, *)
(*        inferType_stmt (Sinst v m) ce1 ce2 -> *)
(*        (* CE.find v wm1 = None -> *) *)
(*        new_comp_name v -> *)
(*        wm2 = inferWidth_wmap0 (Sinst v m) ce1 wm1 -> *)
(*        ce3 = wmap_map2_cenv wm2 ce2 -> *)
(*        inferWidth_sstmt_sem (Sinst v m) wm1 wm2 ce2 ce3. *)
(*    Proof. *)
(*      intros. *)
(*      rewrite H2 H1/=. *)
(*      apply inferWidth_sinst; try done. *)
(*      intros. *)
(*      rewrite /wmap_map2_cenv. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      rewrite (CELemmas.map2_1bis _ _ _ Hnone) (new_v_wmap_none H0 wm1)/=. *)
(*      done. *)
(*    Qed. *)

(*    Lemma inferWidth_sinst_sem_conform' : *)
(*      forall v t m wm1 wm2 ce2 ce3, *)
(*        CE.find v ce2 = Some (t, Instanceof) -> *)
(*        wm2 = inferWidth_wmap0 (Sinst v m) ce2 wm1 -> *)
(*        ce3 = wmap_map2_cenv wm2 ce2 -> *)
(*        inferWidth_sstmt_sem (Sinst v m) wm1 wm2 ce2 ce3. *)
(*    Proof. *)
(*      intros. *)
(*      have Hin : (is_init (Sinst v m)) by done. *)
(*      move : (init_new_comp_name Hin v) => Hnv. *)
(*      move : (new_v_wmap_none Hnv wm1) => Hn. *)
(*      rewrite H1 H0/=. *)
(*      apply inferWidth_sinst; try done. *)
(*      intros. *)
(*      rewrite /wmap_map2_cenv. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      rewrite (CELemmas.map2_1bis _ _ _ Hnone)/= Hn//. *)
(*    Qed. *)

(*    Lemma sizeof_fgtyp_lt_max_width t1 t2 : *)
(*      ftype_equiv (Gtyp t1) (Gtyp t2) -> *)
(*      sizeof_fgtyp t1 <= sizeof_fgtyp t2 -> *)
(*      max_width (Gtyp t1) (Gtyp t2) = Gtyp t2. *)
(*    Proof. *)
(*      elim t1; elim t2; rewrite /=; intros; *)
(*        try (rewrite (maxn_idPr H0)//|| discriminate|| done). *)
(*    Qed. *)

(*    Lemma typeConstraints_max_width t1 t2 : *)
(*      ftype_equiv t1 t2 -> *)
(*      typeConstraintsGe t1 t2 -> *)
(*      max_width t1 t2 = t1. *)
(*    Proof. *)
(*      elim t1; elim t2; rewrite /=; intros; try discriminate. *)
(*      - move : H H0. rewrite/typeConstraintsGe/=. *)
(*        elim f ; elim f0; try (intros; rewrite (maxn_idPr H0)//||discriminate||done). *)
(*    Admitted. *)

(*    Lemma typeConstraints_weak_max_width t1 t2 : *)
(*      ftype_weak_equiv t1 t2 -> *)
(*      typeConstraintsGe t1 t2 -> *)
(*      max_width t1 t2 = t1. *)
(*    Proof. *)
(*    Admitted. *)

(*    Lemma max_width_typeConstraints t1 t2 : *)
(*      ftype_equiv t1 t2 -> *)
(*      max_width t1 t2 = t1 -> *)
(*      typeConstraintsGe t1 t2. *)
(*    Proof. Admitted. *)

(*    Lemma max_width_weak_typeConstraints t1 t2 : *)
(*      ftype_weak_equiv t1 t2 -> *)
(*      max_width t1 t2 = t1 -> *)
(*      typeConstraintsGe t1 t2. *)
(*    Proof. Admitted. *)

(*    Lemma neg_typeConstraints_max_width t1 t2 : *)
(*      ftype_equiv t1 t2 -> *)
(*      ~~ (typeConstraintsGe t1 t2) -> *)
(*      max_width t1 t2 = t2. *)
(*    Proof. *)
(*    Admitted. *)

(*    Lemma neg_typeConstraints_weak_max_width t1 t2 : *)
(*      ftype_weak_equiv t1 t2 -> *)
(*      ~~ (typeConstraintsGe t1 t2) -> *)
(*      max_width t1 t2 = t2. *)
(*    Proof. Admitted. *)

(*    Lemma ftype_equiv_symmetry t1 t2 : *)
(*      ftype_equiv (t1) (t2) -> ftype_equiv (t2) (t1) *)
(*    with ffield_equiv_symmetry f1 f2 : *)
(*           fbtyp_equiv f1 f2 -> fbtyp_equiv f2 f1. *)
(*    Proof. *)
(*      elim: t1 t2 => [f1| f1 H1 n1| n1 ]  [f2| f2 n2| n2 ]//. *)
(*      - elim: f1 f2; try done. *)
(*      - rewrite /= => /andP [Heq Hfeq]. rewrite (eqP Heq)/= eq_refl andTb. *)
(*          by apply H1. *)
(*      - rewrite /=. apply ffield_equiv_symmetry. *)
(*      elim: f1 f2 => [|v1 flp1 f1 fs1 IH1 ] [|v2 flp2 f2 fs2 ] . *)
(*      - done. *)
(*      - rewrite /=//. *)
(*      - rewrite /=; case flp1; done. *)
(*      - elim: flp1 flp2 => [|] [|] /=//. *)
(*        + move => /andP [/andP [Heq Heqf] Heqb]. *)
(*          rewrite (eqP Heq) eq_refl andTb. *)
(*          apply /andP. split. *)
(*          by apply ftype_equiv_symmetry. *)
(*          exact : (IH1 fs2 Heqb). *)
(*        + move => /andP [/andP [Heq Heqf] Heqb]. *)
(*          rewrite (eqP Heq) eq_refl andTb. *)
(*          apply /andP. split. *)
(*          by apply ftype_equiv_symmetry. *)
(*          exact : (IH1 fs2 Heqb). *)
(*    Qed. *)

(*    Lemma ftype_weak_equiv_symmetry t1 t2 : *)
(*      ftype_weak_equiv (t1) (t2) -> ftype_weak_equiv (t2) (t1) *)
(*    with ffield_weak_equiv_symmetry f1 f2 : *)
(*           fbtyp_weak_equiv f1 f2 -> fbtyp_weak_equiv f2 f1. *)
(*    Proof. Admitted. *)

(*    Lemma max_width_symmetry t1 t2 : *)
(*      max_width (t1) (t2) = max_width (t2) (t1). *)
(*    Proof. *)
(*    Admitted. *)

(*    Lemma add_ref_wmap0_max_width r t1 t2 ce wm : *)
(*      CE.find (base_ref r) wm = Some t1 -> *)
(*      CE.find (base_ref r) (add_ref_wmap0 r t2 ce wm) = Some (max_width t1 t2). *)
(*    Proof. Admitted. *)

(*    Lemma inferWidth_sfcnct_ftype_sem_conform : *)
(*      forall r e c1 t0 t1 t2 wm1 ce1 wm2 ce2 , *)
(*        ftype_equiv t1 t2 -> *)
(*        CE.find (base_ref r) ce1 =  Some (t0, c1) -> *)
(*        type_of_ref r ce1 = type_of_cmpnttyp t0 -> *)
(*        is_deftyp (type_of_cmpnttyp t0) -> *)
(*        type_of_hfexpr e ce1 = t2 -> *)
(*        CE.find (base_ref r) wm1 = Some t1 -> *)
(*        wm2 = inferWidth_wmap0 (Sfcnct r e) ce1 wm1 -> *)
(*        ce2 = wmap_map2_cenv wm2 ce1 -> *)
(*        ~~ find_unknown (base_ref r) ce1  -> *)
(*        inferWidth_sstmt_sem (Sfcnct r e) wm1 wm2 ce1 ce2. *)
(*    Proof. *)
(*      intros. rewrite H6 H5 /= H1 H3 H2. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      move : (CE.find_some_vtyp H0) => Hv. *)
(*      move : H0 H1 H2 Hv. *)
(*      case : t0; rewrite /= ; intros. *)
(*      - case Hmax : (typeConstraintsGe t1 t2). *)
(*        + move : (typeConstraints_max_width H Hmax) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*            try (apply inferWidth_sfcnct_ftype_le with (aggr_typ f) (aggr_typ t1) t2 c1; *)
(*                 [ done *)
(*                 | rewrite -Hmw (add_ref_wmap0_max_width _ _ H4) /=Hmw// *)
(*                 | done| done| done *)
(*                 | apply (CE.find_some_vtyp); *)
(*                   rewrite /wmap_map2_cenv/= (CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*                 | done]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_sfcnct_ftype_le with (aggr_typ f) (aggr_typ t1) t2 c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. *)
(*          rewrite /wmap_map2_cenv /=(CELemmas.map2_1bis _ _ _ Hnone) (add_ref_wmap0_max_width _ _ H4). *)
(*          rewrite Hmw H0/= H2//. *)
(*        + move : (neg_typeConstraints_max_width H (negbT Hmax)) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*          try (apply inferWidth_sfcnct_ftype_gt with (aggr_typ f) t1 (aggr_typ t2) c1; *)
(*               [ done *)
(*               | rewrite (add_ref_wmap0_max_width _ _ H4) Hmw// *)
(*               | done| done | done *)
(*               | apply CE.find_some_vtyp; rewrite /wmap_map2_cenv(CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*               | rewrite Hmax//]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_sfcnct_ftype_gt with (aggr_typ f) t1 (aggr_typ t2) c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//. *)
(*          rewrite /= Hmax//. *)
(*      - case Hmax : (typeConstraintsGe t1 t2). *)
(*        + move : (typeConstraints_max_width H Hmax) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*             try (apply inferWidth_sfcnct_ftype_le with (reg_typ h) (reg_typ (mk_freg t1 (clock h) (reset h))) t2 c1; *)
(*                 [ done *)
(*                 | rewrite -Hmw (add_ref_wmap0_max_width _ _ H4) /=Hmw// *)
(*                 | done| done| done *)
(*                 | apply (CE.find_some_vtyp); *)
(*                   rewrite /wmap_map2_cenv/= (CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*                 | done]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_sfcnct_ftype_le with (reg_typ h) (reg_typ (mk_freg t1 (clock h) (reset h))) t2 c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. *)
(*          rewrite /wmap_map2_cenv /=(CELemmas.map2_1bis _ _ _ Hnone) (add_ref_wmap0_max_width _ _ H4). *)
(*          rewrite Hmw H0/= H2//. *)
(*        + move : (neg_typeConstraints_max_width H (negbT Hmax)) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*            try (apply inferWidth_sfcnct_ftype_gt with (reg_typ h) t1 (reg_typ (mk_freg t2 (clock h) (reset h))) c1; *)
(*                 [ done *)
(*                 | rewrite (add_ref_wmap0_max_width _ _ H4) Hmw// *)
(*                 | done| done | done *)
(*                 | apply CE.find_some_vtyp; rewrite /wmap_map2_cenv(CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*                 | rewrite Hmax//]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_sfcnct_ftype_gt with (reg_typ h) t1 (reg_typ (mk_freg t2 (clock h) (reset h))) c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//. *)
(*          rewrite /= Hmax//. *)
(*      - case Hmax : (typeConstraintsGe t1 t2). *)
(*        + move : (typeConstraints_max_width H Hmax) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*          try (apply inferWidth_sfcnct_ftype_le with *)
(*              (mem_typ h) (mem_typ (mk_fmem t1 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) t2 c1; *)
(*                 [ done *)
(*                 | rewrite -Hmw (add_ref_wmap0_max_width _ _ H4) /=Hmw// *)
(*                 | done| done| done *)
(*                 | apply (CE.find_some_vtyp); *)
(*                   rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*                 | done]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_sfcnct_ftype_le with (mem_typ h) (mem_typ (mk_fmem t1 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) t2 c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//. *)
(*        + move : (neg_typeConstraints_max_width H (negbT Hmax)) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*            try (apply inferWidth_sfcnct_ftype_gt with (mem_typ h) t1 (mem_typ (mk_fmem t2 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) c1; *)
(*                 [ done *)
(*                 | rewrite (add_ref_wmap0_max_width _ _ H4) Hmw// *)
(*                 | done| done | done *)
(*                 | apply CE.find_some_vtyp; rewrite /wmap_map2_cenv(CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*                 | rewrite Hmax//]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_sfcnct_ftype_gt with (mem_typ h) t1 (mem_typ (mk_fmem t2 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//. *)
(*          rewrite /= Hmax//. *)
(*      - rewrite /find_unknown H0 in H7.  discriminate. *)
(*    Qed. *)

(*    Lemma inferWidth_spcnct_ftype_sem_conform : *)
(*      forall r e c1 t0 t1 t2 wm1 ce1 wm2 ce2 , *)
(*        ftype_weak_equiv t1 t2 -> *)
(*        CE.find (base_ref r) ce1 =  Some (t0, c1) -> *)
(*        type_of_ref r ce1 = type_of_cmpnttyp t0 -> *)
(*        is_deftyp (type_of_cmpnttyp t0) -> *)
(*        type_of_hfexpr e ce1 = t2 -> *)
(*        CE.find (base_ref r) wm1 = Some t1 -> *)
(*        wm2 = inferWidth_wmap0 (Spcnct r e) ce1 wm1 -> *)
(*        ce2 = wmap_map2_cenv wm2 ce1 -> *)
(*        ~~ find_unknown (base_ref r) ce1 -> *)
(*        inferWidth_sstmt_sem (Spcnct r e) wm1 wm2 ce1 ce2. *)
(*    Proof. *)
(*      intros. rewrite H6 H5 /= H1 H3 H2. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      move : (CE.find_some_vtyp H0) => Hv. *)
(*      move : H0 H1 H2 Hv. *)
(*      case : t0; rewrite /= ; intros. *)
(*      - case Hmax : (typeConstraintsGe t1 t2). *)
(*        + move : (typeConstraints_weak_max_width H Hmax) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*            try (apply inferWidth_spcnct_ftype_le with (aggr_typ f) (aggr_typ t1) t2 c1; *)
(*                 [ done *)
(*                 | rewrite -Hmw (add_ref_wmap0_max_width _ _ H4) /=Hmw// *)
(*                 | done| done| done *)
(*                 | apply (CE.find_some_vtyp); *)
(*                   rewrite /wmap_map2_cenv/= (CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*                 | done]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_spcnct_ftype_le with (aggr_typ f) (aggr_typ t1) t2 c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. *)
(*          rewrite /wmap_map2_cenv /=(CELemmas.map2_1bis _ _ _ Hnone) (add_ref_wmap0_max_width _ _ H4). *)
(*          rewrite Hmw H0/= H2//. *)
(*        + move : (neg_typeConstraints_weak_max_width H (negbT Hmax)) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*          try (apply inferWidth_spcnct_ftype_gt with (aggr_typ f) t1 (aggr_typ t2) c1; *)
(*               [ done *)
(*               | rewrite (add_ref_wmap0_max_width _ _ H4) Hmw// *)
(*               | done| done | done *)
(*               | apply CE.find_some_vtyp; rewrite /wmap_map2_cenv(CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*               | rewrite Hmax//]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_spcnct_ftype_gt with (aggr_typ f) t1 (aggr_typ t2) c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//. *)
(*          rewrite /= Hmax//. *)
(*      - case Hmax : (typeConstraintsGe t1 t2). *)
(*        + move : (typeConstraints_weak_max_width H Hmax) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*             try (apply inferWidth_spcnct_ftype_le with (reg_typ h) (reg_typ (mk_freg t1 (clock h) (reset h))) t2 c1; *)
(*                 [ done *)
(*                 | rewrite -Hmw (add_ref_wmap0_max_width _ _ H4) /=Hmw// *)
(*                 | done| done| done *)
(*                 | apply (CE.find_some_vtyp); *)
(*                   rewrite /wmap_map2_cenv/= (CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*                 | done]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_spcnct_ftype_le with (reg_typ h) (reg_typ (mk_freg t1 (clock h) (reset h))) t2 c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. *)
(*          rewrite /wmap_map2_cenv /=(CELemmas.map2_1bis _ _ _ Hnone) (add_ref_wmap0_max_width _ _ H4). *)
(*          rewrite Hmw H0/= H2//. *)
(*        + move : (neg_typeConstraints_weak_max_width H (negbT Hmax)) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*            try (apply inferWidth_spcnct_ftype_gt with (reg_typ h) t1 (reg_typ (mk_freg t2 (clock h) (reset h))) c1; *)
(*                 [ done *)
(*                 | rewrite (add_ref_wmap0_max_width _ _ H4) Hmw// *)
(*                 | done| done | done *)
(*                 | apply CE.find_some_vtyp; rewrite /wmap_map2_cenv(CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*                 | rewrite Hmax//]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_spcnct_ftype_gt with (reg_typ h) t1 (reg_typ (mk_freg t2 (clock h) (reset h))) c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//. *)
(*          rewrite /= Hmax//. *)
(*      - case Hmax : (typeConstraintsGe t1 t2). *)
(*        + move : (typeConstraints_weak_max_width H Hmax) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*          try (apply inferWidth_spcnct_ftype_le with *)
(*              (mem_typ h) (mem_typ (mk_fmem t1 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) t2 c1; *)
(*                 [ done *)
(*                 | rewrite -Hmw (add_ref_wmap0_max_width _ _ H4) /=Hmw// *)
(*                 | done| done| done *)
(*                 | apply (CE.find_some_vtyp); *)
(*                   rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*                 | done]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_spcnct_ftype_le with (mem_typ h) (mem_typ (mk_fmem t1 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) t2 c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//. *)
(*        + move : (neg_typeConstraints_weak_max_width H (negbT Hmax)) => Hmw. *)
(*          move : H3 H5. *)
(*          case e; intros; *)
(*            try (apply inferWidth_spcnct_ftype_gt with (mem_typ h) t1 (mem_typ (mk_fmem t2 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) c1; *)
(*                 [ done *)
(*                 | rewrite (add_ref_wmap0_max_width _ _ H4) Hmw// *)
(*                 | done| done | done *)
(*                 | apply CE.find_some_vtyp; rewrite /wmap_map2_cenv(CELemmas.map2_1bis _ _ _ Hnone); *)
(*                   rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw// *)
(*                 | rewrite Hmax//]). *)
(*          rewrite /= in H3; rewrite H3. *)
(*          apply inferWidth_spcnct_ftype_gt with (mem_typ h) t1 (mem_typ (mk_fmem t2 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) c1; try done. *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//. *)
(*          apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*          rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//. *)
(*          rewrite /= Hmax//. *)
(*      - rewrite /find_unknown H0 in H7. discriminate. *)
(*    Qed. *)


(*    Lemma inferWidth_sfcnct_sem_conform : *)
(*      forall v1 e c1 t0 t1 t2 wm1 ce1 wm2 ce2 , *)
(*        ftype_equiv (Gtyp t1) (Gtyp t2) -> *)
(*        CE.find v1 ce1 = Some (aggr_typ (Gtyp t0), c1) -> *)
(*        is_deftyp (Gtyp t0) -> *)
(*        type_of_hfexpr e ce1 = (Gtyp t2) -> *)
(*        CE.find v1 wm1 = Some (Gtyp t1) -> *)
(*        wm2 = inferWidth_wmap0 (Sfcnct (eid v1) e) ce1 wm1 -> *)
(*        ce2 = wmap_map2_cenv wm2 ce1 -> *)
(*        inferWidth_sstmt_sem (Sfcnct (eid v1) e) wm1 wm2 ce1 ce2. *)
(*    Proof. *)
(*      intros. rewrite H4 /= (CE.find_some_vtyp H0) H1 H3. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      case Hmax : (sizeof_fgtyp t2 <= sizeof_fgtyp t1). *)
(*      - move : (sizeof_fgtyp_lt_max_width (ftype_equiv_symmetry H) (Hmax)) => Hmw . *)
(*        move : H2 H4. *)
(*        case He : e => [ct c| c e1 | u e1 | op e1 e2 | c e1 e2 | c e1 | r2 ] H2 H4; *)
(*                         try (apply inferWidth_sfcnct_gtyp_le with c1 t0 t1 t2; *)
(*                            [done *)
(*                            | rewrite H2 Hmw (CELemmas.add_eq_o wm1 _ (eq_refl v1))// *)
(*                            | done| done| done *)
(*                            | rewrite H5 H4 /wmap_map2_cenv /inferWidth_wmap0 H2; *)
(*                              rewrite (lock add_ref_wmap0)/= (CE.find_some_vtyp H0) (lock is_deftyp)/= -!lock H1; *)
(*                              rewrite (CELemmas.map2_1bis (add_ref_wmap0 (eid v1) (Gtyp t2) ce1 wm1) ce1 v1 Hnone); *)
(*                              rewrite /add_ref_wmap0 (lock max_width) /= -lock H3 Hmw; *)
(*                              rewrite (CELemmas.add_eq_o wm1 (Gtyp t1) (eq_refl v1)) H0; *)
(*                              rewrite /add_width_2_cenv (lock is_deftyp)/= -lock H1// *)
(*                            | done]). *)
(*        + rewrite /type_of_hfexpr in H2. rewrite H2. *)
(*          apply inferWidth_sfcnct_gtyp_le with c1 t0 t1 t2; try done. *)
(*          rewrite Hmw (CELemmas.add_eq_o wm1 (Gtyp t1) (eq_refl v1))//. *)
(*          rewrite H5 H4/wmap_map2_cenv /inferWidth_wmap0 H2. *)
(*          rewrite (lock add_ref_wmap0)/= (CE.find_some_vtyp H0) (lock is_deftyp)/= -lock H1/=-lock. *)
(*          rewrite /add_ref_wmap0 (lock max_width)/= H3 -lock Hmw. *)
(*          rewrite (CELemmas.map2_1bis (CE.add v1 (Gtyp t1) wm1) ce1 v1 Hnone) H0. *)
(*          rewrite (CELemmas.add_eq_o wm1 (Gtyp t1) (eq_refl v1)) /add_width_2_cenv (lock is_deftyp)/=. *)
(*          rewrite -lock H1//. *)
(*      - move : (negbT Hmax). rewrite -ltnNge => Hlt. *)
(*        move : (sizeof_fgtyp_lt_max_width H (ltnW Hlt)) => Hmw. *)
(*        move : H2 H4. *)
(*        case He : e => [ct c| c e1 | u e1 | op e1 e2 | c e1 e2 | c e1 | r2 ] H2 H4; *)
(*                         try (apply inferWidth_sfcnct_gtyp_gt with c1 t0 t1 t2; *)
(*                            [ done *)
(*                            | rewrite H2 max_width_symmetry Hmw (CELemmas.add_eq_o wm1 (Gtyp t2) (eq_refl v1))// *)
(*                            | done| done| done *)
(*                            | rewrite H5 H4 /wmap_map2_cenv /inferWidth_wmap0 H2; *)
(*                              rewrite (lock add_ref_wmap0)/= (CE.find_some_vtyp H0) (lock is_deftyp)/= -!lock H1; *)
(*                              rewrite (CELemmas.map2_1bis (add_ref_wmap0 (eid v1) (Gtyp t2) ce1 wm1) ce1 v1 Hnone); *)
(*                              rewrite /add_ref_wmap0 (lock max_width) /= -lock H3 max_width_symmetry Hmw; *)
(*                              rewrite (CELemmas.add_eq_o wm1 (Gtyp t2) (eq_refl v1)) H0; *)
(*                              rewrite /add_width_2_cenv (lock is_deftyp)/= -lock H1// *)
(*                            | done]). *)
(*        + rewrite /= in H2; rewrite H2. *)
(*          apply inferWidth_sfcnct_gtyp_gt with c1 t0 t1 t2; try done. *)
(*          rewrite max_width_symmetry Hmw (CELemmas.add_eq_o wm1 (Gtyp t2) (eq_refl v1))//. *)
(*          rewrite H5 H4/wmap_map2_cenv /inferWidth_wmap0 H2. *)
(*          rewrite (lock add_ref_wmap0)/= (CE.find_some_vtyp H0) (lock is_deftyp)/= -lock H1/=-lock. *)
(*          rewrite /add_ref_wmap0 (lock max_width)/= H3 -lock max_width_symmetry Hmw. *)
(*          rewrite (CELemmas.map2_1bis (CE.add v1 (Gtyp t2) wm1) ce1 v1 Hnone) H0. *)
(*          rewrite (CELemmas.add_eq_o wm1 (Gtyp t2) (eq_refl v1)) /add_width_2_cenv (lock is_deftyp)/=. *)
(*          rewrite -lock H1//. *)
(*    Qed. *)

(*    Lemma inferWidth_sskip_sem_conform : *)
(*      forall wm1 wm2 ce1 ce2, *)
(*        wm2 = inferWidth_wmap0 sskip ce1 wm1 -> *)
(*        ce2 = wmap_map2_cenv wm2 ce1 -> *)
(*        inferWidth_sstmt_sem (sskip) wm1 wm2 ce1 ce2. *)
(*    Proof. *)
(*      move => wm1 wm2 ce1 ce2 H H1. rewrite /= in H. *)
(*      apply inferWidth_sskip. intros. *)
(*      rewrite H1 H. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*      rewrite H0 H2. *)
(*      split. done. *)
(*      case t; rewrite /=; intros; try done. *)
(*      case (is_deftyp f); done. *)
(*      case (is_deftyp (type h)); try done. *)
(*      case h; intros; rewrite /=//. *)
(*      case (is_deftyp (data_type h)); try done. *)
(*      case h; intros; rewrite //. *)
(*    Qed. *)

(*    (* Lemma inferWidth_sstop_sem_conform : *) *)
(*    (*   forall wm1 wm2 ce1 ce2 ss1 ss2 n, *) *)
(*    (*     wm2 = inferWidth_wmap0 (sstop ss1 ss2 n) ce1 wm1 -> *) *)
(*    (*     ce2 = wmap_map2_cenv wm2 ce1 -> *) *)
(*    (*     inferWidth_sstmt_sem (sstop ss1 ss2 n) wm1 wm2 ce1 ce2. *) *)
(*    (* Proof. *) *)
(*    (*   move => wm1 wm2 ce1 ce2 ss1 ss2 n H H1. rewrite /= in H. *) *)
(*    (*   apply inferWidth_sstop. intros. *) *)
(*    (*   rewrite H1 H. *) *)
(*    (*   have Hnone : (add_width_2_cenv None None = None) by done. *) *)
(*    (*   rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *) *)
(*    (*   rewrite H0 H2. *) *)
(*    (*   split. done. *) *)
(*    (*   case t; rewrite /=; intros; try done. *) *)
(*    (*   case (is_deftyp f); done. *) *)
(*    (*   case (is_deftyp (type h)); try done. *) *)
(*    (*   case h; intros; rewrite /=//. *) *)
(*    (*   case (is_deftyp (data_type h)); try done. *) *)
(*    (*   case h; intros; rewrite //. *) *)
(*    (* Qed. *) *)

(*    Lemma inferWidth_sinvalid_sem_conform : *)
(*      forall wm1 wm2 ce1 ce2 v, *)
(*        wm2 = inferWidth_wmap0 (sinvalid v) ce1 wm1 -> *)
(*        ce2 = wmap_map2_cenv wm2 ce1 -> *)
(*        inferWidth_sstmt_sem (sinvalid v) wm1 wm2 ce1 ce2. *)
(*    Proof. *)
(*      move => wm1 wm2 ce1 ce2 v H H1. rewrite /= in H. *)
(*      apply inferWidth_sinvalid. intros. *)
(*      rewrite H1 H. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*      rewrite H0 H2. *)
(*      split. done. *)
(*      case t; rewrite /=; intros; try done. *)
(*      case (is_deftyp f); done. *)
(*      case (is_deftyp (type h)); try done. *)
(*      case h; intros; rewrite /=//. *)
(*      case (is_deftyp (data_type h)); try done. *)
(*      case h; intros; rewrite //. *)
(*    Qed. *)

(*    Lemma inferWidth_swhen_sem_conform_tmp : *)
(*      forall wm1 wm2 ce1 ce2 ss1 ss2 n, *)
(*        wm2 = inferWidth_wmap0 (swhen ss1 ss2 n) ce1 wm1 -> *)
(*        ce2 = wmap_map2_cenv wm2 ce1 -> *)
(*        inferWidth_sstmt_sem (swhen ss1 ss2 n) wm1 wm2 ce1 ce2. *)
(*    Proof. *)
(*      move => wm1 wm2 ce1 ce2 ss1 ss2 n H H1. rewrite /= in H. *)
(*      apply inferWidth_swhen. intros. *)
(*      rewrite H1 H. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *)
(*      rewrite H0 H2. *)
(*      split. done. *)
(*      case t; rewrite /=; intros; try done. *)
(*      case (is_deftyp f); done. *)
(*      case (is_deftyp (type h)); try done. *)
(*      case h; intros; rewrite /=//. *)
(*      case (is_deftyp (data_type h)); try done. *)
(*      case h; intros; rewrite //. *)
(*    Qed. *)

(*    Lemma cefind_eq_eq_width : *)
(*      forall v (ce1 ce2 : cenv) t1 t2 c, *)
(*        CE.find v ce1 = Some (t1, c) -> *)
(*        CE.find v ce2 = Some (t2, c) -> *)
(*        CE.find v ce1 = CE.find v ce2 -> *)
(*        typeConstraintsGe (type_of_cmpnttyp t2) (type_of_cmpnttyp t1). *)
(*    Proof. *)
(*    Admitted. *)

(*    Lemma inferWidth_sstmt_sem_conform : *)
(*      forall st wm1 wm2 ce1 ce2 *)
(*        t1 t2, *)
(*            (* CE.find (base_ref r) ce1 = Some (t1, c) -> *) *)
(*            (* is_deftyp (type_of_cmpnttyp t1) -> *) *)
(*            (* CE.find (base_ref r) ce2 = Some (t2, c) -> *) *)
(*        wm2 = inferWidth_wmap0 st ce1 wm1 -> *)
(*        ce2 = wmap_map2_cenv wm2 ce1 -> *)
(*        inferWidth_sstmt_sem st wm1 wm2 ce1 ce2 -> *)
(*        (forall r c, *)
(*            ftype_equiv (type_of_cmpnttyp t1) (type_of_cmpnttyp t2) /\ *)
(*            CE.find (base_ref r) ce1 = Some (t1, c) /\ *)
(*            CE.find (base_ref r) ce2 = Some (t2, c)) -> *)
(*        typeConstraintsGe (type_of_cmpnttyp t2) (type_of_cmpnttyp t1). *)
(*    Proof. *)
(*    Admitted. *)


(*    Inductive inferWidth_stmts_sem : hfstmt_seq -> cenv -> cenv -> Prop := *)
(*    | inferWidth_stmts_nil ce1 ce2 : *)
(*        (forall v, *)
(*          CE.find v ce1 = CE.find v ce2) -> *)
(*          inferWidth_stmts_sem qnil ce1 ce2 *)
(*    | inferWidth_stmts_imp st sts (ce1 ce2 ce3 : cenv) : *)
(*        (forall r  t1 c, *)
(*            new_comp_name (base_ref r) /\ *)
(*            CE.find (base_ref r) ce1 = Some (t1, c) /\ *)
(*            (* is_deftyp (type_of_cmpnttyp t1) -> *) *)
(*            ~~ is_deftyp (type_of_cmpnttyp (fst (CE.vtyp (base_ref r) ce3))) -> *)
(*            exists (wm1 wm2 : wmap0), *)
(*              inferWidth_sstmt_sem st wm1 wm2 ce1 ce2) -> *)
(*        (exists wm1 wm2, inferWidth_sstmt_sem st wm1 wm2 ce1 ce2) -> *)
(*        inferWidth_stmts_sem sts ce2 ce3 -> *)
(*        inferWidth_stmts_sem (Qcons st sts) ce1 ce3. *)

(*    Lemma infer_stmt_lst st ss ce1 : *)
(*      forall wm0 wm1 , *)
(*        wm1 = inferWidth_wmap0 st ce1 wm0 -> *)
(*        inferWidth_fun (Qcons st ss) ce1 = inferWidth_fun ss (wmap_map2_cenv wm1 ce1). *)
(*    Proof. Admitted. *)

(*    Lemma inferType_stmts_hd ss sts ce0 ce1 : *)
(*      inferType_stmts (Qcons ss sts) ce0 ce1 -> *)
(*      inferType_stmt ss ce0 ce1. *)
(*    Proof. *)
(*    Admitted. *)

(*    Lemma type_of_hexpr_cefind r ce t : *)
(*      CE.find (base_ref r) ce = Some t -> *)
(*      type_of_ref (r) ce = type_of_cmpnttyp (fst t). *)
(*    Proof. Admitted. *)

(*   (*   inferType_stmts_unknow : seq hfstmt -> cenv -> cenv -> Prop := *) *)
(*   (* | Infertype_stmts_know ss ce ce' : *) *)
(*   (*     (exists v,  *) *)
(*   (*                ~~ find_unknown v ce') -> *) *)
(*   (*     inferType_stmts (ss) ce ce'. *) *)

(*    Definition is_inital (s : hfstmt) : bool := *)
(*      match s with *)
(*      | Spcnct _ _ | Sfcnct _ _ | Sinvalid _ | Swhen _ _ _ *)
(*      (* | Sstop _ _ _  *)| Sskip => false *)
(*      | _ => true *)
(*      end. *)

(*    Fixpoint is_inital_all_t (s : hfstmt_seq) : bool := *)
(*      match (s) with *)
(*      | Qnil => true *)
(*      | Qcons h t => if (is_inital h) then is_inital_all_t t else false *)
(*      end. *)

(*    Fixpoint not_inital_all (s : hfstmt_seq) : bool := *)
(*      match s with *)
(*      | Qnil => true *)
(*      | Qcons h t => if (is_inital h) then false else not_inital_all t *)
(*      end. *)

(*    Lemma inferWidth_stmts_inital_sem_conform : *)
(*      forall sts ce0 ce1 (v:var), *)
(*        ( *)
(*          exists wm0 wm1, *)
(*            forall r t , *)
(*              new_comp_name (base_ref r) /\ *)
(*              is_inital_all_t sts /\ *)
(*               inferWidth_wmap0 (Qhead sskip sts) ce1 wm0 = wm1 /\ *)
(*            CE.find (base_ref r) ce0 = Some t /\ *)
(*            is_deftyp (type_of_cmpnttyp (fst t)) /\ *)
(*            ~~ find_unknown (base_ref r) ce1 /\ *)
(*            ~~ is_deftyp (type_of_cmpnttyp (fst (CE.vtyp (base_ref r) (inferWidth_fun sts ce1)))) *)
(*            )-> *)
(*            (* ~~ is_deftyp (type_of_cmpnttyp (fst (CE.vtyp v (inferWidth_fun sts ce1)))) /\ *) *)
(*            (*ce2 = wmap_map2_cenv wm1 ce1 /\*) *)
(*            inferType_stmts sts ce0 ce1 -> *)
(*        inferWidth_stmts_sem sts ce1 (inferWidth_fun sts ce1). *)
(*    Proof. *)
(*      have Hnone : (add_width_2_cenv None None = None) by done. *)
(*      elim => [ce0 ce1  v He Hiw | st ss Hm ce0 ce1 v He Hiw]. *)
(*      - *)
(*        apply inferWidth_stmts_nil. rewrite /inferWidth_fun/wmap_map2_cenv/=. intro. *)
(*        rewrite (CELemmas.map2_1bis _ _ _ Hnone). rewrite CELemmas.empty_o//. *)
(*      - *)
(*        case He => [wm0 [wm1 Hec]]. *)
(*        apply inferWidth_stmts_imp with (wmap_map2_cenv wm1 ce1). *)
(*        move : Hec Hiw. *)
(*        elim st. *)
(*        + (*skip*) *)
(*          intros. *)
(*          move : (Hec (r) (aggr_typ def_ftype, Node) (* sskip *)) => [Hbrs1 [Hbrt [Hi[Hdt [Hndt [Hun Hit]]]]]]. *)
(*          (* move : Hbrt => [ [Hinit Hi]].  *) rewrite /= in Hbrt. *)
(*          rewrite //. *)
(*          (* exists wm0; exists wm1. *) *)
(*          (* apply inferWidth_sskip_sem_conform; try done. *) *)
(*          (* move : (Hec (r) (aggr_typ def_ftype, Node) ) => [Hbrs1 [Hbrt [Hdt [Hndt [Hun Hit]]]]]. *) *)
(*          (* rewrite //. *) *)
(*        + (*swire*) *)
(*          intros. *)
(*          exists wm0; exists wm1. *)
(*          move : (Hec (Eid s) (aggr_typ f, Wire) (* (Swire s f) *)) => [Hbrs1 [Hbrt [Hi [Hdt [Hndt [Hun Hit]]]]]]. *)
(*          move : (new_v_wmap_none Hbrs1 wm0) => Hnv. *)
(*          apply inferWidth_swire_sem_conform with ce0; try done. *)
(*          exact : (inferType_stmts_hd Hiw). *)
(*        + (*reg*) *)
(*          intros. *)
(*          exists wm0; exists wm1. *)
(*          move : (Hec (Eid s) (reg_typ h, Register) (* (Sreg s h) *)) => [Hbrs1 [Hbrt [Hi[Hdt [Hndt [Hun Hit]]]]]]. *)
(*          apply inferWidth_sreg_sem_conform with ce0; try done. *)
(*          exact : (inferType_stmts_hd Hiw). *)
(*        + (*mem*) *)
(*          intros. *)
(*          exists wm0; exists wm1. *)
(*          move : (Hec (Eid s) (CE.vtyp s ce0) (* (Smem s h) *)) => [Hbrs1 [Hbrt [Hi[Hdt [Hndt [Hun Hit]]]]]]. *)
(*          apply inferWidth_smem_sem_conform with ce0; try done. *)
(*          exact : (inferType_stmts_hd Hiw). *)
(*        + (*inst*) *)
(*          intros. *)
(*          move : (Hec (Eid s) (CE.vtyp s0 ce0) (* (Sinst s s0) *)) => [Hbrs1 [Hbrt [Hi[Hdt [Hndt [Hun Hit]]]]]]. *)
(*          exists wm0; exists wm1. *)
(*          apply inferWidth_sinst_sem_conform with ce0; try done. *)
(*          exact : (inferType_stmts_hd Hiw). *)
(*        + (*node*) *)
(*          intros. *)
(*          exists wm0; exists wm1. *)
(*          move : (Hec (Eid s) (CE.vtyp s ce0) (* (Snode s h) *)) => [Hbrs1 [Hbrt [Hi [Hdt [Hndt [Hun Hit]]]]]]. *)
(*          apply inferWidth_snode_sem_conform with ce0; try done. *)
(*          exact : (inferType_stmts_hd Hiw). *)
(*        + (*fcnct*) *)
(*          intros. *)
(*          move : (Hec h (CE.vtyp (base_ref h) ce0) (* (Sfcnct h h0) *)) => [Hbrs1 [Hbrt [Hi[Hdt [Hndt [Hun Hit]]]]]]. *)
(*          rewrite //. *)
(*          (* exists wm0; exists wm1. *) *)
(*          (* move : (inferType_stmts_hd Hiw) => Hitc. *) *)
(*          (* inversion Hitc; subst.  *) *)
(*          (* apply inferWidth_sfcnct_ftype_sem_conform with (snd (CE.vtyp (base_ref h) ce1)) ( (fst (CE.vtyp (base_ref h) ce1))) (type_of_cmpnttyp (fst (CE.vtyp (base_ref h) ce1))) (type_of_cmpnttyp (fst (CE.vtyp (base_ref h) (wmap_map2_cenv wm0 ce1)))); try done. *) *)
(*          (* move : (H3 ((fst (CE.vtyp (base_ref h) ce1))) *) *)
(*          (*            (type_of_cmpnttyp (fst (CE.vtyp (base_ref h) (wmap_map2_cenv wm0 ce1)))) *) *)
(*          (*            (snd (CE.vtyp (base_ref h) ce1))) => [Hit1 [Hit2 Hit3]]. *) *)
(*          (* rewrite //. *) *)
(*          (* move : (CE.find_some_vtyp Hbrt) => Hv. rewrite -surjective_pairing -Hbrt//. *) *)
(*          (* exact : (type_of_hexpr_cefind Hbrt). *) *)
(*          (* move : (H3 ((fst (CE.vtyp (base_ref h) ce1))) *) *)
(*          (*            (type_of_cmpnttyp (fst (CE.vtyp (base_ref h) (wmap_map2_cenv wm0 ce1)))) *) *)
(*          (*            (snd (CE.vtyp (base_ref h) ce1))) => [Hit1 [Hit2 Hit3]]. *) *)
(*          (* done. *) *)
(*        + (*pcnct*) *)
(*          intros. *)
(*          move : (Hec h (CE.vtyp (base_ref h) ce0) (* (Spcnct h h0) *)) => [Hbrs1 [Hbrt [Hi[Hdt [Hndt [Hun Hit]]]]]]. *)
(*          rewrite //. *)
(*        (* exists wm0; exists wm1. *) *)
(*        (* move : (inferType_stmts_hd Hiw) => Hitc. *) *)
(*        (* inversion Hitc; subst.  *) *)
(*        (* apply inferWidth_spcnct_ftype_sem_conform with (snd (CE.vtyp (base_ref h) ce1)) ( (fst (CE.vtyp (base_ref h) ce1))) (type_of_cmpnttyp (fst (CE.vtyp (base_ref h) ce1))) (type_of_cmpnttyp (fst (CE.vtyp (base_ref h) (wmap_map2_cenv wm0 ce1)))); try done. *) *)
(*        (* move : (H3 ((fst (CE.vtyp (base_ref h) ce1))) *) *)
(*        (*            (type_of_cmpnttyp (fst (CE.vtyp (base_ref h) (wmap_map2_cenv wm0 ce1)))) *) *)
(*        (*            (snd (CE.vtyp (base_ref h) ce1))) => [Hit1 [Hit2 Hit3]]. *) *)
(*        (* rewrite //. *) *)
(*        (* move : (CE.find_some_vtyp Hbrt) => Hv. rewrite -surjective_pairing -Hbrt//. *) *)
(*        (* exact : (type_of_hexpr_cefind Hbrt). *) *)
(*        (* move : (H3 ((fst (CE.vtyp (base_ref h) ce1))) *) *)
(*        (*            (type_of_cmpnttyp (fst (CE.vtyp (base_ref h) (wmap_map2_cenv wm0 ce1)))) *) *)
(*        (*            (snd (CE.vtyp (base_ref h) ce1))) => [Hit1 [Hit2 Hit3]]. *) *)
(*        (* done. *) *)
(*        + (*invalid*) *)
(*          intros. *)
(*          move : (Hec (h) (aggr_typ def_ftype, Node) (* (Sinvalid h) *)) => [Hbrs1 [Hbrt [Hi[Hdt [Hndt [Hun Hit]]]]]]. *)
(*          rewrite //. *)
(*        (* exists wm0; exists wm1. *) *)
(*        (* rewrite /= in Hdt. rewrite /= in Hbrt; rewrite /= in Hbrs1. *) *)
(*        (* apply inferWidth_sinvalid; try rewrite //. *) *)
(*        (* rewrite Hiw//. *) *)
(*        (* rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone) Hbrs1. *) *)
(*        (* move : (inferType_stmts_hd Hit) => Hits. *) *)
(*        (* inversion Hits; subst. rewrite Hbrt//. *) *)
(*        + (*when*) *)
(*          intros. *)
(*          move : (Hec (r) (aggr_typ def_ftype, Node) (* (Swhen h l l0) *)) => [Hbrs1 [Hbrt [Hi[Hdt [Hndt [Hun Hit]]]]]]. *)
(*          rewrite //. *)
(*        (* rewrite /= in Hiw; rewrite /= in Hbrs; rewrite /= in Hbrt. *) *)
(*        (* apply inferWidth_swhen with (Eid v); try rewrite //. *) *)
(*        (* rewrite Hiw//. *) *)
(*        (* rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone) Hbrs1. *) *)
(*        (* move : (inferType_stmts_hd Hit) => Hits. *) *)
(*        (* inversion Hits; subst.  *) *)
(*        (* + (*stop*) *) *)
(*        (*   intros. *) *)
(*        (*   move : (Hec (r) (aggr_typ def_ftype, Node) (* (Sstop h h0 n) *)) => [Hbrs1 [Hbrt [Hi[Hdt [Hndt [Hun Hit]]]]]]. *) *)
(*        (*   rewrite //. *) *)
(*          (* rewrite /= in Hiw; rewrite /= in Hbrs; rewrite /= in Hbrt. *) *)
(*          (* apply inferWidth_sstop with v; try rewrite //. *) *)
(*          (* rewrite Hiw//. *) *)
(*          (* rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone) Hbrs1. *) *)
(*          (* move : (inferType_stmts_hd Hit) => Hits. *) *)
(*          (* inversion Hits; subst.  *) *)
(*        + *)
(*          move : (Hec (Eid v) (aggr_typ def_ftype, Node)) => [Hbrs1 [Hbrt [Hi[Hdt [Hndt [Hun Hit]]]]]]. *)
(*          symmetry in Hi. *)

(*          (* rewrite (infer_stmt_lst _ Hi). *) *)
(*    (*       apply Hm with ce0 (*wmap_map2_cenv wm1 ce1*) ; try done. *) *)
(*    (*       exists wm1; exists (inferWidth_wmap0 (hd sskip ss) (wmap_map2_cenv wm1 ce1) wm1). *) *)
(*    (*       intros. *) *)
(*    (*       move : (Hec r t) => [Hbrs10 [Hbrt0 [Hin0 [Hdt0 [Hndt0 [Hun0 Hit0]]]]]]. *) *)
(*    (*       repeat (split; try done). *) *)
(*    (*       rewrite /= in Hbrt0. move : Hbrt0. case (is_inital st); try done. *) *)
(*    (*       rewrite /wmap_map2_cenv/find_unknown (CELemmas.map2_1bis _ _ _ Hnone). *) *)
(*    (*       rewrite (new_v_wmap_none Hbrs10 wm1)/=. *) *)
(*    (*       rewrite /find_unknown/= in Hun0. done. *) *)
(*    (*       move : Hit0. rewrite (infer_stmt_lst ss Hi)//. *) *)
(*    (*       inversion Hiw. *) *)
(*    (*       apply Infertype_stmts_know. *) *)
(*    (*       exists (base_ref (Eid v)). *) *)
(*    (*       rewrite /find_unknown/wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *) *)
(*    (*       rewrite (new_v_wmap_none Hbrs1 wm1)/=. *) *)
(*    (*       rewrite /find_unknown/= in Hun. done. *) *)
(*    (* Qed. *) *)
(* Admitted. *)


(*    (*       rewrite (infer_stmt_lst _ Hi). *) *)
(*    (*       apply Hm with ce0 (*wmap_map2_cenv wm1 ce1*) ; try done. *) *)
(*    (*       exists wm1; exists (inferWidth_wmap0 (Qhead sskip ss) (wmap_map2_cenv wm1 ce1) wm1). *) *)
(*    (*       intros. *) *)
(*    (*       move : (Hec r t) => [Hbrs10 [Hbrt0 [Hin0 [Hdt0 [Hndt0 [Hun0 Hit0]]]]]]. *) *)
(*    (*       repeat (split; try done). *) *)
(*    (*       rewrite /= in Hbrt0. move : Hbrt0. case (is_inital st); try done. *) *)
(*    (*       rewrite /wmap_map2_cenv/find_unknown (CELemmas.map2_1bis _ _ _ Hnone). *) *)
(*    (*       rewrite (new_v_wmap_none Hbrs10 wm1)/=. *) *)
(*    (*       rewrite /find_unknown/= in Hun0. done. *) *)
(*    (*       move : Hit0. rewrite (infer_stmt_lst ss Hi)//. *) *)
(*    (*       apply Infertype_stmts_know. *) *)
(*    (*       exists (base_ref (Eid v)). *) *)
(*    (*       rewrite /find_unknown/wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone). *) *)
(*    (*       rewrite (new_v_wmap_none Hbrs1 wm1)/=. *) *)
(*    (*       rewrite /find_unknown/= in Hun. done. *) *)
(*    (* Qed. *) *)



(*    Parameter not_init_wmfind_some : *)
(*      forall s, ~~ is_init s -> forall v (wm:wmap0) t, CE.find v wm = Some t. *)
(*    Parameter infer_type_no_unknown_type : *)
(*      forall sts ce0 ce1, inferType_stmts sts ce0 ce1 -> forall v c, ~ (CE.find v ce1 = Some (unknown_typ, c)). *)

(*    Parameter find_same_ce_wmap2ce : *)
(*      forall v (ce1 ce2: cenv) wm1, *)
(*      CE.find v ce1 = CE.find v ce2 -> *)
(*      wmap_map2_cenv wm1 ce1 = wmap_map2_cenv wm1 ce2. *)

(*    Parameter typeof_same_ce : *)
(*      forall v e (ce1 ce2: cenv) , *)
(*      CE.find v ce1 = CE.find v ce2 -> *)
(*      type_of_hfexpr e ce1 = type_of_hfexpr e ce2. *)
(*    Parameter typeofr_same_ce : *)
(*      forall v e (ce1 ce2: cenv) , *)
(*      CE.find v ce1 = CE.find v ce2 -> *)
(*      type_of_ref e ce1 = type_of_ref e ce2. *)
(*    Parameter add_wmap_same_ce : *)
(*      forall h t (ce1 ce2: cenv) wm, *)
(*      CE.find (base_ref h) ce1 = CE.find (base_ref h) ce2 -> *)
(*      add_ref_wmap0 h t ce1 wm = *)
(*    add_ref_wmap0 h t ce2 wm. *)


(*    Inductive inferWidth_stmts_sem' : seq hfstmt -> cenv -> cenv -> Prop := *)
(*    | inferWidth_stmts_nil' ce1 ce2 : *)
(*        (forall v, *)
(*          CE.find v ce1 = CE.find v ce2) -> *)
(*          inferWidth_stmts_sem' nil ce1 ce2 *)
(*    | inferWidth_stmts_cons' st sts (ce1 ce2 ce3 : cenv) : *)
(*        (* (forall r  t1 c, *) *)
(*        (*     new_comp_name (base_ref r) /\ *) *)
(*        (*     CE.find (base_ref r) ce1 = Some (t1, c) /\ *) *)
(*        (*     (* is_deftyp (type_of_cmpnttyp t1) -> *) *) *)
(*        (*     ~~ is_deftyp (type_of_cmpnttyp (fst (CE.vtyp (base_ref r) ce3))) -> *) *)
(*        (*     exists (wm1 wm2 : wmap0), *) *)
(*        (*       inferWidth_sstmt_sem st wm1 wm2 ce1 ce2) -> *) *)
(*        (exists wm1 wm2, inferWidth_sstmt_sem st wm1 wm2 ce1 ce2) -> *)
(*        inferWidth_stmts_sem' sts ce2 ce3 -> *)
(*        inferWidth_stmts_sem' (st :: sts) ce1 ce3. *)

   (* Lemma inferWidth_stmts_sem_conform' : *)
   (*   forall (sts:seq hfstmt) ce0 ce1 ce2, *)
   (*     (* ( *) *)
   (*     (*   exists wm0 wm1, *) *)
   (*     (*     forall r t , *) *)
   (*     (*       new_comp_name (base_ref r) /\ *) *)
   (*     (*       inferWidth_wmap0 (hd sskip sts) ce1 wm0 = wm1 /\ *) *)
   (*     (*       CE.find (base_ref r) ce0 = Some t /\ *) *)
   (*     (*       CE.find (base_ref r) wm0 = Some (type_of_cmpnttyp (fst t)) /\ *) *)
   (*     (*     is_deftyp (type_of_cmpnttyp (fst t)) /\ *) *)
   (*     (*     ~~ find_unknown (base_ref r) ce1 /\ *) *)
   (*     (*     ~~ is_deftyp (type_of_cmpnttyp (fst (CE.vtyp (base_ref r) (inferWidth_fun sts ce1))))  *) *)
   (*     (*     )-> *) *)
   (*     (inferType_stmts sts ce0 ce1 /\ forall v, CE.find v ce1 = CE.find v ce2) -> *)
   (*     inferWidth_stmts_sem' sts ce2 (inferWidth_fun sts ce2). *)

   (* Lemma inferWidth_stmts_sem_conform : *)
   (*   forall (sts : hfstmt_seq) ce0 ce1 (v:var), *)
   (*     ( *)
   (*       exists wm0 wm1, *)
   (*         forall r t , *)
   (*           new_comp_name (base_ref r) /\ *)
   (*           inferWidth_wmap0 (Qhead sskip sts) ce1 wm0 = wm1 /\ *)
   (*           CE.find (base_ref r) ce0 = Some t /\ *)
   (*           CE.find (base_ref r) wm0 = Some (type_of_cmpnttyp (fst t)) /\ *)
   (*         is_deftyp (type_of_cmpnttyp (fst t)) /\ *)
   (*         ~~ find_unknown (base_ref r) ce1 /\ *)
   (*         ~~ is_deftyp (type_of_cmpnttyp (fst (CE.vtyp (base_ref r) (inferWidth_fun sts ce1)))) *)
   (*         )-> *)
   (*         (* ~~ is_deftyp (type_of_cmpnttyp (fst (CE.vtyp v (inferWidth_fun sts ce1)))) /\ *) *)
   (*         (*ce2 = wmap_map2_cenv wm1 ce1 /\*) *)
   (*         inferType_stmts sts ce0 ce1 -> *)
   (*     inferWidth_stmts_sem sts ce1 (inferWidth_fun sts ce1). *)
   (* Proof. *)
   (*   have Hnone : (add_width_2_cenv None None = None) by done. *)
   (*   elim => [ce0 ce1 ce2 Hiw | st ss Hm ce0 ce1 ce2 Hiw]. *)
   (*   - apply inferWidth_stmts_nil'. intros. *)
   (*     rewrite /inferWidth_fun/wmap_map2_cenv/=. *)
   (*     rewrite (CELemmas.map2_1bis _ _ _ Hnone) CELemmas.empty_o//. *)
   (*   - *)
   (*     have Hin : ((is_init st) \/ ~~(is_init st)) by (case (is_init st); [by left| by right]). *)
   (*     rewrite /inferWidth_fun. *)
   (*     apply inferWidth_stmts_cons' with (wmap_map2_cenv (inferWidth_wmap0 st ce1 empty_wmap0)  ce1). *)
   (*     move : Hiw => [Hif Hce12]. *)
   (*     inversion Hif; subst. *)
   (*     exists empty_wmap0 . exists (inferWidth_wmap0 st ce1 empty_wmap0). *)
   (*     move : Hif H1 Hin. *)

   (* Lemma inferWidth_stmts_sem_conform : *)
   (*   forall sts ce0 ce1 (v:var), *)
   (*     ( *)
   (*       exists wm0 wm1, *)
   (*         forall r t , *)
   (*           new_comp_name (base_ref r) /\ *)
   (*           inferWidth_wmap0 (hd sskip sts) ce1 wm0 = wm1 /\ *)
   (*           CE.find (base_ref r) ce0 = Some t /\ *)
   (*           CE.find (base_ref r) wm0 = Some (type_of_cmpnttyp (fst t)) /\ *)
   (*         is_deftyp (type_of_cmpnttyp (fst t)) /\ *)
   (*         ~~ find_unknown (base_ref r) ce1 /\ *)
   (*         ~~ is_deftyp (type_of_cmpnttyp (fst (CE.vtyp (base_ref r) (inferWidth_fun sts ce1)))) *)
   (*         )-> *)
   (*         (* ~~ is_deftyp (type_of_cmpnttyp (fst (CE.vtyp v (inferWidth_fun sts ce1)))) /\ *) *)
   (*         (*ce2 = wmap_map2_cenv wm1 ce1 /\*) *)
   (*         inferType_stmts sts ce0 ce1 -> *)
   (*     inferWidth_stmts_sem sts ce1 (inferWidth_fun sts ce1). *)
   (* Proof. *)
   (*   have Hnone : (add_width_2_cenv None None = None) by done. *)
   (*   elim => [ce0 ce1  v He Hiw | st ss Hm ce0 ce1 v He Hiw]. *)
   (*   - *)
   (*     apply inferWidth_stmts_nil. rewrite /inferWidth_fun/wmap_map2_cenv/=. intro. *)
   (*     rewrite (CELemmas.map2_1bis _ _ _ Hnone). rewrite CELemmas.empty_o//. *)
   (*   - *)
   (*     case He => [wm0 [wm1 Hec]]. *)
   (*     apply inferWidth_stmts_imp with (wmap_map2_cenv wm1 ce1). *)
   (*     move : Hec Hiw. *)

       (* elim st. *)
       (* + (*skip*) *)
       (*   intros.  *)
       (*   apply inferWidth_sskip_sem_conform; try done. *)
       (*   erewrite (find_same_ce_wmap2ce _ (Hce12 _)). done. *)
       (* + (*swire*) *)

       (*   move => s f Hit Hits. move => [Hin | Hin]; try rewrite //. *)
       (*   move : (init_new_comp_name Hin s) => Hns. *)
       (*   move : (new_v_wmap_none Hns empty_wmap0) => Hnv. *)
       (*   apply inferWidth_swire_sem_conform'; try done.  *)
       (*   move : (inferType_stmts_hd Hit) => Hhd. inversion Hhd; subst. *)
       (*   rewrite -H5 (Hce12 s)//. *)
       (*   erewrite (find_same_ce_wmap2ce _ (Hce12 _)). done. *)
       (*   (* intros. *) *)
       (*   (* exists wm0; exists wm1. *) *)
       (*   (* move : (Hec (Eid s) (aggr_typ f, Wire) (* (Swire s f) *)) => [Hbrs1 [Hbrt [[Hdt [Hndt [Hun Hit]]]]]]. *) *)
       (*   (* rewrite /= in Hbrt. *) *)
       (*   (* move : (new_v_wmap_none Hbrs1 wm0) => Hnv. *) *)
       (*   (* apply inferWidth_swire_sem_conform with ce0; try done. *) *)
       (*   (* exact : (inferType_stmts_hd Hiw). *) *)
       (* + (*reg*) *)
       (*   intros. *)
       (*   apply inferWidth_sreg_sem_conform'; try done. *)
       (*   move : (inferType_stmts_hd Hif) => Hhd. inversion Hhd; subst. *)
       (*   rewrite -H6 (Hce12 s)//. *)
       (*   erewrite (find_same_ce_wmap2ce _ (Hce12 _)). done. *)
       (* + (*mem*) *)
       (*   intros. *)
       (*   apply inferWidth_smem_sem_conform'; try done. *)
       (*   move : (inferType_stmts_hd Hif) => Hhd. inversion Hhd; subst. *)
       (*   rewrite -H6 (Hce12 s)//. *)
       (*   erewrite (find_same_ce_wmap2ce _ (Hce12 _)). done. *)
       (* + (*inst*) *)
       (*   intros. *)
       (*   apply inferWidth_sinst_sem_conform' with (fst (CE.vtyp s0 ce0)); try done. *)
       (*   move : (inferType_stmts_hd Hif) => Hhd. inversion Hhd; subst. *)
       (*   rewrite -H7 (Hce12 s)//. *)
       (*   erewrite (find_same_ce_wmap2ce _ (Hce12 _)). done. *)
       (* + (*node*) *)
       (*   intros. *)
       (*   apply inferWidth_snode_sem_conform'; try done. *)
       (*   move : (inferType_stmts_hd Hif) => Hhd. inversion Hhd; subst. *)
       (*   rewrite -(typeof_same_ce h (Hce12 s)) -H3 -H7//. *)
       (*   rewrite/=(typeof_same_ce h (Hce12 s)). *)
       (*   case (is_deftyp (type_of_hfexpr h ce2)); try done. *)
       (*   erewrite (find_same_ce_wmap2ce _ (Hce12 _)). done. *)
       (* + (*fcnct*) *)
       (*   intros. *)
       (*   move : Hin => [Hin|Hin]; try done. *)
       (*   move : (inferType_stmts_hd Hif) => Hitc.  *)
       (*   inversion Hitc; subst. *)
       (*   move : H5 => [Hit1 [Hit2 Hit3]]. *)
       (*   move : (not_init_wmfind_some Hin (base_ref h) empty_wmap0 (type_of_cmpnttyp t)) => Haux. *)
       (*   case Hde : (is_deftyp (type_of_cmpnttyp t)). *)
       (*   apply inferWidth_sfcnct_ftype_sem_conform with c t (type_of_cmpnttyp t) t'; try done. *)
       (*   rewrite -(Hce12 (base_ref h))//. *)
       (*   erewrite <-(typeofr_same_ce _ (Hce12 _)). *)
       (*   rewrite (type_of_hexpr_cefind Hit1)//. *)
       (*   erewrite <-(typeof_same_ce _ (Hce12 _)). done. *)
       (*   rewrite /=. erewrite <-(typeofr_same_ce _ (Hce12 _)). *)
       (*   erewrite <-(typeof_same_ce _ (Hce12 _)). *)
       (*   case (is_deftyp (type_of_ref h ce1)); try done. *)
       (*   rewrite (add_wmap_same_ce _ empty_wmap0 (Hce12 _)). *)
       (*   case h0; try done. *)
       (*   intros. erewrite <-(typeofr_same_ce _ (Hce12 _)). *)
       (*   rewrite (add_wmap_same_ce _ empty_wmap0 (Hce12 _))//. *)
       (*   erewrite (find_same_ce_wmap2ce _ (Hce12 _)). done. *)
       (*   move : (infer_type_no_unknown_type Hif) => Hfu. *)
       (*   rewrite /find_unknown. move : (Hfu (base_ref h) c ). *)
       (*   rewrite -(Hce12 (base_ref h)). *)
       (*   rewrite Hit1. case t; try done. *)
       (*   apply inferWidth_sfcnct_tmp with (type_of_cmpnttyp t). *)
       (*   have Hit1' : CE.find (base_ref h) ce2 = Some (t, c) by rewrite -(Hce12 (base_ref h))//. *)
       (*   rewrite (type_of_hexpr_cefind Hit1')//. *)
       (*   rewrite /=(type_of_hexpr_cefind Hit1)/= Hde; case h0; done. *)
       (*   rewrite -(Hce12 (base_ref h))/=(type_of_hexpr_cefind Hit1)/= Hde; case h0; intros; move : Hde; *)
       (*     rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone) Haux Hit1; *)
       (*     case t; rewrite /=; intros; try (rewrite Hde//|| discriminate). *)
       (*   rewrite Hde//.          *)
       (* + (*pcnct*) *)
       (*            intros. *)
       (*   move : Hin => [Hin|Hin]; try done. *)
       (*   move : (inferType_stmts_hd Hif) => Hitc.  *)
       (*   inversion Hitc; subst. *)
       (*   move : H5 => [Hit1 [Hit2 Hit3]]. *)
       (*   move : (not_init_wmfind_some Hin (base_ref h) empty_wmap0 (type_of_cmpnttyp t)) => Haux. *)
       (*   case Hde : (is_deftyp (type_of_cmpnttyp t)). *)
       (*   apply inferWidth_spcnct_ftype_sem_conform with c t (type_of_cmpnttyp t) t'; try done. *)
       (*   rewrite -(Hce12 (base_ref h))//. *)
       (*   erewrite <-(typeofr_same_ce _ (Hce12 _)). *)
       (*   rewrite (type_of_hexpr_cefind Hit1)//. *)
       (*   erewrite <-(typeof_same_ce _ (Hce12 _)). done. *)
       (*   rewrite /=. erewrite <-(typeofr_same_ce _ (Hce12 _)). *)
       (*   erewrite <-(typeof_same_ce _ (Hce12 _)). *)
       (*   case (is_deftyp (type_of_ref h ce1)); try done. *)
       (*   rewrite (add_wmap_same_ce _ empty_wmap0 (Hce12 _)). *)
       (*   case h0; try done. *)
       (*   intros. erewrite <-(typeofr_same_ce _ (Hce12 _)). *)
       (*   rewrite (add_wmap_same_ce _ empty_wmap0 (Hce12 _))//. *)
       (*   erewrite (find_same_ce_wmap2ce _ (Hce12 _)). done. *)
       (*   move : (infer_type_no_unknown_type Hif) => Hfu. *)
       (*   rewrite /find_unknown. move : (Hfu (base_ref h) c ). *)
       (*   rewrite -(Hce12 (base_ref h)). *)
       (*   rewrite Hit1. case t; try done. *)
       (*   apply inferWidth_spcnct_tmp with (type_of_cmpnttyp t). *)
       (*   have Hit1' : CE.find (base_ref h) ce2 = Some (t, c) by rewrite -(Hce12 (base_ref h))//. *)
       (*   rewrite (type_of_hexpr_cefind Hit1')//. *)
       (*   rewrite /=(type_of_hexpr_cefind Hit1)/= Hde; case h0; done. *)
       (*   rewrite -(Hce12 (base_ref h))/=(type_of_hexpr_cefind Hit1)/= Hde; case h0; intros; move : Hde; *)
       (*     rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone) Haux Hit1; *)
       (*     case t; rewrite /=; intros; try (rewrite Hde//|| discriminate). *)
       (*   rewrite Hde//.    *)
       (* + (*invalid*) *)
       (*   intros. *)
       (*   apply inferWidth_sinvalid_sem_conform; try done. *)
       (*   erewrite (find_same_ce_wmap2ce _ (Hce12 _)). done. *)
       (* + (*when*) *)
       (*   intros. *)
       (*   apply inferWidth_swhen_sem_conform_tmp; try done. *)
       (*   erewrite (find_same_ce_wmap2ce _ (Hce12 _)). done. *)
       (* + (*stop*) *)
       (*   intros. *)
       (*   apply inferWidth_sstop_sem_conform; try done. *)
       (*   erewrite (find_same_ce_wmap2ce _ (Hce12 _)). done. *)
     (* -  rewrite -/(inferWidth_fun _). *)
   (* Admitted. *)
*)