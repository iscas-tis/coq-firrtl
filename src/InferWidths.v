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

(* not last connection yet, so that one varaible map to a stmt set. 
   one element is explored, once all the elements in its stmt set are explored. *)

Fixpoint expr2varlist (expr : HiFP.hfexpr) (tmap : ft_pmap) (ls : seq ProdVarOrder.t) : option (seq ProdVarOrder.t) := 
  match expr with
  | Econst _ _ => Some ls
  | Eref ref => match ref2pvar ref tmap with
                | Some pv => Some (List.cons pv ls)
                | None => None
                end
  | Eprim_unop _ e1 => expr2varlist e1 tmap ls
  | Eprim_binop _ e1 e2 => match expr2varlist e1 tmap ls, expr2varlist e2 tmap ls with
                          | Some ls', Some ls'' => Some (ls' ++ ls'')
                          | _,_ => None
                          end
  | Emux e1 e2 e3 => match expr2varlist e1 tmap ls, expr2varlist e2 tmap ls, expr2varlist e3 tmap ls with
                    | Some ls', Some ls'', Some ls''' => Some (ls' ++ ls'' ++ ls''')
                    | _,_,_ => None
                    end
  | Evalidif e1 e2 => match expr2varlist e1 tmap ls, expr2varlist e2 tmap ls with
                      | Some ls', Some ls'' => Some (ls' ++ ls'')
                      | _,_ => None
                      end
  | Ecast _ e => expr2varlist e tmap ls
  end.
  
Fixpoint infer_implicit (ft_ref : ftype) (ft_expr : ftype_explicit) : option ftype :=
  match ft_ref, ft_expr with
  | Gtyp (Fuint _), exist (Gtyp (Fuint _)) _
  | Gtyp (Fsint _), exist (Gtyp (Fsint _)) _
  | Gtyp Fclock, exist (Gtyp Fclock) _
  | Gtyp Freset, exist (Gtyp Freset) _
  | Gtyp Fasyncreset, exist (Gtyp Fasyncreset) _ => Some ft_ref (* if it's not an implicit type, don't change that. *)
  | Gtyp (Fuint_implicit w_ref), exist (Gtyp (Fuint w_expr)) _ => Some (Gtyp (Fuint_implicit (max w_ref w_expr)))
  | Gtyp (Fsint_implicit w_ref), exist (Gtyp (Fsint w_expr)) _ => Some (Gtyp (Fsint_implicit (max w_ref w_expr)))
  | Atyp t_ref n_ref, exist (Atyp t_expr n_expr) p => match (n_expr == n_ref), infer_implicit t_ref (exist ftype_not_implicit_width t_expr p) with
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
   end.

Fixpoint InferWidth_ff (v : N) (ff : ffield) (num : N) (newt : ftype_explicit) : option ffield :=
  match ff with
  | Fflips v0 Nflip ft ff' => if v == (N.add num 1%num) (* 找到被更新的标号, 所对应的field *)
                              then (* 比较Btyp现有对应位置上的ftype和待更新的newt是否match, 取较大的更新Btyp *)
                                match infer_implicit ft newt with 
                                | Some newt' => Some (Fflips v0 Nflip newt' ff') (* 修改当前field的type, ff'不变 *)
                                | None => None
                                end
                              else if v > (N.add (N.add num (N.of_nat (size_of_ftype ft))) 1%num) (* 不在该field中, 找下一个field *)
                                   then match InferWidth_ff v ff' (N.add (N.add num (N.of_nat (size_of_ftype ft))) 1%num) newt with
                                      | Some newf => Some (Fflips v0 Nflip ft newf)
                                      | None => None
                                      end
                                   else (* 在field v0中 *)
                                   match ft with
                                   | Gtyp _ => None (* gtyp case 应该满足 v == (N.add num 1%num) 不进入else *)
                                   | Atyp atyp anum => match infer_implicit atyp newt with 
                                                | Some newt' => Some (Fflips v0 Nflip (Atyp newt' anum) ff')
                                                | None => None
                                                end
                                   | Btyp bff => match InferWidth_ff v bff (N.add num 1%num) newt with
                                                | Some nf => Some (Fflips v0 Nflip (Btyp nf) ff')
                                                | None => None
                                                end
                                   end
  | _ => None
  end.

Fixpoint InferWidth_fun (v : ProdVarOrder.t) (el : seq HiFP.hfexpr) (tmap : ft_pmap) : option ft_pmap := 
  match el with
  | nil => Some tmap
  | e :: etl => match type_of_e e tmap, ft_find v tmap with
                (* 当v在tmap中有已存v, 是直接被声明的变量 *)
                | Some newt, Some ft => match infer_implicit ft newt with
                                        | Some nt => InferWidth_fun v etl (ft_add v nt tmap)
                                        | None => None (* type不match，没有新的正确tmap *)
                                        end
                (* tmap 中没有v, 可能是subindex或subfield或node *)
                | Some newt, None => if (snd v) == N0 (* node *)
                                     then InferWidth_fun v etl (ft_add v (explicit_to_ftype newt) tmap)
                                    else match ft_find (fst v, N0) tmap with
                                    | Some (Atyp t_ref n_ref) => (* 比较t_ref与newt是否match, 取较大的更新Atyp *)
                                                               match infer_implicit t_ref newt with
                                                               | Some newt' => InferWidth_fun v etl (ft_add (fst v, N0) (Atyp newt' n_ref) tmap)
                                                               | None => None
                                                               end
                                    | Some (Btyp ff_ref) => match InferWidth_ff (snd v) ff_ref N0 newt with
                                                        | Some newf => InferWidth_fun v etl (ft_add (fst v, N0) (Btyp newf) tmap)
                                                        | None => None
                                                        end
                                    | _ => None (* 若(fst v, N0)是Gtyp或None, v有错误 *)
                                    end
                | _, _ => None
                end
  end.

Fixpoint InferWidths_fun (od : seq ProdVarOrder.t) (var2exprs : var2exprsmap) (tmap : ft_pmap) : option ft_pmap := 
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

Fixpoint drawel (v : ProdVarOrder.t) (el : seq HiFP.hfexpr) (tmap : ft_pmap) (newg : ProdVarOrder.t -> seq ProdVarOrder.t) (vertices : seq ProdVarOrder.t) : option ((ProdVarOrder.t -> seq ProdVarOrder.t) * (seq ProdVarOrder.t)) :=
  (* recursively draw dependencies in el for element v *)
  match el with
  | nil => Some (newg, vertices)
  | e :: etl => let vl := expr2varlist e tmap nil in
                match vl with (* all elements appears in e *)
                | Some ls => let g' := List.fold_left (fun tempg tempv => updg tempv (cons v (tempg tempv)) tempg) ls newg in
                             drawel v etl tmap g' (vertices ++ ls)
                | None => None
                end
  end.

Fixpoint drawg depandencyls (tmap : ft_pmap) (expli_reg : seq ProdVarOrder.t) (newg : ProdVarOrder.t -> seq ProdVarOrder.t) (vertices : seq ProdVarOrder.t) : option ((ProdVarOrder.t -> seq ProdVarOrder.t) * (seq ProdVarOrder.t)) :=
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

Theorem InferWidths_correct :
(* Proves that InferWidth_fun preserves the semantics *)
   forall (F : HiFP.hfmodule) (vm' : module_graph_vertex_set_p.env) (ct : module_graph_connection_trees_p.env),
      match InferWidths_m F with
      | Some F' => Sem F' vm' ct -> Sem F (make_vm_implicit F vm') ct
      
      (*exists vm : module_graph_vertex_set_p.env, (* make_vm_implicit vm' F : 找所有implicit declaration, 改 vertex_type *)
                                       Sem F vm ct /\ module_graph_vertex_set_p.Equal vm' (make_vm_explicit vm) *)
      | _ => True
      end.
Proof.
  (* KY previous version *)
  intro F. 
  case H : (InferWidths_m F) => [F'|]; try done.
  move => vm ct.
  rewrite /Sem.
  case Hm : F => [v pp ss|v' pp' ss'].
  (* Inmod case *)

  rewrite Hm in H. 
  rewrite /InferWidths_m in H.
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
  clear H. 

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