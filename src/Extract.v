From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
From Coq Require Import ExtrOcamlIntConv ExtrOcamlNatInt ExtrOcamlZInt.
From Coq Require Import Arith List.
From mathcomp Require Import tuple.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env Firrtl HiEnv HiFirrtl.
From firrtl Require Import ModuleGraph_simplified InferWidth_rewritten ExpandWhens ExpandConnects_new.

Extraction Language OCaml.

(* Avoid name clashes *)
Extraction Blacklist Nat Int List String.

Cd "src/ocaml/extraction".
Separate Extraction
         seq.catrev nat_of_int n_of_int int_of_nat int_of_n int_of_z
         NBitsDef.from_string NBitsDef.from_hex NBitsDef.from_bin NBitsDef.b1
         NBitsDef.to_hex NBitsDef.to_nat NBitsDef.to_bin (*Datatypes.xorb
         NBitsDef.invB NBitsDef.zext seq.seq_eqType seq.unzip1*)
         (*LoFirrtl.run_module0 LoFirrtl.run_module
         LoFirrtl.no_mem_run_module_inline LoFirrtl.no_mem_run_module0_inline
         LoFirrtl.no_mem_run_module*) LoFirrtl.no_mem_run_module0
         (*LoFirrtl.testnat LoFirrtl.testN*)
         Env.sizeof_fgtyp
         HiFirrtl.hfcircuit ModuleGraph_simplified.type_of_expr
         InferWidth_rewritten.InferWidths_m
         ExpandConnects_new.expandconnects_fmodule ExpandConnects_new.rcd_pmap_from_m ExpandConnects_new.output_ft_pmap
         ExpandWhens.ExpandWhens_fun
         .
Cd "../../..".
