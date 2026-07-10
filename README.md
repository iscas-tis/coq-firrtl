# Artifact for *Fixed-Point Semantics and Verified Lowering Transformations for FIRRTL*

This artifact contains the implementation and formalization accompanying the paper **Fixed-Point Semantics and Verified Lowering Transformations for FIRRTL**. It includes:

- A Coq formalization of **the first fixed-point formal semantics for FIRRTL**.
- Coq formalizations for two representative lowering transformations, **lowerTypes** and **expandWhens**, and proofs that both preserve the semantics.
- Parser and LoFIRRTL emitter for the extracted OCaml implementations of **the two verified transformations**.

## Abstract
FIRRTL is an intermediate representation for the Chisel hardware description language that has been widely adopted in hardware designs. It provides high-level, domain-specific constructs that facilitate the synthesis of Chisel design, during which these constructs must be eliminated through a sequence of lowering transformations before reaching Low FIRRTL (LoFIRRTL), a representation close to Verilog. The complexity of these lowering transformations makes semantic preservation nontrivial: among 659 reported issues in the FIRRTL repository, 104 concern bugs in compiler behavior. This paper presents the first mechanized semantic framework for FIRRTL. At its core is a reusable %part of the framework is a fixed-point semantics that provides an interpretation of FIRRTL programs. We instantiate this semantic framework on two representative lowering transformations, i.e., lowerTypes and expandWhens, and specify their functional correctness with respect to this semantics. Building on these specifications, we mechanically prove in Rocq %proof assistant that both transformations preserve the semantics of well-formed FIRRTL programs at their intended pipeline stages. We also extract an OCaml implementation of these verified lowering transformations from the Rocq implementation and validate their behavior against the official C++ FIRRTL compiler on a benchmark suite of 130 FIRRTL programs.

> **📌 For a Quick Start**: 
> Please refer to **[`REQUIREMENTS.md`](REQUIREMENTS.md)** for the exact dependency versions, hardware specs, and the one-command smoke test (`./build_and_run.sh`). 
> This `README.md` focuses on **code navigation, paper-to-proof mapping, and advanced usage**.

## 🚀 Getting Started 

### 1. Set up the environment
Follow the **Step-by-Step Build Instructions** in [`REQUIREMENTS.md`](REQUIREMENTS.md) to install the exact versions of Coq 8.16.0, OCaml 4.14.2, MathComp 1.15.0, and Dune 3.16.0 via OPAM.

### 2. Run the automated smoke test
From the root directory of this repository:
```bash
./build_and_run.sh
```
This script automatically compiles the Coq proofs, extracts the OCaml code, builds the executable, and runs it on a small example (`FormalSimple.fir`).

**Expected quick output**: You should see `✅ Coq formalization compiled successfully` ... `🎉 Smoke test completed successfully!` and a generated `FormalSimple.lo.fir` file in `src/ocaml/demo/chiselbook/`. This is the new firrtl circuit obtained through our verified transformations. The output file can be processed by downstream tools like `firtool`.

*(For the full expected log, see `REQUIREMENTS.md`)*

### 3. (Optional) Run on other benchmarks
After the build, you can test any other `.fir` file in `src/ocaml/demo/`:
```bash
cd src/ocaml_try
./_build/default/generate_lofir.exe ../ocaml/demo/your_target.fir
```

## Artifact Structure & Code Guide

```
.
├── lib/                              # Reusable math lemmas (nbits, ssrlib)
├── src/
│   ├── HiFirrtl.v                    # Syntax definition of HiFirrtl
│   ├── Firrtl.v                      # Syntax definition of LoFirrtl
│   ├── Semantics.v                   # Fixed-point semantics framework
│   ├── LowerTypes.v                  # Formalization of lowerTypes transformation
│   ├── LowerTypes_proof.v            # Verification of lowerTypes transformation
│   ├── ExpandWhens.v                 # Formalization of expandWhens transformation
│   ├── ExpandWhens_proof.v           # Verification of expandWhens transformation
│   ├── ocaml/                        # Extracted OCaml implementation & Benchmarks
│   │   ├── hiparser/                 # FIRRTL Parser and LoFIRRTL emitter
│   │   ├── demo/                     # 130 benchmark FIRRTL programs
│   │   ├── generate_lofir.ml         # Verified compiler executable
│   │   └── ...
│   └── ...
├── build_and_run.sh                  # Automation script
└── ...
```

### Key Files and Their Correspondence to the Paper

#### 📄 `HiFirrtl.v`
Defines the abstract syntax of the source language (HiFirrtl).

| Definition | Paper Reference |
| :--- | :--- |
| `size_of_ftype` | Section 4.1, `sizeOfFtype` |

---

#### 📄 `Semantics.v`
Formalizes the **fixed-point semantics** and provides shared definitions used across both transformations.

| Definition / Lemma | Paper Reference | Description |
| :--- | :--- | :--- |
| `eval_hfstmt` | Section 3.2.1 | Defines `value_iter` (the semantic evaluator) |
| `iterate` | Section 3.2.3 | Implements the iteration of the semantic functor |
| `list_expr`, `list_ref` | Section 4.1 | Defines `listGExp` and `listGTypeRef` (used in type inference) |

---

#### 📄 `LowerTypes.v`
Formalizes the **lowerTypes** transformation (Section 4.1 of the paper).

| Definition | Paper Reference | Description |
| :--- | :--- | :--- |
| `type_of_ref` | Section 4.1 | Defines `typeOfRef` |
| `type_of_hfexpr` | Section 4.1 | Defines `typeOfExp` |
| `expand_port` | Section 4.1 | Lowering function for a port |
| `expand_wire`, `expand_reg`, `expand_node` | Section 4.1 | Lowering functions for wires, registers, and nodes |
| `expand_invalid` | Section 4.1 | Lowering function for an invalidation |
| `expand_fcnct` | Section 4.1 | Lowering function for a connection |
| `lowertypes_stmts` | Section 4.1 | Lowering function for a statement sequence |
| `lowertypes` | Section 4.1 | Top-level definition of the `lowerTypes` transformation |

---

#### 📄 `LowerTypes_proof.v`
**Verifies** the correctness of the **lowerTypes** transformation (Sections 4.2 and 4.3).

| Lemma / Theorem | Paper Reference | Description |
| :--- | :--- | :--- |
| `eval_expand_inv` | Lemma 4.7 | Invalidation case of **Statement Expansion** |
| `eval_expand_wire` | Lemma 4.7 | Wire declaration case of **Statement Expansion** |
| `eval_expand_reg` | Lemma 4.7 | Register declaration case of **Statement Expansion** |
| `eval_expand_node` | Lemma 4.7 | Node case of **Statement Expansion** |
| `eval_expand_fcnct` | Lemma 4.7 | Connection case of **Statement Expansion** |
| `eval_expand_stmt` | Lemma 4.7 | **Statement Expansion** |
| `Sem_preservation_lowerTypes` | Theorem 4.9 | **Correctness of LowerTypes** |

---

#### 📄 `ExpandWhens.v`
Formalizes the **expandWhens** transformation (Section 5.1 of the paper).

| Definition | Paper Reference | Description |
| :--- | :--- | :--- |
| `def_expr` | Section 5.1 | Defines the **connection status** |
| `connectConnect_fun` | Section 5.1 | Defines `collectConnects` |
| `combine_branches` | Section 5.1 | Defines `combineBranches` |
| `convert_to_connect_stmts` | Section 5.1 | Defines `connStmts` |
| `expandWhens` | Section 5.1 | Top-level definition of the `expandWhens` transformation |

---

#### 📄 `ExpandWhens_proof.v`
**Verifies** the correctness of the **expandWhens** transformation (Sections 5.2 and 5.3).

| Lemma / Theorem | Paper Reference | Description |
| :--- | :--- | :--- |
| `ExpandWhens_fun_tmap_eq` | Lemma 5.1 | **Kind/Type Preservation** |
| `find_node_qin_with_cond`, `eval_hfstmts_for_unique_node` | Lemma 5.3 | **Node Evaluation** correctness |
| `eval_hfstmts_ExpandBranches_funs_find_for_comb` | Lemma 5.4 | **Soundness of `collectConnects`** |
| `eval_hfstmts_convert_to_connect_stmts_for_comb` | Lemma 5.5 | **Soundness of `connStmts`** |
| `func_type_included_eval_hfstmts` | Lemma 5.6 | **Single-step Simulation**  |
| `Sem_preservation_expandWhens` | Theorem 5.8 | **Correctness of ExpandWhens** |

---

## 🛠️ Troubleshooting

**Common Issues:**
- **Permission denied**: Try `chmod -R 777 your/file`
- **Coq compilation errors**: Check Coq version is exactly 8.16.0