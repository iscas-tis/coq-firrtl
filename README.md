# Artifact for *Fixed-Point Semantics and Verified Lowering Transformations for FIRRTL*

This artifact contains the implementation and formalization accompanying the paper **Fixed-Point Semantics and Verified Lowering Transformations for FIRRTL**. It includes:

- A Coq formalization of **the first fixed-point formal semantics for FIRRTL**.
- Coq formalizations for two representative lowering transformations, **lowerTypes** and **expandWhens**, and proofs that both preserve the semantics.
- Parser and LoFIRRTL emitter for the extracted OCaml implementations of **the two verified transformations**.

## Abstract
FIRRTL is an intermediate representation for the Chisel hardware description language that has been widely adopted in hardware designs. It provides high-level, domain-specific constructs that facilitate the synthesis of Chisel design, during which these constructs must be eliminated through a sequence of lowering transformations before reaching Low FIRRTL (LoFIRRTL), a representation close to Verilog. The complexity of these lowering transformations makes semantic preservation nontrivial: among 659 reported issues in the FIRRTL repository, 104 concern bugs in compiler behavior. This paper presents the first mechanized semantic framework for FIRRTL. At its core is a reusable %part of the framework is a fixed-point semantics that provides an interpretation of FIRRTL programs. We instantiate this semantic framework on two representative lowering transformations, i.e., lowerTypes and expandWhens, and specify their functional correctness with respect to this semantics. Building on these specifications, we mechanically prove in Rocq %proof assistant that both transformations preserve the semantics of well-formed FIRRTL programs at their intended pipeline stages. We also extract an OCaml implementation of these verified lowering transformations from the Rocq implementation and validate their behavior against the official C++ FIRRTL compiler on a benchmark suite of 130 FIRRTL programs.

## 🚀 Getting Started Guide

### Prerequisites

- macOS 12+ or Linux (Ubuntu 22.04+/Debian 11+)
* [OPAM](https://opam.ocaml.org) 2.1+
* [Coq](https://coq.inria.fr) 8.16.0 
* [MathComp](https://github.com/math-comp/math-comp) 1.15.0
* [Ocaml](https://ocaml.org) 4.14.2
* [dune](https://github.com/ocaml/dune) 3.16.0
* [Git LFS](https://git-lfs.com) >= 3.0 (required for large benchmark files)

### Installation & Smoke Test

```bash
# 1. Install dependencies (see REQUIREMENTS.txt for detailed versions)
opam pin add coq 8.16.0
opam pin add ocaml 4.14.2
opam install -y \
    coq-mathcomp-algebra=1.15.0 \
    coq-mathcomp-fingroup=1.15.0 \
    coq-mathcomp-ssreflect=1.15.0

# 2. Install Git LFS (if not already installed)  

Choose the command that matches your operating system:

| OS | Command |
|----|---------|
| **macOS** | `brew install git-lfs` |
| **Ubuntu / Debian** | `sudo apt-get install git-lfs` |
| **CentOS / RHEL** | `sudo yum install git-lfs` |
| **Windows** | Download and run the installer from [git-lfs.com](https://git-lfs.com), or use Git for Windows (which includes LFS). |

# 3. fetch LFS files (benchmark data)
git lfs install
git lfs pull

# 4. Run the smoke test
./build_and_run.sh
```

#### Expected Smoke Test Output
```bash
✅ Coq formalization compiled successfully
✅ OCaml implementation built
🚀 Running demo on sample circuit...
after lowerTypes :
circuit 0 : 
  module 0 : 
    input _0_0 : Clock
    input _1_0 : UInt<1>
    input _2_0 : UInt<10>
    input _2_1 : UInt<10>
    output _2_2 : UInt<10>
    node _3_0 = and(_2_0, _2_1)
    _2_2 <= _3_0
lowerTypes time : 0.000005s

after expandWhens :
circuit 0 : 
  module 0 : 
    input _0_0 : Clock
    input _1_0 : UInt<1>
    input _2_0 : UInt<10>
    input _2_1 : UInt<10>
    output _2_2 : UInt<10>
    node _3_0 = and(_2_0, _2_1)
    _2_2 <= _3_0
expandWhens time : 0.000018s
total time : 0.000031s

FIRRTL version 2.0.0
circuit FormalSimple : 
  module FormalSimple : 
    input clock : Clock
    input reset1 : UInt<1>
    input io_a : UInt<10>
    input io_b : UInt<10>
    output io_y : UInt<10>
    node _io_y_T = and(io_a, io_b)
    io_y <= _io_y_T
../ocaml/demo/chiselbook/FormalSimple.lo.fir is generated
🎉 Smoke test completed successfully!
```

### Note
We are using the simple FIRRTL program `FormalSimple.fir` in `ocaml/demo/chiselbook`, in fact, the benchmarks mentioned in the article are all included in `ocaml/demo/`. You can replace the test file path in `build_and_run.sh` with any of the test cases provided by us, for example:
```bash
./_build/default/run_solver.exe ../ocaml/demo/chiselbook/Arbiter3.fir
```
Further more, if you run the test locally, you will find a new firrtl file named `FormalSimple.lo.fir` in the same directory as `FormalSimple.fir`. This is the new firrtl circuit obtained through our verified transformations. The output file can be processed by downstream tools like `firtool`.

## Artifact Structure & Code Guide

```
.
├── lib                              # Lemmas to be used
│   ├── nbits
│   └── simplssrlib
├── src
│   ├── HiFirrtl.v                   # Syntax of HiFirrtl
│   ├── Firrtl.v                     # Syntax of LoFirrtl
│   ├── ExpandConnects_inst.v        # Formalization of lowerTypes
│   ├── ExpandWhens_inst.v           # Formalization of expandWhens
│   ├── Semantics.v                  # Formalization of Semantics and Verification of lowerTypes and expandWhens
│   ├── ocaml/
│   │   ├── hiparser/                # A HiFirrtl parser
│   │   ├── demo/                    # Benchmarks
│   │   ├── generate_lofir.ml        # Experimental Ocaml compiler
│   │   └── ...
│   ├── build_and_run.sh             # Script to run the Ocaml compiler
│   ├── ...
```

**Key Files:**
- `ExpandConnects_inst.v` : Formalizes lowerTypes.
Definition `solve_ubs_aux` : Section 3.2, `Proposition 3`.

- `branch_and_bound.v`: Contains `Proposition 2` proof, Formalizes the `BaB` algorithm and its correctness proof.
Theorem `smaller_sol_is_sol` : Section 2.2 , `Proposition 2`.
Function `bab_bin` : Section 3.3, Section 4.1(`BaB`).
Theorem `bab_bin_correct1`, Theorem `bab_bin_correct2` : Section 4.2(`P_BaB`).

- `floyd_sc.v` : Formalizes the `maximum Floys-Warshall` algorithm and its correctness proof.
Function `solve_simple_cycle` : Section 3.4, Section 4.1(`inferSCC: nontrivial-maxfw`).
Lemma `scc_smallest`, Lemma `solve_simple_cycle_correctness` : Section 4.2(`P_maxFW`).

- `inferWidths.v` : Formalizes the complete width inference procedure and its correctness proof.
Definition `solve_scc` : Section 4.1(`inferSCC`)
Fixpoint `solve_alg` : Section 4.1(`inferWidth`)
Lemma `solve_scc_correctness`, Lemma `solve_scc_smallest`, Lemma `solve_scc_unsat` : Section 4.2(`P_inferSCC`)
Lemma `solve_alg_correctness`, Lemma `solve_alg_smallest`, Lemma `solve_alg_return_unsat` : Section 4.2(`P_inferWidth`)

## 🛠️ Troubleshooting

**Common Issues:**
- **Network problem during building docker**: Try `docker pull ocaml/opam:debian-11-ocaml-4.14` before build.
- **Permission denied**: Try `chmod -R 777 your/file`
- **Coq compilation errors**: Check Coq version is exactly 8.16.0