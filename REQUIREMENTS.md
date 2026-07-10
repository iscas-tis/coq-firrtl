# REQUIREMENTS for [Fixed-Point Semantics and Verified Lowering Transformations for FIRRTL] Artifact

This document specifies the exact hardware and software prerequisites, as well as the **strict step-by-step commands** to build and validate the artifact natively.

## 1. Hardware Requirements
- **Minimum RAM**: 8 GB
- **Disk Space**: **5 GB** free space (required for Coq build intermediates, `opam` switch, and the large FIRRTL benchmark files)

## 2. Base System Requirements
- **Linux**: Ubuntu 22.04 LTS (or Debian 11/12)
- **macOS**: Monterey (12) or later (Intel/Apple Silicon)

**Required system tools** (install via `apt` or `brew` before proceeding):
- `git`
- `make`, `gcc`, `g++` (build essentials)
- `opam` (OCaml Package Manager) **version 2.1.0 or higher**

## 3. Setting Up the Exact OCaml/Coq Environment 

**Note**: We strongly recommend you using a clean terminal to create a switch that is isolated from your system's default OCaml.

```bash
# 1. Initialize opam if not already done
opam init --disable-sandboxing
eval $(opam env)

# 2. Create a dedicated switch with the exact OCaml version
opam switch create coq-firrtl-artifact ocaml-base-compiler.4.14.2
eval $(opam env)

# 3. Add the official Coq opam repository
opam repo add coq-released https://coq.inria.fr/opam/released

# 4. Install the pinned dependencies (exact versions)
opam pin add coq 8.16.0
opam pin add ocaml 4.14.2
opam install -y \
    coq-mathcomp-algebra=1.15.0 \
    coq-mathcomp-fingroup=1.15.0 \
    coq-mathcomp-ssreflect=1.15.0
```

## 4. Fetching Large Files (Optional, only for the XiangShan benchmark)

Our repository contains multiple small/medium `.fir` benchmark files directly under `src/ocaml/demo/`. You can **skip this entire section** and still successfully build the project on the smaller examples.

The only file that exceeds GitHub's 100 MB limit is the large **"XiangShan"** benchmark (200+ MB), which is stored via Git LFS. 
**Only follow the commands below if you intend to run the XiangShan compilation test.**

```bash
# 1. Ensure Git LFS is installed on your system
# (macOS: brew install git-lfs / Ubuntu: sudo apt install git-lfs)

# 2. Initialize LFS (only needed if you haven't used it before)
git lfs install

# 3. Fetch the specific large benchmark files
git lfs pull
```

## 5. Building the Project and Running the Smoke Test (Native)

We provide a **one-command smoke test** script (`build_and_run.sh`) that fully automates:
- Coq project compilation
- OCaml code extraction
- Dune project initialization and build
- Running the verified transformations on a small sample circuit (`FormalSimple.fir`)

Make the script executable if needed:
```bash
chmod +x build_and_run.sh
```

From the root directory of the repository, execute:

```bash
# Run the fully automated smoke test
./build_and_run.sh
```

**What this script does internally** (for your reference):
1. Generates the Coq `Makefile` via `coq_makefile`.
2. Compiles the entire Coq formalization (`make`).
3. Initializes a fresh Dune project under `src/`.
4. Copies all necessary OCaml extraction files and parser modules.
5. Builds the OCaml executable with `dune build`.
6. Runs the executable on `src/ocaml/demo/chiselbook/FormalSimple.fir`.

## 6. Expected Output of the Smoke Test

If successful, the terminal will output :

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

Also, a new file `FormalSimple.lo.fir` will be generated in the same directory as the input file.

## 7. Testing Other Benchmarks (Optional)

The repository contains **130 FIRRTL programs** under `src/ocaml/demo/`. After running the smoke test, you can manually test any other `.fir` file by running the built binary directly:

```bash
cd src/ocaml_try
./_build/default/generate_lofir.exe ../ocaml/demo/your_target.fir
```

**Large File Warning**: If you wish to test the "XiangShan" benchmark (200+ MB), please ensure Git LFS is installed and run `git lfs pull` first (see Section 4).

## 8. Expected Execution Time

**Smoke Test (./build_and_run.sh)**: **~1–3 minutes** (on a modern 8-core machine).  
- Coq compilation: ~1–3 min  
- OCaml extraction & build: ~10 sec  
- Demo execution: < 1 sec  

## 9. For Detailed Code Navigation

The `README.md` file in the root directory contains:
- A full mapping between paper definitions and specific Coq files (e.g., `LowerTypes.v`, `Semantics.v`).
- An exhaustive explanation of the artifact directory structure.
- Customization instructions for running on different benchmarks.