# REQUIREMENTS for [Fixed-Point Semantics and Verified Lowering Transformations for FIRRTL] Artifact

## 1. Hardware Architecture
- **Minimum RAM**: 8GB
- **Disk Space**: 5GB minimum (for dependencies and build artifacts)

## 2. Software Requirements (Native Environment)

### Base System
- **Operating System**: macOS ≥12 (Monterey), Linux (Ubuntu 22.04/Debian 11+)
- **Package Manager**: Homebrew (macOS), apt (Linux)
- **Git LFS** ≥3.0 – required to retrieve large benchmark files stored with Git LFS.

### Core Dependencies
- [Coq](https://coq.inria.fr) = 8.16.0
- [Mathematical Components](https://math-comp.github.io) (MathComp) = 1.15.0
- [OCaml](https://ocaml.org) = 4.14.2
- [dune](https://dune.build) = 3.16.0