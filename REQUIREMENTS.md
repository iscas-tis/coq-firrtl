# REQUIREMENTS for [Fixed-Point Semantics and Verified Lowering Transformations for FIRRTL] Artifact

## 1. Hardware Architecture
- **Minimum RAM**: 8GB
- **Disk Space**: 5GB minimum (for dependencies and build artifacts)

## 2. Software Requirements (Native Environment)
*For users not using Docker - RECOMMENDED to use Docker instead*

### Base System
- **Operating System**: macOS ≥12 (Monterey), Linux (Ubuntu 22.04/Debian 11+)
- **Package Manager**: Homebrew (macOS), apt (Linux)

### Core Dependencies
- [Coq](https://coq.inria.fr) = 8.16.0
- [Mathematical Components](https://math-comp.github.io) (MathComp) = 1.15.0
- [OCaml](https://ocaml.org) = 4.14.2
- [dune](https://dune.build) = 3.16.0

## 3. Docker Environment (RECOMMENDED)
The provided Dockerfile creates a reproducible environment with all dependencies.

### Docker Specifications
- **Base Image**: `ocaml/opam:debian-ocaml-4.14`
- **To be installed**:
  - Coq 8.16.0
  - MathComp 1.15.0
  - dune 3.16.0