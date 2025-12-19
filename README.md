# lean-works

[![Lean Action CI](https://github.com/yannickseurin/lean-works/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/yannickseurin/lean-works/actions/workflows/lean_action_ci.yml)
[![Dynamic Regex Badge](https://img.shields.io/badge/dynamic/regex?url=https://raw.githubusercontent.com/yannickseurin/lean-works/refs/heads/main/lean-toolchain&search=leanprover/lean4:(.*)&replace=$1&label=Lean4)](https://github.com/leanprover/lean4)

Experimenting with Lean 4 for proving stuff related to cryptography.

## Overview

The files in the main *LeanWorks* folder are organized as follows.

### Root files

- *ToMathlib.lean*: General lemmas that don't fit anywhere else and could potentially be pushed to Mathlib.
- *Negligible.lean*: Some results about negligible functions. It includes the proof of a theorem by Bellare about the equivalence of two definitions of negligibility for a family of functions (namely, Theorem 3.2 from https://eprint.iacr.org/1997/004.pdf).
- *Probability.lean*: General results about probabilities. For example, we prove that if `f : α → β` is bijective, then drawing `a` uniformly from `α`
and applying `f` yields the uniform distribution on `β`.

### *Hard Problems* Folder 

Folder containing files defining hardness assumptions:

- *CyclicGroups.lean*: Hard problems in cyclic groups (discrete logarithm, CDH, DDH...).

### *Cryptosystems* folder

Folder containing files defining various cryptographic primitives and schemes and related security proofs:

#### PKE folder

Public key encryption schemes:

- *Defs.lean*: Basic definitions about public-key encryption schemes (syntax, correctness, IND-CPA security).

## Prerequisites

First, you need to [install Lean4](https://lean-lang.org/install/) on your machine.

## Setup

Then, clone this repository and, from the root of the project, run

```bash
lake exe cache get
lake build
```

## Lean resources

- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Style guidelines](https://leanprover-community.github.io/contribute/style.html)
- [Documentation guidelines](https://leanprover-community.github.io/contribute/doc.html) 
