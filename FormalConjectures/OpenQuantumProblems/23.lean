/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

noncomputable section


/-!
# Open Quantum Problem 23: SIC-POVMs

## Mathematical problem
The OQP page presents three increasingly strong formulations of this problem.
In this file we formalize the first one, closest to the physics terminology:
existence of a symmetric informationally complete POVM in every finite dimension.

A SIC-POVM in dimension $d$ can be represented by a family of $d^2$ normalized
vectors in $\mathbb{C}^d$ whose pairwise squared overlaps are all equal to
$(d + 1)^{-1}$. We encode such a family as a map `Fin (d ^ 2) → StateVector d`.

## Background
SIC-POVMs are a basic structure in finite-dimensional quantum information.
They are closely related to equiangular lines, tight frames, quantum state
reconstruction, and finite-dimensional measurement theory.
The open problem asks whether such families exist in every dimension.

## What this file formalizes
This file formalizes the existence problem for symmetric informationally complete
POVMs through the predicate `HasSICPOVM d`.

More precisely, it contains the following layers.

### Core API
The main definitions formalized in this file are:
- `StateVector d`: a state vector in `ℂ^d`;
- `mkStateVector`: constructor from coordinates in the computational basis;
- `IsNormalized ψ`: normalization predicate for a state vector;
- `overlapSq φ ψ`: squared magnitude of the inner-product overlap;
- `HasConstantOverlapSq c Φ`: constant pairwise squared-overlap condition;
- `sicOverlapSq d`: the SIC overlap value `(d + 1)⁻¹`;
- `IsSICFamily d Φ`: the predicate that a family of `d^2` vectors in `ℂ^d`
  is a SIC family;
- `HasSICPOVM d`: existence of a SIC family in dimension `d`.

In addition, the file includes explicit witness families and convenient
constructors used in the low-dimensional benchmark cases:
- `vec2`, `vec3`;
- `qubitSICFamily`;
- `hesseFamily`;
- `bb84Family`.

### Complete open conjecture
The main open theorem is:
- `sicPOVMs`, expressing the conjecture that for every `d ≥ 1`, there exists a
  SIC-POVM in dimension `d`.

### Special cases
The file also isolates several special cases:
- solved low-dimensional benchmark cases:
  `hasSICPOVM_zero`, `hasSICPOVM_one`, `hasSICPOVM_two`, `hasSICPOVM_three`;
- a negative benchmark result:
  `bb84Family_not_isSICFamily`, showing that the BB84 family in dimension `2`
  does not form a SIC family;
- selected open benchmark dimensions:
  `hasSICPOVM_56`, `hasSICPOVM_58`, `hasSICPOVM_59`, `hasSICPOVM_60`,
  `hasSICPOVM_64`, `hasSICPOVM_68`, `hasSICPOVM_69`, `hasSICPOVM_70`,
  `hasSICPOVM_71`, `hasSICPOVM_72`, `hasSICPOVM_75`.

### Test lemmas
The file includes the following test lemmas and benchmark-support statements:
- `hasConstantOverlapSq_singleton`;
- `sicOverlapSq_one`, `sicOverlapSq_two`, `sicOverlapSq_three`,
  `sicOverlapSq_pos`;
- `isSICFamily_singleton_iff`, `isSICFamily_one_of_normalized`;
- `qubitSICFamily_normalized`, `qubitSICFamily_pairwise`;
- `hesseFamily_normalized`, `hesseFamily_pairwise`;
- `bb84Family_normalized`.

At present, these `@[category test, AMS 15 47 81]` results are included with
placeholder proofs `by sorry`; they are intended to be proved in the next PR.

## References
*Primary source list entry:*
- IQOQI Vienna Open Quantum Problems, problem 23:
  https://oqp.iqoqi.oeaw.ac.at/sic-povms-and-zauners-conjecture
- Formal Conjectures issue #1823:
  https://github.com/google-deepmind/formal-conjectures/issues/1823

### Foundational references
- J. M. Renes, R. Blume-Kohout, A. J. Scott, and M. C. Caves,
  *Symmetric informationally complete quantum measurements*,
  J. Math. Phys. 45, 2171-2180 (2004), arXiv:quant-ph/0310075.
- G. Zauner,
  *Quantum Designs: Foundations of a Noncommutative Design Theory*,
  PhD thesis, University of Vienna (1999).
-/

namespace OpenQuantumProblem23

/- ## Basic structures -/

/-- A state vector in the $d$-dimensional complex Hilbert space $\mathbb{C}^d$. -/
abbrev StateVector (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- Build a state vector from its coordinates in the computational basis. -/
abbrev mkStateVector {d : ℕ} (ψ : Fin d → ℂ) : StateVector d := WithLp.toLp 2 ψ

/-- Coercion from a state vector to its coordinate function. -/
instance {d : ℕ} : CoeFun (StateVector d) (fun _ => Fin d → ℂ) where
  coe ψ := ψ.ofLp

/-- A state vector is normalized if it has $L^2$ norm $1$. -/
def IsNormalized {d : ℕ} (ψ : StateVector d) : Prop := ‖ψ‖ = 1

/-- The squared magnitude of the overlap between two state vectors. -/
def overlapSq {d : ℕ} (φ ψ : StateVector d) : ℝ :=
  Complex.normSq (∑ i : Fin d, star (φ i) * ψ i)

/-- A family has constant pairwise squared overlap $c$ if every two distinct members have squared overlap $c$. -/
def HasConstantOverlapSq {d N : ℕ} (c : ℝ) (Φ : Fin N → StateVector d) : Prop :=
  Pairwise fun i j => overlapSq (Φ i) (Φ j) = c

/-- The squared overlap value of a SIC family in dimension $d$. -/
def sicOverlapSq (d : ℕ) : ℝ := (d + 1 : ℝ)⁻¹

/-- A SIC family in dimension $d$ consists of $d^2$ normalized vectors in $\mathbb{C}^d$ with pairwise squared overlap $(d + 1)^{-1}$. -/
def IsSICFamily (d : ℕ) (Φ : Fin (d ^ 2) → StateVector d) : Prop :=
  (∀ i, IsNormalized (Φ i)) ∧ HasConstantOverlapSq (sicOverlapSq d) Φ

/-- There exists a SIC-POVM in dimension $d$. -/
def HasSICPOVM (d : ℕ) : Prop :=
  ∃ Φ : Fin (d ^ 2) → StateVector d, IsSICFamily d Φ

/- ## Basic benchmark cases -/

/-- Any singleton family has constant pairwise squared overlap, vacuously. -/
@[category test, AMS 15 47 81]
lemma hasConstantOverlapSq_singleton {d : ℕ} (c : ℝ) (ψ : StateVector d) :
    HasConstantOverlapSq c (fun _ : Fin 1 => ψ) := by sorry

/-- The SIC overlap value in dimension $1$ is $1/2$. -/
@[category test, AMS 15 47 81]
lemma sicOverlapSq_one : sicOverlapSq 1 = (1 / 2 : ℝ) := by sorry

/-- The SIC overlap value is positive in every dimension. -/
@[category test, AMS 15 47 81]
lemma sicOverlapSq_pos (d : ℕ) : 0 < sicOverlapSq d := by sorry

/-- In dimension $1$, a singleton family is SIC exactly when its vector is normalized. -/
@[category test, AMS 15 47 81]
lemma isSICFamily_singleton_iff {ψ : StateVector 1} :
    IsSICFamily 1 (fun _ : Fin 1 => ψ) ↔ IsNormalized ψ := by sorry

/-- The empty family witnesses the degenerate dimension-$0$ case. -/
@[category test, AMS 15 47 81]
theorem hasSICPOVM_zero : HasSICPOVM 0 := by sorry

/-- Any normalized state in dimension $1$ yields a SIC family. -/
@[category test, AMS 15 47 81]
lemma isSICFamily_one_of_normalized {ψ : StateVector 1} (hψ : IsNormalized ψ) :
    IsSICFamily 1 (fun _ : Fin 1 => ψ) := by sorry

/-- Dimension $1$ admits a SIC-POVM. -/
@[category test, AMS 15 47 81]
theorem hasSICPOVM_one : HasSICPOVM 1 := by sorry

/- ## Explicit low-dimensional witnesses -/

/-- The standard algebraic primitive cube root of unity. -/
def ω : ℂ :=
  ((-(1 : ℝ) / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I

/-- The first real amplitude used in the tetrahedral qubit SIC. -/
def tetraA : ℝ := Real.sqrt (1 / 3)

/-- The second real amplitude used in the tetrahedral qubit SIC. -/
def tetraB : ℝ := Real.sqrt (2 / 3)

/-- The common scale used in the Hesse qutrit SIC. -/
def hesseS : ℝ := Real.sqrt (1 / 2)

/-- A convenient constructor for qubit state vectors. -/
def vec2 (z₀ z₁ : ℂ) : StateVector 2 := mkStateVector ![z₀, z₁]

/-- A convenient constructor for qutrit state vectors. -/
def vec3 (z₀ z₁ z₂ : ℂ) : StateVector 3 := mkStateVector ![z₀, z₁, z₂]

/-- The tetrahedral qubit SIC family. -/
def qubitSICFamily : Fin 4 → StateVector 2
  | 0 => vec2 1 0
  | 1 => vec2 (tetraA : ℂ) (tetraB : ℂ)
  | 2 => vec2 (tetraA : ℂ) ((tetraB : ℂ) * ω)
  | _ => vec2 (tetraA : ℂ) ((tetraB : ℂ) * (ω ^ 2))

/-- The Hesse qutrit SIC family. -/
def hesseFamily : Fin 9 → StateVector 3
  | 0 => vec3 0 (hesseS : ℂ) (-(hesseS : ℂ))
  | 1 => vec3 0 (hesseS : ℂ) (-((hesseS : ℂ) * ω))
  | 2 => vec3 0 (hesseS : ℂ) (-((hesseS : ℂ) * (ω ^ 2)))
  | 3 => vec3 (-(hesseS : ℂ)) 0 (hesseS : ℂ)
  | 4 => vec3 (-((hesseS : ℂ) * ω)) 0 (hesseS : ℂ)
  | 5 => vec3 (-((hesseS : ℂ) * (ω ^ 2))) 0 (hesseS : ℂ)
  | 6 => vec3 (hesseS : ℂ) (-(hesseS : ℂ)) 0
  | 7 => vec3 (hesseS : ℂ) (-((hesseS : ℂ) * ω)) 0
  | _ => vec3 (hesseS : ℂ) (-((hesseS : ℂ) * (ω ^ 2))) 0

/-- The BB84 family of four qubit states. -/
def bb84Family : Fin 4 → StateVector 2
  | 0 => vec2 1 0
  | 1 => vec2 0 1
  | 2 => vec2 (hesseS : ℂ) (hesseS : ℂ)
  | _ => vec2 (hesseS : ℂ) (-(hesseS : ℂ))

/-- The SIC overlap value in dimension $2$ is $1/3$. -/
@[category test, AMS 15 47 81]
lemma sicOverlapSq_two : sicOverlapSq 2 = (1 / 3 : ℝ) := by sorry

/-- The SIC overlap value in dimension $3$ is $1/4$. -/
@[category test, AMS 15 47 81]
lemma sicOverlapSq_three : sicOverlapSq 3 = (1 / 4 : ℝ) := by sorry

/-- Every vector in the tetrahedral qubit SIC family is normalized. -/
@[category test, AMS 15 47 81]
lemma qubitSICFamily_normalized (i : Fin 4) :
    IsNormalized (qubitSICFamily i) := by sorry

/-- The tetrahedral qubit SIC family has the correct constant pairwise overlap. -/
@[category test, AMS 15 47 81]
lemma qubitSICFamily_pairwise :
    HasConstantOverlapSq (sicOverlapSq 2) qubitSICFamily := by sorry

/-- Dimension $2$ admits a SIC-POVM, witnessed by the tetrahedral qubit SIC. -/
@[category test, AMS 15 47 81]
theorem hasSICPOVM_two : HasSICPOVM 2 := by sorry

/-- Every vector in the Hesse qutrit SIC family is normalized. -/
@[category test, AMS 15 47 81]
lemma hesseFamily_normalized (i : Fin 9) :
    IsNormalized (hesseFamily i) := by sorry

/-- The Hesse qutrit SIC family has the correct constant pairwise overlap. -/
@[category test, AMS 15 47 81]
lemma hesseFamily_pairwise :
    HasConstantOverlapSq (sicOverlapSq 3) hesseFamily := by sorry

/-- Dimension $3$ admits a SIC-POVM, witnessed by the Hesse qutrit SIC. -/
@[category test, AMS 15 47 81]
theorem hasSICPOVM_three : HasSICPOVM 3 := by sorry

/-- Every vector in the BB84 family is normalized. -/
@[category test, AMS 15 47 81]
lemma bb84Family_normalized (i : Fin 4) :
    IsNormalized (bb84Family i) := by sorry

/-- The BB84 family has the right cardinality for a qubit SIC but fails the constant-overlap condition. -/
@[category test, AMS 15 47 81]
theorem bb84Family_not_isSICFamily : ¬ IsSICFamily 2 bb84Family := by sorry

/- ## Smallest open special cases (all d<=75) -/

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $56$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_56 : answer(sorry) ↔ HasSICPOVM 56 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $58$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_58 : answer(sorry) ↔ HasSICPOVM 58 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $59$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_59 : answer(sorry) ↔ HasSICPOVM 59 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $60$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_60 : answer(sorry) ↔ HasSICPOVM 60 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $64$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_64 : answer(sorry) ↔ HasSICPOVM 64 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $68$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_68 : answer(sorry) ↔ HasSICPOVM 68 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $69$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_69 : answer(sorry) ↔ HasSICPOVM 69 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $70$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_70 : answer(sorry) ↔ HasSICPOVM 70 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $71$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_71 : answer(sorry) ↔ HasSICPOVM 71 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $72$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_72 : answer(sorry) ↔ HasSICPOVM 72 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $75$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_75 : answer(sorry) ↔ HasSICPOVM 75 := by sorry

/- ## Full conjecture -/

/-- Do SIC-POVMs exist in every finite dimension? -/
@[category research open, AMS 15 47 81]
theorem sicPOVMs :
    answer(sorry) ↔ ∀ d : ℕ, 1 ≤ d → HasSICPOVM d := by
  sorry

end OpenQuantumProblem23
