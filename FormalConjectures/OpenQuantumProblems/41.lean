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
open scoped BigOperators ComplexOrder

/-!
# Open Quantum Problem 41

Core definitions for the tripartite mixed-state formulation of OQP 41,
together with the main open theorem.
-/
namespace OpenQuantumProblem41

/-- Computational-basis indices for the `AB` subsystem. -/
abbrev ABIdx (dA dB : ℕ) := Fin dA × Fin dB

/-- Computational-basis indices for the `AC` subsystem. -/
abbrev ACIdx (dA dC : ℕ) := Fin dA × Fin dC

/-- Computational-basis indices for the `BC` subsystem. -/
abbrev BCIdx (dB dC : ℕ) := Fin dB × Fin dC

/-- Computational-basis indices for the full `ABC` system. -/
abbrev ABCIdx (dA dB dC : ℕ) := Fin dA × Fin dB × Fin dC

/-- Matrices on `H_A ⊗ H_B ⊗ H_C`, expressed in the computational basis. -/
abbrev TripartiteMatrix (dA dB dC : ℕ) :=
  Matrix (ABCIdx dA dB dC) (ABCIdx dA dB dC) ℂ

/-- Matrices on `H_A ⊗ H_B`. -/
abbrev BipartiteMatrixAB (dA dB : ℕ) :=
  Matrix (ABIdx dA dB) (ABIdx dA dB) ℂ

/-- Matrices on `H_A ⊗ H_C`. -/
abbrev BipartiteMatrixAC (dA dC : ℕ) :=
  Matrix (ACIdx dA dC) (ACIdx dA dC) ℂ

/-- Matrices on `H_B ⊗ H_C`. -/
abbrev BipartiteMatrixBC (dB dC : ℕ) :=
  Matrix (BCIdx dB dC) (BCIdx dB dC) ℂ

/-- A tripartite density matrix on `H_A ⊗ H_B ⊗ H_C`, represented in
computational-basis coordinates. -/
def IsDensityMatrix {dA dB dC : ℕ} (ρ : TripartiteMatrix dA dB dC) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = (1 : ℂ)

/-- Partial trace over subsystem `A`. -/
def partialTraceA {dA dB dC : ℕ}
    (ρ : TripartiteMatrix dA dB dC) : BipartiteMatrixBC dB dC :=
  fun i j => ∑ a : Fin dA, ρ (a, i.1, i.2) (a, j.1, j.2)

/-- Partial trace over subsystem `B`. -/
def partialTraceB {dA dB dC : ℕ}
    (ρ : TripartiteMatrix dA dB dC) : BipartiteMatrixAC dA dC :=
  fun i j => ∑ b : Fin dB, ρ (i.1, b, i.2) (j.1, b, j.2)

/-- Partial trace over subsystem `C`. -/
def partialTraceC {dA dB dC : ℕ}
    (ρ : TripartiteMatrix dA dB dC) : BipartiteMatrixAB dA dB :=
  fun i j => ∑ c : Fin dC, ρ (i.1, i.2, c) (j.1, j.2, c)

/-- `r_{AB} = rank(Tr_C(ρ))`. -/
def marginalRankAB {dA dB dC : ℕ} (ρ : TripartiteMatrix dA dB dC) : ℕ :=
  Matrix.rank (partialTraceC ρ)

/-- `r_{AC} = rank(Tr_B(ρ))`. -/
def marginalRankAC {dA dB dC : ℕ} (ρ : TripartiteMatrix dA dB dC) : ℕ :=
  Matrix.rank (partialTraceB ρ)

/-- `r_{BC} = rank(Tr_A(ρ))`. -/
def marginalRankBC {dA dB dC : ℕ} (ρ : TripartiteMatrix dA dB dC) : ℕ :=
  Matrix.rank (partialTraceA ρ)

/-- The concrete rank inequality singled out on the OQP page. -/
def SatisfiesOQP41 {dA dB dC : ℕ} (ρ : TripartiteMatrix dA dB dC) : Prop :=
  marginalRankAB ρ ≤ marginalRankAC ρ * marginalRankBC ρ

/-- Open Quantum Problem 41 in the explicit tripartite mixed-state form stated on the OQP page. -/
@[category research open, AMS 15 47 81 94]
theorem oqp_41 :
    answer(sorry) ↔
      ∀ dA dB dC : ℕ,
        1 ≤ dA →
        1 ≤ dB →
        1 ≤ dC →
        ∀ ρ : TripartiteMatrix dA dB dC,
          IsDensityMatrix ρ → SatisfiesOQP41 ρ := by
  sorry

end OpenQuantumProblem41
