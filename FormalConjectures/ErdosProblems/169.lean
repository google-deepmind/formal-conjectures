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
import Mathlib

open scoped ENNReal

/-!
# Erdős Problem 169: statement formalization

Source: the supplied `169(1).pdf`, pp. 1–4.

This file defines the main question and the uniform-tail question from p. 2.
It does NOT prove either question, the numerical records in the comments,
or the asserted equivalence with Erdős Problem 3.

Reciprocal sums and their supremum live in `ENNReal`, so divergence is
represented by infinity rather than by the default value of a real `tsum`.
`W k` is the TWO-colour van der Waerden number on {1, ..., N}.

No `sorry`, additional axioms, or `native_decide` are used. The conjectures
are definitions of propositions, not theorems asserting those propositions.
Compilation has not been checked in the authoring environment.
-/

namespace Erdos169

/-- A nonconstant k-term arithmetic progression contained in A. -/
def HasAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ A

/-- A contains no nonconstant k-term arithmetic progression. -/
def APFree (A : Set ℕ) (k : ℕ) : Prop :=
  ¬ HasAP A k

/-- A is a set of strictly positive integers with no k-term progression. -/
def Admissible (A : Set ℕ) (k : ℕ) : Prop :=
  (∀ n ∈ A, 0 < n) ∧ APFree A k

/-- The sum of reciprocals, with infinity permitted. -/
noncomputable def reciprocalSum (A : Set ℕ) : ℝ≥0∞ :=
  ∑' n : A, ((n.val : ℝ≥0∞)⁻¹)

/-- The extremal function from Problem 169. -/
noncomputable def f (k : ℕ) : ℝ≥0∞ :=
  ⨆ (A : Set ℕ) (_ : Admissible A k), reciprocalSum A

/-- Every two-colouring of {1, ..., N} contains a monochromatic k-AP.
Colourings of all naturals are equivalent here, since only 1,...,N are used. -/
def VanDerWaerdenProperty (k N : ℕ) : Prop :=
  ∀ c : ℕ → Fin 2, ∃ a d : ℕ,
    0 < a ∧ 0 < d ∧
    (∀ i : ℕ, i < k → a + i * d ≤ N) ∧
    (∀ i : ℕ, i < k → c (a + i * d) = c a)

/-- Least positive N with the two-colour van der Waerden property.
Existence is the classical van der Waerden theorem, not proved in this file.
As usual for `sInf` on naturals, an empty defining set would give zero. -/
noncomputable def W (k : ℕ) : ℕ :=
  sInf {N : ℕ | 0 < N ∧ VanDerWaerdenProperty k N}

/-- For k ≥ 3 this is the positive real number log(W(k)), in ENNReal. -/
noncomputable def logW (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.log (W k : ℝ))

/-- The quotient, retaining the possibility that f(k) is infinite. -/
noncomputable def normalizedF (k : ℕ) : ℝ≥0∞ :=
  f k / logW k

/-- Main question: does f(k) / log(W(k)) tend to infinity?
`𝓝 ⊤` is intentional: infinity is an actual point of ENNReal.
Starting at k + 3 restricts the sequence to the domain in the PDF. -/
def Conjecture : Prop :=
  Filter.Tendsto (fun k : ℕ => normalizedF (k + 3))
    Filter.atTop (nhds (⊤ : ℝ≥0∞))

/-- The finiteness assertion discussed in the PDF. Its equivalence with
Erdős Problem 3 is not asserted as a proved theorem here. -/
def FiniteExtremalSums : Prop :=
  ∀ k : ℕ, 3 ≤ k → f k < ⊤

/-- The uniform-tail question on p. 2. The cutoff formulation also handles
the empty set without needing to assign it a minimum. -/
def UniformTailConjecture : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ A : Set ℕ,
      Admissible A k → (∀ n ∈ A, N ≤ n) →
      reciprocalSum A < ENNReal.ofReal ε

/-! Elementary structural facts, independent of the conjectures. -/

/-- A progression remains a progression in a larger set. -/
theorem hasAP_mono {A B : Set ℕ} {k : ℕ}
    (hAB : A ⊆ B) (h : HasAP A k) : HasAP B k := by
  rcases h with ⟨a, d, hd, hmem⟩
  exact ⟨a, d, hd, fun i hi => hAB (hmem i hi)⟩

/-- An initial segment of a progression is a shorter progression. -/
theorem hasAP_of_le {A : Set ℕ} {k l : ℕ}
    (hkl : k ≤ l) (h : HasAP A l) : HasAP A k := by
  rcases h with ⟨a, d, hd, hmem⟩
  exact ⟨a, d, hd, fun i hi => hmem i (lt_of_lt_of_le hi hkl)⟩

/-- Avoiding k-term progressions implies avoiding longer progressions. -/
theorem apFree_of_le {A : Set ℕ} {k l : ℕ}
    (hkl : k ≤ l) (h : APFree A k) : APFree A l := by
  intro hl
  exact h (hasAP_of_le hkl hl)

/-- Every admissible reciprocal sum is bounded by the defining supremum. -/
theorem reciprocalSum_le_f {A : Set ℕ} {k : ℕ}
    (h : Admissible A k) : reciprocalSum A ≤ f k := by
  unfold f
  exact le_iSup_of_le A (le_iSup_of_le h le_rfl)

/-- The extremal function is nondecreasing. -/
theorem f_monotone : Monotone f := by
  intro k l hkl
  unfold f
  refine iSup_le fun A => iSup_le fun h => ?_
  exact le_iSup_of_le A
    (le_iSup_of_le (show Admissible A l from
      ⟨h.1, apFree_of_le hkl h.2⟩) le_rfl)

end Erdos169
