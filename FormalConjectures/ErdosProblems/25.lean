/-
Copyright 2025 The Formal Conjectures Authors.

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

/-!
# Erdős Problem 25: Logarithmic density of size-dependent congruences

Let $n_1 < n_2 < \dots$ be an arbitrary sequence of integers, each with an associated residue class
$a_i \pmod{n_i}$. Let $A$ be the set of integers $n$ such that for every $i$ either $n < n_i$ or
$n \not\equiv a_i \pmod{n_i}$. Must the logarithmic density of $A$ exist?

*Reference:* [erdosproblems.com/25](https://www.erdosproblems.com/25)

We first define logarithmic density, as it is not yet in the core Mathlib.
-/

open Filter Finset Real Nat Set
open scoped Topology
open Classical

section LogarithmicDensity

/-- The partial logarithmic sum of a set `A` up to `n`.
    Sum of 1/k for k in A ∩ [1, n]. -/
noncomputable def partialLogSum (A : Set ℕ) (n : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1), if k ∈ A ∧ k ≠ 0 then (1 : ℝ) / k else 0

/--
A set `A` has logarithmic density `d` if the sequence
$(1 / \log n) \cdot \sum_{k \in A, k \le n} (1/k)$ converges to `d`.
-/
def HasLogarithmicDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun n => partialLogSum A n / Real.log n) atTop (𝓝 d)

end LogarithmicDensity

namespace Erdos25

/-- The parameters for the problem: a sequence of moduli and residues. -/
structure CongruenceSystem where
  n : ℕ → ℕ             -- Sequence of moduli n_i
  a : ℕ → ℤ             -- Sequence of residues a_i
  n_pos : ∀ i, 0 < n i  -- Moduli must be positive
  n_strict_mono : StrictMono n -- n_1 < n_2 <... (strictly increasing)

/--
The "Survivor Set" A.
An integer `x` is in `A` if for every index `i`, `x` "escapes" the constraint.
Escape condition: either `x` is small (`x < n_i`) OR `x` does not match the residue (`x ≢ a_i mod n_i`).
-/
def survivor_set (S : CongruenceSystem) : Set ℕ :=
  { x | ∀ i, (x : ℤ) < S.n i ∨ ¬((x : ℤ) ≡ S.a i [ZMOD S.n i]) }

/--
**Erdős Problem 25**

Let $n_1 < n_2 < \dots$ be an arbitrary sequence of integers, each with an associated residue class
$a_i \pmod{n_i}$. Let $A$ be the set of integers $n$ such that for every $i$ either $n < n_i$ or
$n \not\equiv a_i \pmod{n_i}$. Must the logarithmic density of $A$ exist?
-/
@[category research open, AMS 11]
theorem erdos_25 (S : CongruenceSystem) :
    (∃ d, HasLogarithmicDensity (survivor_set S) d) ↔ answer(sorry) := by
  sorry

end Erdos25
