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
-/

open Filter Finset Real Nat Set
open scoped Topology
open Classical

namespace Erdos25

/--
A set `A` has logarithmic density `d` if the sequence
$(1 / \log n) \cdot \sum_{k \in A, k \le n} (1/k)$ converges to `d`.
-/
def HasLogarithmicDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun n => (∑ k ∈ range (n + 1) with k ∈ A, (1 : ℝ) / k) / Real.log n) atTop (𝓝 d)

/--
**Erdős Problem 25**

Let $n_1 < n_2 < \dots$ be an arbitrary sequence of integers, each with an associated residue class
$a_i \pmod{n_i}$. Let $A$ be the set of integers $n$ such that for every $i$ either $n < n_i$ or
$n \not\equiv a_i \pmod{n_i}$. Must the logarithmic density of $A$ exist?
-/
@[category research open, AMS 11]
theorem erdos_25 (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (h_pos : ∀ i, 0 < seq_n i)
    (h_mono : StrictMono seq_n) :
    (∃ d, HasLogarithmicDensity
      { x : ℕ | ∀ i, (x : ℤ) < seq_n i ∨ ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i]) } d)
    ↔ answer(sorry) := by
  sorry

end Erdos25
