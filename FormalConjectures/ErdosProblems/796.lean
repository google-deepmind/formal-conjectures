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

import FormalConjecturesUtil

/-!
# Erdős Problem 796

*Reference:* [erdosproblems.com/796](https://www.erdosproblems.com/796)
-/

namespace Erdos796

open Classical Filter
open scoped Topology

/-- The number of unordered representations `m = a₁ * a₂` by two distinct
elements `a₁ < a₂` of `A`. -/
def repCount (A : Finset ℕ) (m : ℕ) : ℕ :=
  ((A ×ˢ A).filter fun a => a.1 < a.2 ∧ a.1 * a.2 = m).card

/-- `A` has at most `k - 1` representations of every `m` (fewer than `k`). -/
def HasRepBound (k : ℕ) (A : Finset ℕ) : Prop := ∀ m : ℕ, repCount A m < k

/-- `g k n = g_k(n)` is the largest size of a subset `A ⊆ {1, …, n}` in which
every `m` has fewer than `k` representations `m = a₁ a₂` with `a₁ < a₂ ∈ A`. -/
noncomputable def g (k n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (HasRepBound k)).sup Finset.card

/-- The proposed second-order rescaling of `g_3(n)`:
`(g_3(n) - (log log n / log n) · n) / (n / log n)`, whose limit is the constant
`c` in the problem. -/
noncomputable def normalizedError (n : ℕ) : ℝ :=
  ((g 3 n : ℝ) - (n : ℝ) * Real.log (Real.log n) / Real.log n) / ((n : ℝ) / Real.log n)

/--
Let $k\geq 2$ and let $g_k(n)$ be the largest possible size of
$A\subseteq \{1,\ldots,n\}$ such that every $m$ has $<k$ solutions to
$m=a_1a_2$ with $a_1<a_2\in A$. Is it true that
$$g_3(n)=\frac{\log\log n}{\log n}n+(c+o(1))\frac{n}{\log n}$$
for some constant $c$?

The answer is yes: the rescaled error `normalizedError` converges.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/williamjblair/lean-proofs/blob/main/starfleet/erdos-796/Research/CanonicalTail.lean"]
theorem erdos_796 :
    answer(True) ↔ ∃ c : ℝ, Tendsto normalizedError atTop (𝓝 c) := by
  sorry

end Erdos796
