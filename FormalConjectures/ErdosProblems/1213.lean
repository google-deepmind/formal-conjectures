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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 1213

*References:*
- [erdosproblems.com/1213](https://www.erdosproblems.com/1213)
- [He86] Hegyvári, N., *On consecutive sums in sequences*. Acta Math. Hungar. (1986), 193-200.
-/

@[expose] public section

namespace Erdos1213

/--
A finite sequence `A 0, …, A (s - 1)` has two distinct (nonempty) index intervals
`[u, v)` and `[x, y)` with the same sum.
-/
def HasEqualIntervalSums (A : ℕ → ℕ) (s : ℕ) : Prop :=
  ∃ u v x y : ℕ, u < v ∧ v ≤ s ∧ x < y ∧ y ≤ s ∧ (u, v) ≠ (x, y) ∧
    ∑ i ∈ Finset.Ico u v, A i = ∑ i ∈ Finset.Ico x y, A i

/--
Let $a,K\geq 1$. Does there exist $f(a,K)$ such that if $a=a_1<\cdots <a_s$ is a sequence of
integers with $a_s> f(a,K)$ and with bounded gaps $a_{i+1}-a_i\leq K$ then there are two distinct
intervals $I$ and $J$ such that
$$\sum_{i\in I}a_i=\sum_{j\in J}a_j?$$

Hegyvári [He86] has proved the answer is yes, and gives an explicit bound of the shape
$f(a,K) \ll ae^{O(K)}$. Hegyvári believes that the exponential dependence on $K$ here is not best
possible.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1213.lean#L495"]
theorem erdos_1213 : answer(True) ↔ ∀ a K : ℕ, 1 ≤ a → 1 ≤ K → ∃ f : ℕ,
    ∀ (s : ℕ) (A : ℕ → ℕ), 0 < s → A 0 = a → StrictMonoOn A (Set.Iio s) →
      (∀ i, i + 1 < s → A (i + 1) - A i ≤ K) → f < A (s - 1) → HasEqualIntervalSums A s := by
  sorry

/--
Hegyvári [He86] proved that one can take $f(a,K) \ll ae^{O(K)}$.
-/
@[category research solved, AMS 11]
theorem erdos_1213.variants.hegyvari : ∃ C : ℝ, 0 < C ∧ ∀ a K : ℕ, 1 ≤ a → 1 ≤ K →
    ∀ (s : ℕ) (A : ℕ → ℕ), 0 < s → A 0 = a → StrictMonoOn A (Set.Iio s) →
      (∀ i, i + 1 < s → A (i + 1) - A i ≤ K) → C * a * Real.exp (C * K) < A (s - 1) →
        HasEqualIntervalSums A s := by
  sorry

end Erdos1213
