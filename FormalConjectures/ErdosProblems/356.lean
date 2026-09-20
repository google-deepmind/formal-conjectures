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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 356

*References:*
- [erdosproblems.com/356](https://www.erdosproblems.com/356)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Ko15] Konieczny, J., *On consecutive sums in permutations*. arXiv:1504.07156 (2015).
- [Be23b] Beker, A., *On a problem of Erdős and Graham about consecutive sums in strictly
  increasing sequences*. arXiv:2311.10087 (2023).
-/

@[expose] public section

open Filter

namespace Erdos356

/-- The set of sums $\sum_{u\leq i\leq v}a_i$ of nonempty consecutive blocks of a finite
sequence `a`. -/
def consecutiveSums {k : ℕ} (a : Fin k → ℕ) : Finset ℕ :=
  (Finset.univ.filter fun p : Fin k × Fin k => p.1 ≤ p.2).image
    fun p => ∑ i ∈ Finset.Icc p.1 p.2, a i

/--
Is there some $c>0$ such that, for all sufficiently large $n$, there exist integers
$a_1<\cdots<a_k\leq n$ such that there are at least $cn^2$ distinct integers of the form
$\sum_{u\leq i\leq v}a_i$?

This fails for $a_i=i$ for example. Erdős and Graham [ErGr80] also ask what happens if we drop
the monotonicity restriction and just ask that the $a_i$ are distinct. They speculated that
perhaps some permutation of $\{1,\ldots,n\}$ has at least $cn^2$ such distinct sums - this is
true, as proved by Konieczny [Ko15] (see [34](https://www.erdosproblems.com/34)).

The original problem was solved (in the affirmative) by Beker [Be23b].

See also [34](https://www.erdosproblems.com/34), [357](https://www.erdosproblems.com/357), and
[358](https://www.erdosproblems.com/358).
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos356.lean#L1135"]
theorem erdos_356 : answer(True) ↔ ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    ∃ (k : ℕ) (a : Fin k → ℕ), StrictMono a ∧ (∀ i, 1 ≤ a i ∧ a i ≤ n) ∧
      c * n ^ 2 ≤ (consecutiveSums a).card := by
  sorry

/--
Erdős and Graham [ErGr80] also ask how many consecutive integers $>n$ can be represented as such
a sum. Is it true that, for any $c>0$ at least $cn$ such integers are possible (for sufficiently
large $n$)?
-/
@[category research open, AMS 11]
theorem erdos_356.variants.consecutive : answer(sorry) ↔ ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop,
    ∃ (k : ℕ) (a : Fin k → ℕ), StrictMono a ∧ (∀ i, 1 ≤ a i ∧ a i ≤ n) ∧
      ∃ m : ℕ, n < m ∧ ∀ j : ℕ, m ≤ j → j < m + ⌈c * n⌉₊ → j ∈ consecutiveSums a := by
  sorry

end Erdos356
