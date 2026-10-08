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
# Erdős Problem 356

*References:*
- [erdosproblems.com/356](https://www.erdosproblems.com/356)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980), p. 58.
- [Be23b] Beker, A., *On a problem of Erdős and Graham about consecutive sums in strictly
  increasing sequences*. arXiv:2311.10087 (2023).
-/

@[expose] public section

namespace Erdos356

/-- The finite set of sums of nonempty consecutive blocks of `a 1, …, a k`. -/
def consecutiveSums (k : ℕ) (a : ℕ → ℤ) : Finset ℤ :=
  ((Finset.Icc 1 k ×ˢ Finset.Icc 1 k).filter (fun p => p.1 ≤ p.2)).image
    (fun p => ∑ i ∈ Finset.Icc p.1 p.2, a i)

/-- The integers `a 1, …, a k` are strictly increasing and lie in `[1, n]`. -/
def IsAdmissible (n k : ℕ) (a : ℕ → ℤ) : Prop :=
  (∀ i ∈ Finset.Icc 1 k, ∀ j ∈ Finset.Icc 1 k, i < j → a i < a j) ∧
  (∀ i ∈ Finset.Icc 1 k, 1 ≤ a i ∧ a i ≤ n)

/--
Is there some $c>0$ such that, for all sufficiently large $n$, there exist integers
$a_1<\cdots<a_k\leq n$ such that there are at least $cn^2$ distinct integers of the form
$\sum_{u\leq i\leq v}a_i$?

The original problem was solved (in the affirmative) by Beker [Be23b].

We require $1\leq a_i$, as in Beker's formulation of the problem.
-/
@[category research solved, AMS 5 11]
@[formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos356.lean#L1135"]
theorem erdos_356 : answer(True) ↔
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∃ (k : ℕ) (a : ℕ → ℤ), IsAdmissible n k a ∧
        c * (n : ℝ) ^ 2 ≤ (consecutiveSums k a).card := by
  sorry

/--
They also ask how many consecutive integers $>n$ can be represented as such a sum? Is it true
that, for any $c>0$ at least $cn$ such integers are possible (for sufficiently large $n$)?
-/
@[category research open, AMS 5 11]
theorem erdos_356.variants.consecutive : answer(sorry) ↔
    ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in Filter.atTop,
      ∃ (k : ℕ) (a : ℕ → ℤ), IsAdmissible n k a ∧
        ∃ t : ℤ, (n : ℤ) < t ∧
          ∀ j : ℕ, (j : ℝ) < c * n → t + j ∈ consecutiveSums k a := by
  sorry

end Erdos356
