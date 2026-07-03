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

/-!
# Conjectures associated with a

a: $a(n) = \text{least } k \text{ such that } \sqrt{k^2 \operatorname{XOR} (k+1)^2} = 2n+1$,
$a(n) = -1 \text{ if there is no such } k$.
This is equivalent to finding the smallest $k \in \mathbb{N}$
such that $k^2 \oplus (k+1)^2 = (2n+1)^2$.
We use the set infimum ($\operatorname{sInf}$) to denote the least element
of the set of natural numbers satisfying the condition.
Since Mathlib's `sInf` on a subset of `ℕ` gives a result in `ℕ`, this definition
is only completely faithful to the OEIS when the set is non-empty.
The OEIS definition implies that the set of k's is non-empty for all n.

*References:*
- [A224515](https://oeis.org/A224515)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA224515


open Nat Set

/--
a: $a(n) = \text{least } k \text{ such that } \sqrt{k^2 \operatorname{XOR} (k+1)^2} = 2n+1$,
$a(n) = -1 \text{ if there is no such } k$.
This is equivalent to finding the smallest $k \in \mathbb{N}$
such that $k^2 \oplus (k+1)^2 = (2n+1)^2$.
We use the set infimum ($\operatorname{sInf}$) to denote the least element
of the set of natural numbers satisfying the condition.
Since Mathlib's `sInf` on a subset of `ℕ` gives a result in `ℕ`, this definition
is only completely faithful to the OEIS when the set is non-empty.
The OEIS definition implies that the set of k's is non-empty for all n.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- The term (2*n + 1)^2 is the target value.
  let target_sq : ℕ := (2 * n + 1) ^ 2
  -- Define the set of candidate k's.
  sInf { k : ℕ | Nat.xor (k ^ 2) ((k + 1) ^ 2) = target_sq }


@[category API, AMS 11]
lemma A224515_eq (n val : ℕ) (h_in : Nat.xor (val ^ 2) ((val + 1) ^ 2) = (2 * n + 1) ^ 2)
  (h_min : ∀ k < val, Nat.xor (k ^ 2) ((k + 1) ^ 2) ≠ (2 * n + 1) ^ 2) : a n = val := by
  unfold a
  dsimp only
  refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt ⟨val, h_in⟩ ?_ ?_
  · intro a ha
    by_contra h
    exact h_min a (by omega) ha
  · intro w hw
    exact ⟨val, h_in, hw⟩

@[category test, AMS 11]
lemma a_zero : a 0 = 0 := by
  apply A224515_eq 0 0 (by decide)
  intro k hk; omega

@[category test, AMS 11]
lemma a_one : a 1 = 4 := by
  apply A224515_eq 1 4 (by decide)
  intro k hk; interval_cases k <;> decide

@[category test, AMS 11]
lemma a_two : a 2 = 3 := by
  apply A224515_eq 2 3 (by decide)
  intro k hk; interval_cases k <;> decide

@[category test, AMS 11]
lemma a_three : a 3 = 24 := by
  apply A224515_eq 3 24 (by decide)
  intro k hk; interval_cases k <;> decide

@[category test, AMS 11]
lemma a_four : a 4 = 23 := by
  apply A224515_eq 4 23 (by decide)
  intro k hk; interval_cases k <;> decide


/--
a: $a(n) = \text{least } k \text{ such that } \sqrt{k^2 \operatorname{XOR} (k+1)^2} = 2n+1$,
$a(n) = -1 \text{ if there is no such } k$.
This is equivalent to finding the smallest $k \in \mathbb{N}$
such that $k^2 \oplus (k+1)^2 = (2n+1)^2$.
We use the set infimum ($\operatorname{sInf}$) to denote the least element
of the set of natural numbers satisfying the condition.
Since Mathlib's `sInf` on a subset of `ℕ` gives a result in `ℕ`, this definition
is only completely faithful to the OEIS when the set is non-empty.
The OEIS definition implies that the set of k's is non-empty for all n.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/224515.wip.lean#L268"]
theorem exists_xor_sq_eq (n : ℕ) : ∃ k : ℕ, Nat.xor (k ^ 2) ((k + 1) ^ 2) = (2 * n + 1) ^ 2 := by
    sorry

end OeisA224515
