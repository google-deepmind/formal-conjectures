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
# Scholz conjecture on addition chains

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Scholz_conjecture)
- [MathWorld](https://mathworld.wolfram.com/ScholzConjecture.html)
- [Tall22](https://arxiv.org/abs/2210.13812) Amadou Tall. "The Scholz conjecture on addition
  chain is true for infinitely many integers with $\ell(2n) = \ell(n)$." _arXiv:2210.13812_ (2022).
  Also available as [ePrint 2023/020](https://eprint.iacr.org/2023/020).
- [OEIS A003313](https://oeis.org/A003313)
-/

namespace ScholzConjecture

local notation "ℓ(" n ")" => additionChainLength n

/--
The Scholz conjecture, also known as the Scholz-Brauer conjecture, asserts that
for every positive integer $n$, the addition-chain length of $2^n - 1$ is at most
$n - 1 + \ell(n)$.
-/
@[category research open, AMS 11 68]
theorem scholz_conjecture :
    answer(sorry) ↔ ∀ (n : ℕ), 0 < n → ℓ(2 ^ n - 1) ≤ n - 1 + ℓ(n) := by
  sorry

-- TODO(eyang07): add solved variants. See Wikipedia reference.

/-- `7` is the first value where the doubling bound is not sharp: it gives `ℓ(7) ≥ 3`, and no
four-entry chain ends at `7`. Every entry of such a chain lies strictly between `1` and `7`, so
there are only finitely many to rule out. -/
@[category API, AMS 11 68]
private lemma three_notMem_additionChainSteps_seven : 3 ∉ additionChainSteps 7 := by
  rintro ⟨c, ⟨hhead, hsorted, hsum⟩, hlast, hlen⟩
  match c, hlen with
  | [w, x, y, z], _ =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hlast
    subst hhead; subst hlast
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at hsorted
    obtain ⟨⟨h1x, h1y, -⟩, ⟨hxy, hx7⟩, hy7, -⟩ := hsorted
    interval_cases x <;> interval_cases y <;> simp_all [List.mem_cons]

/-- The first few values of $\ell(n)$. See [OEIS A003313](https://oeis.org/A003313). -/
@[category test, AMS 11]
theorem additionChainLength_first_values :
    [ℓ(1), ℓ(2), ℓ(3), ℓ(4), ℓ(5), ℓ(6), ℓ(7), ℓ(8), ℓ(9), ℓ(10)] =
    [0, 1, 2, 2, 3, 3, 4, 3, 4, 4] := by
  have h1 : ℓ(1) = 0 := Nat.le_zero.mp (additionChainLength_le [1] (by decide) rfl rfl)
  have key : ∀ (n r : ℕ) (c : List ℕ), IsAdditionChain c → c.getLast? = some n →
      c.length = r + 1 → 2 ^ (r - 1) < n → 1 ≤ r → ℓ(n) = r := by
    intro n r c hc hlast hlen hlow hr
    refine le_antisymm (additionChainLength_le c hc hlast hlen) ?_
    have := lt_additionChainLength_of_two_pow_lt (additionChainSteps_nonempty c hc hlast hlen) hlow
    omega
  have h2 := key 2 1 [1, 2] (by decide) rfl rfl (by norm_num) (by norm_num)
  have h3 := key 3 2 [1, 2, 3] (by decide) rfl rfl (by norm_num) (by norm_num)
  have h4 := key 4 2 [1, 2, 4] (by decide) rfl rfl (by norm_num) (by norm_num)
  have h5 := key 5 3 [1, 2, 4, 5] (by decide) rfl rfl (by norm_num) (by norm_num)
  have h6 := key 6 3 [1, 2, 3, 6] (by decide) rfl rfl (by norm_num) (by norm_num)
  have h8 := key 8 3 [1, 2, 4, 8] (by decide) rfl rfl (by norm_num) (by norm_num)
  have h9 := key 9 4 [1, 2, 4, 8, 9] (by decide) rfl rfl (by norm_num) (by norm_num)
  have h10 := key 10 4 [1, 2, 4, 5, 10] (by decide) rfl rfl (by norm_num) (by norm_num)
  have h7 : ℓ(7) = 4 := by
    have hne := additionChainSteps_nonempty (n := 7) (r := 4) [1, 2, 3, 4, 7] (by decide) rfl rfl
    have hub := additionChainLength_le (n := 7) (r := 4) [1, 2, 3, 4, 7] (by decide) rfl rfl
    have hlb := lt_additionChainLength_of_two_pow_lt (n := 7) (r := 2) hne (by norm_num)
    have hne3 : ℓ(7) ≠ 3 := fun h => three_notMem_additionChainSteps_seven (h ▸ Nat.sInf_mem hne)
    omega
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

end ScholzConjecture
