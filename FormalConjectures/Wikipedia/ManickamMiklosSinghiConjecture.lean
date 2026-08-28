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
# The Manickam–Miklós–Singhi conjecture (1988)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Manickam%E2%80%93Mikl%C3%B3s%E2%80%93Singhi_conjecture)
* [MM88] Manickam, N. and Miklós, D. (1988). "On the number of nonnegative partial sums of a
  nonnegative sum." *Colloq. Math. Soc. János Bolyai* 52, pp. 385--392.
* [MS88] Manickam, N. and Singhi, N. M. (1988). "First distribution invariants and EKR theorems."
  *J. Combin. Theory Ser. A* 48, pp. 91--103.
* [CSS14] Chowdhury, A., Sarkis, G. and Shahriari, S. (2014). "The Manickam–Miklós–Singhi
  conjectures for sets and vector spaces." *J. Combin. Theory Ser. A* 128, pp. 84--103.
* [Po15] Pokrovskiy, A. (2015). "A linear bound on the Manickam–Miklós–Singhi conjecture."
  *J. Combin. Theory Ser. A* 133, pp. 280--306. [arXiv:1308.2176](https://arxiv.org/abs/1308.2176)
-/

open Finset

namespace ManickamMiklosSinghiConjecture

/-- The number of `k`-element subsets of `Fin n` on which the real weights `x` have
nonnegative sum. -/
noncomputable def nonnegSubsetCount (n k : ℕ) (x : Fin n → ℝ) : ℕ :=
  ((univ : Finset (Fin n)).powersetCard k).filter (fun S => 0 ≤ ∑ i ∈ S, x i) |>.card

/--
**The Manickam–Miklós–Singhi conjecture (1988).**

If $n \ge 4k$ and $x_1, \dots, x_n$ are real numbers with $x_1 + \dots + x_n = 0$, then at least
$\binom{n-1}{k-1}$ of the $k$-element subsets $S \subseteq \{1, \dots, n\}$ have
$\sum_{i \in S} x_i \ge 0$. (The bound is attained by $x = (n-1, -1, \dots, -1)$; the
condition $n \ge 4k$ cannot be weakened to $n \ge 3k + 1$ in general.)
-/
@[category research open, AMS 5]
theorem manickam_miklos_singhi_conjecture : answer(sorry) ↔
    ∀ (n k : ℕ), 1 ≤ k → 4 * k ≤ n → ∀ x : Fin n → ℝ, ∑ i, x i = 0 →
      (n - 1).choose (k - 1) ≤ nonnegSubsetCount n k x := by
  sorry

/--
**Pokrovskiy (2015): the conjecture holds for $n \ge C k$ with an absolute constant $C$.**

Pokrovskiy proved this with $C = 10^{46}$, the first bound linear in $k$.

*Reference:* [Po15].
-/
@[category research solved, AMS 5]
theorem manickam_miklos_singhi_conjecture.variants.pokrovskiy :
    ∃ C : ℕ, ∀ (n k : ℕ), 1 ≤ k → C * k ≤ n → ∀ x : Fin n → ℝ, ∑ i, x i = 0 →
      (n - 1).choose (k - 1) ≤ nonnegSubsetCount n k x := by
  sorry

/--
**Chowdhury–Sarkis–Shahriari (2014): the conjecture holds for $n \ge 8k^2$.**

*Reference:* [CSS14].
-/
@[category research solved, AMS 5]
theorem manickam_miklos_singhi_conjecture.variants.quadratic (n k : ℕ) (hk : 1 ≤ k)
    (hn : 8 * k ^ 2 ≤ n) (x : Fin n → ℝ) (hx : ∑ i, x i = 0) :
    (n - 1).choose (k - 1) ≤ nonnegSubsetCount n k x := by
  sorry

/--
**The case `k = 1`.**

With $k = 1$ the claim is that some $x_i$ is nonnegative, which is immediate since the $x_i$
sum to $0$ (and $n \ge 4 > 0$, so there is at least one $x_i$).
-/
@[category research solved, AMS 5]
theorem manickam_miklos_singhi_conjecture.variants.one (n : ℕ) (hn : 4 ≤ n) (x : Fin n → ℝ)
    (hx : ∑ i, x i = 0) :
    (n - 1).choose 0 ≤ nonnegSubsetCount n 1 x := by
  rw [Nat.choose_zero_right]
  -- Some `x i` is nonnegative: otherwise the total sum would be negative.
  have hne : (univ : Finset (Fin n)).Nonempty := by
    have : NeZero n := ⟨by omega⟩
    exact univ_nonempty
  obtain ⟨i, hi⟩ : ∃ i, 0 ≤ x i := by
    by_contra h
    push Not at h
    have : ∑ i, x i < 0 := Finset.sum_neg (fun i _ => h i) hne
    linarith
  -- The singleton `{i}` is a `1`-subset with nonnegative sum.
  refine Finset.card_pos.mpr ⟨{i}, ?_⟩
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  exact ⟨⟨Finset.subset_univ _, Finset.card_singleton i⟩, by simpa using hi⟩

end ManickamMiklosSinghiConjecture
