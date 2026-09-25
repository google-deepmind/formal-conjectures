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
# Erdős Problem 54

*References:*
- [erdosproblems.com/54](https://www.erdosproblems.com/54)
- [BuEr85] Burr, S. A. and Erdős, P., *A Ramsey-type property in additive number theory*.
  Glasgow Math. J. (1985), 5-10.
- [CFP21] Conlon, D., Fox, J. and Pham, H. T., *Subset sums, completeness and colorings*.
  [arXiv:2104.14766](https://arxiv.org/abs/2104.14766) (2021).
- [Er95] Erdős, Paul, *Some of my favourite problems in number theory, combinatorics, and
  geometry*. Resenhas (1995), 165-186.
-/

@[expose] public section

open Filter Set

namespace Erdos54

/-- A set `A` of natural numbers is *Ramsey `r`-complete* if, for every `r`-colouring of `A`,
every sufficiently large integer is a sum of distinct elements of `A` of the same colour. -/
def IsRamseyComplete (r : ℕ) (A : Set ℕ) : Prop :=
  ∀ f : ℕ → Fin r, ∀ᶠ n in atTop, ∃ i, n ∈ subsetSums (A ∩ f ⁻¹' {i})

/-- A Ramsey `r`-complete set is complete when `0 < r`. -/
@[category API, AMS 5 11]
theorem IsRamseyComplete.isAddComplete {r : ℕ} (hr : 0 < r) {A : Set ℕ}
    (hA : IsRamseyComplete r A) : IsAddComplete A := by
  filter_upwards [hA fun _ ↦ ⟨0, hr⟩] with n hn
  obtain ⟨_, hn⟩ := hn
  exact subsetSums_mono inter_subset_left hn

/--
A set of integers $A$ is Ramsey $2$-complete if, whenever $A$ is $2$-coloured, all sufficiently
large integers can be written as a monochromatic sum of elements of $A$.

Burr and Erdős [BuEr85] showed that there is $c > 0$ such that no Ramsey $2$-complete $A$ satisfies
$\lvert A\cap \{1,\ldots,N\}\rvert \leq c(\log N)^2$ for all large $N$, and that there is a
Ramsey $2$-complete $A$ with $\lvert A\cap \{1,\ldots,N\}\rvert < (2\log_2 N)^3$ for all large $N$.
Improve either of these bounds.

Resolved by Conlon, Fox, and Pham [CFP21], who constructed a Ramsey $2$-complete $A$ with
$\lvert A\cap \{1,\ldots,N\}\rvert \ll (\log N)^2$. This matches the lower bound up to a constant.
-/
@[category research solved, AMS 5 11]
theorem erdos_54 : ∃ A : Set ℕ, IsRamseyComplete 2 A ∧
    (fun N : ℕ ↦ ((A ∩ Icc 1 N).ncard : ℝ)) =O[atTop] (fun N : ℕ ↦ Real.log N ^ 2) := by
  sorry

/--
Burr and Erdős [BuEr85]: there is $c > 0$ such that every Ramsey $2$-complete $A$ satisfies
$\lvert A\cap \{1,\ldots,N\}\rvert > c(\log N)^2$ for infinitely many $N$.
-/
@[category research solved, AMS 5 11]
theorem erdos_54.variants.lower : ∃ c > (0 : ℝ), ∀ A : Set ℕ, IsRamseyComplete 2 A →
    ∃ᶠ N : ℕ in atTop, c * Real.log N ^ 2 < (A ∩ Icc 1 N).ncard := by
  sorry

/--
Burr and Erdős [BuEr85]: there is a Ramsey $2$-complete $A$ such that
$\lvert A\cap \{1,\ldots,N\}\rvert < (2\log_2 N)^3$ for all large $N$.
-/
@[category research solved, AMS 5 11]
theorem erdos_54.variants.upper : ∃ A : Set ℕ, IsRamseyComplete 2 A ∧
    ∀ᶠ N : ℕ in atTop, ((A ∩ Icc 1 N).ncard : ℝ) < (2 * Real.logb 2 N) ^ 3 := by
  sorry

end Erdos54
