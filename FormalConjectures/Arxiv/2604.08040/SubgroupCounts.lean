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
# Group structure via subgroup counts

*Reference:* [arxiv/2604.08040](https://arxiv.org/abs/2604.08040)
**Group Structure via Subgroup Counts**
by *Angsuman Das, Hiranya Kishore Dey, Khyati Sharma*

For a finite group $G$, write $\mathrm{cyc}(G)$ for the number of cyclic subgroups and
$t = \pi(G)$ for the number of distinct primes dividing $|G|$. Small $\mathrm{cyc}(G)$
relative to $2^t$ forces structure: nilpotency below $5 \cdot 2^{t-2}$, supersolvability
below $2^{t+1}$. Conjecture 5.5 asks for the solvability threshold.
-/

namespace Arxiv.«2604.08040»

variable (G : Type*) [Group G] [Fintype G]

/-- $\mathrm{cyc}(G)$, the number of cyclic subgroups of `G`. -/
noncomputable def cyc : ℕ := Nat.card {H : Subgroup G // IsCyclic H}

/-- $\pi(G)$, the number of distinct primes dividing `|G|`. -/
noncomputable def numPrimeFactors : ℕ := (Fintype.card G).primeFactors.card

/--
**Conjecture 5.5 (Das-Dey-Sharma, 2026).** If a finite group `G` satisfies
$\mathrm{cyc}(G) < 2^{\pi(G)+2}$ then `G` is solvable.
-/
@[category research open, AMS 20]
theorem solvable_of_cyc_lt :
    answer(sorry) ↔ ∀ (G : Type) [Group G] [Fintype G],
      cyc G < 2 ^ (numPrimeFactors G + 2) → IsSolvable G := by
  sorry

/--
**Theorem 3.1.** Below $5 \cdot 2^{t-2}$ cyclic subgroups the group is nilpotent.
-/
@[category research solved, AMS 20]
theorem nilpotent_of_cyc_lt (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) :
    Group.IsNilpotent G := by
  sorry

/--
**Theorem 4.2.** Below $2^{t+1}$ cyclic subgroups the group is supersolvable.

Stated here as solvability, which supersolvability implies, since Mathlib has no
`IsSupersolvable`.
-/
@[category research solved, AMS 20]
theorem solvable_of_cyc_lt_two_pow_succ (h : cyc G < 2 ^ (numPrimeFactors G + 1)) :
    IsSolvable G := by
  sorry

/-- The alternating group on five letters has order $60 = 2^2 \cdot 3 \cdot 5$. -/
@[category test, AMS 20]
theorem card_alternatingGroup_fin_five :
    Fintype.card (alternatingGroup (Fin 5)) = 60 := by
  rw [← Nat.card_eq_fintype_card, ← Nat.mul_left_cancel_iff (by norm_num : 0 < 2),
      two_mul_nat_card_alternatingGroup, Nat.card_perm]
  norm_num [Fintype.card_fin]

/-- The alternating group on five letters has exactly $32$ cyclic subgroups: the trivial one,
$15$ of order $2$, $10$ of order $3$ and $6$ of order $5$. -/
@[category test, AMS 20]
theorem cyc_alternatingGroup_five : cyc (alternatingGroup (Fin 5)) = 32 := by
  sorry

/-- $A_5$ is where the bound bites. It has $\pi = 3$ and $\mathrm{cyc} = 32 = 2^{3+2}$, so it
misses the hypothesis by one and stays consistent with the conjecture despite being insoluble.
Any threshold above $2^{t+2}$ would be refuted by it. -/
@[category test, AMS 20]
theorem not_cyc_alternatingGroup_five_lt :
    ¬ cyc (alternatingGroup (Fin 5)) < 2 ^ (numPrimeFactors (alternatingGroup (Fin 5)) + 2) := by
  rw [cyc_alternatingGroup_five]
  unfold numPrimeFactors
  rw [card_alternatingGroup_fin_five, show Nat.primeFactors 60 = {2, 3, 5} from by decide +kernel]
  norm_num

/-- The trivial group has one cyclic subgroup and no prime divisors, so the hypothesis holds
and the conclusion is immediate. -/
@[category test, AMS 20]
theorem cyc_punit : cyc PUnit = 1 := by
  rw [cyc, Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun H H' => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨⊥, inferInstance⟩⟩

end Arxiv.«2604.08040»
