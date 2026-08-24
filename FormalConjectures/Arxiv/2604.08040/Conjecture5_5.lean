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

*Reference:* [arXiv:2604.08040v1](https://arxiv.org/abs/2604.08040v1)
**Group Structure via Subgroup Counts**
by *Angsuman Das, Hiranya Kishore Dey, Khyati Sharma* (2026)

For a finite group $G$, let $\mathrm{cyc}(G)$ denote the number of cyclic subgroups of $G$,
and let $t = \pi(G)$ denote the number of distinct prime divisors of $|G|$.

The paper establishes several structural results of the form
"if $\mathrm{cyc}(G)$ or $\mathrm{sub}(G)$ is small relative to $2^t$, then $G$
has a strong structural property":

* $\mathrm{cyc}(G) < 5 \cdot 2^{t-2} \implies G$ is nilpotent (Theorem 3.1)
* $\mathrm{cyc}(G) < 2^{t+1} \implies G$ is supersolvable (Theorem 4.2)
* $\mathrm{sub}(G) < 59 \cdot 2^{t-3} \implies G$ is solvable (Theorem 5.3)

**Conjecture 5.5** proposes the analogue for solvability via cyclic subgroup count:
if $\mathrm{cyc}(G) < 2^{t+2}$, then $G$ is solvable.

* **In-Paper Location:** Conjecture 5.5, Section 5 "Solvability of a group from $\mathrm{sub}(G)$"
  ([PDF page 15](https://arxiv.org/pdf/2604.08040v1#page=15))
* **OpenConjecture ID:** 1512
-/

namespace Arxiv.«2604.08040»

variable (G : Type*) [Group G] [Fintype G]

/--
The number of cyclic subgroups of a finite group `G`.
-/
noncomputable def cyc : ℕ :=
  Nat.card {H : Subgroup G // IsCyclic H}

/--
The number of distinct prime divisors of the order of `G`.

This is $\pi(G)$ in the notation of the paper.
-/
noncomputable def numPrimeFactors : ℕ :=
  (Fintype.card G).primeFactors.card

/--
**Conjecture 5.5** (Das, Dey, Sharma 2026):
If a finite group `G` satisfies $\mathrm{cyc}(G) < 2^{t+2}$, where $t = \pi(G)$ is the
number of distinct prime divisors of $|G|$, then `G` is solvable.
-/
@[category research open, AMS 20]
theorem solvable_of_cyc_lt :
    answer(sorry) ↔ ∀ (G : Type) [Group G] [Fintype G],
      cyc G < 2 ^ (numPrimeFactors G + 2) → Group.IsSolvable G := by
  sorry

/--
**Theorem 3.1.** Below $5 \cdot 2^{t-2}$ cyclic subgroups, the group is nilpotent.
-/
@[category research solved, AMS 20]
theorem nilpotent_of_cyc_lt (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) :
    Group.IsNilpotent G := by
  sorry

/--
**Theorem 4.2.** Below $2^{t+1}$ cyclic subgroups, the group is supersolvable.

Stated here as solvability, which supersolvability implies, since Mathlib does not
currently have a standalone `IsSupersolvable` class.
-/
@[category research solved, AMS 20]
theorem solvable_of_cyc_lt_two_pow_succ (h : cyc G < 2 ^ (numPrimeFactors G + 1)) :
    Group.IsSolvable G := by
  sorry

/- ## Sharpness & Test cases -/

/-- The alternating group on five letters has order $60 = 2^2 \cdot 3 \cdot 5$. -/
@[category test, AMS 20]
theorem card_alternatingGroup_fin_five :
    Fintype.card (alternatingGroup (Fin 5)) = 60 := by
  rw [← Nat.card_eq_fintype_card, ← Nat.mul_left_cancel_iff (by norm_num : 0 < 2),
      two_mul_nat_card_alternatingGroup, Nat.card_perm]
  norm_num [Fintype.card_fin]

/--
The alternating group on five letters has exactly $32$ cyclic subgroups: the trivial one,
$15$ of order $2$, $10$ of order $3$ and $6$ of order $5$.
-/
@[category test, AMS 20]
theorem cyc_alternatingGroup_five : cyc (alternatingGroup (Fin 5)) = 32 := by
  sorry

/--
$A_5$ is the sharpness witness: it has $\pi(A_5) = 3$ and $\mathrm{cyc}(A_5) = 32 = 2^{3+2}$,
so it misses the strict inequality $\mathrm{cyc}(G) < 2^{t+2}$ by exactly $1$.
This confirms $A_5$ is consistent with Conjecture 5.5 despite being non-solvable.
-/
@[category test, AMS 20]
theorem not_cyc_alternatingGroup_five_lt :
    ¬ cyc (alternatingGroup (Fin 5)) < 2 ^ (numPrimeFactors (alternatingGroup (Fin 5)) + 2) := by
  rw [cyc_alternatingGroup_five]
  unfold numPrimeFactors
  rw [card_alternatingGroup_fin_five, show Nat.primeFactors 60 = {2, 3, 5} from by decide +kernel]
  norm_num

/--
The trivial group has exactly one cyclic subgroup (itself).
-/
@[category test, AMS 20]
theorem cyc_punit : cyc PUnit = 1 := by
  rw [cyc, Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun H H' => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨⊥, inferInstance⟩⟩

/--
The trivial group has zero prime divisors.
-/
@[category test, AMS 20]
theorem numPrimeFactors_trivial : numPrimeFactors PUnit = 0 := by
  simp [numPrimeFactors]

end Arxiv.«2604.08040»
