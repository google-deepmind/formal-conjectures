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
# Znám's Problem and the Odd Znám Question

Štefan Znám (1972) asked which finite sets $S = \{n_1, \dots, n_k\}$ of integers greater than $1$
have the property that every $x \in S$ properly divides $1 + \prod_{y \in S \setminus \{x\}} y$.
Ladislav Skula (1975) proved that no solution exists for $k < 5$, Jaroslav Janák and Skula (1978)
showed that only finitely many solutions exist for each fixed $k$ (OEIS A075441), and Qi Sun (1983)
constructed at least one solution for every $k \ge 5$. Whether any proper Znám set consists
entirely of odd integers remains open.

*References:*
- [Wikipedia: Znám's problem](https://en.wikipedia.org/wiki/Zn%C3%A1m%27s_problem)
- [OEIS A075441](https://oeis.org/A075441)
- L. Skula, *On a problem of Znám*, Acta Fac. Rerum Natur. Univ. Comenian. Math. **32** (1975),
  87–90.
- J. Janák and L. Skula, *On the integers $x_i$ for which
  $x_i \mid x_1 \cdots x_{i-1} x_{i+1} \cdots x_n + 1$*, Math. Slovaca **28** (1978), no. 3,
  305–310.
- Q. Sun, *On a problem of Š. Znám*, Sichuan Daxue Xuebao (1983), no. 4, 9–12.
-/

@[expose] public section

namespace ZnamsProblem

/-- A nonempty finite set $S \subseteq \mathbb{N}$ of integers $> 1$ is a proper Znám solution if
each $x \in S$ properly divides $1 + \prod_{y \in S \setminus \{x\}} y$. -/
def IsProperZnamSet (S : Finset ℕ) : Prop :=
  S.Nonempty ∧ (∀ x ∈ S, 1 < x) ∧
    ∀ x ∈ S, x ∣ ((S.erase x).prod id + 1) ∧ x < (S.erase x).prod id + 1

instance instDecidableIsProperZnamSet (S : Finset ℕ) :
    Decidable (IsProperZnamSet S) := by
  unfold IsProperZnamSet
  infer_instance

/-- No singleton $\{a\}$ satisfies `IsProperZnamSet`, so every proper Znám set has cardinality at
least $2$. -/
@[category API, AMS 11]
theorem two_le_card_of_isProperZnamSet {S : Finset ℕ} (hS : IsProperZnamSet S) :
    2 ≤ S.card := by
  rcases hS with ⟨hne, hgt1, hdiv⟩
  by_contra hlt
  have hcard1 : S.card = 1 := by
    have hpos : 0 < S.card := Finset.card_pos.mpr hne
    omega
  rcases Finset.card_eq_one.mp hcard1 with ⟨a, rfl⟩
  have ha1 : 1 < a := hgt1 a (Finset.mem_singleton_self a)
  have ha2 : a < 2 := by simpa using (hdiv a (Finset.mem_singleton_self a)).2
  omega

/-- No pair $\{a, b\}$ of cardinality $2$ satisfies `IsProperZnamSet`, so every proper Znám set has
cardinality at least $3$. -/
@[category API, AMS 11]
theorem three_le_card_of_isProperZnamSet {S : Finset ℕ} (hS : IsProperZnamSet S) :
    3 ≤ S.card := by
  have h2 : 2 ≤ S.card := two_le_card_of_isProperZnamSet hS
  by_contra hlt
  have hcard2 : S.card = 2 := by omega
  rcases Finset.card_eq_two.mp hcard2 with ⟨a, b, hab, rfl⟩
  rcases hS with ⟨_, _, hdiv⟩
  have ha_mem : a ∈ ({a, b} : Finset ℕ) := Finset.mem_insert_self a {b}
  have hb_mem : b ∈ ({a, b} : Finset ℕ) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have herase_a : ({a, b} : Finset ℕ).erase a = {b} :=
    Finset.erase_insert (Finset.notMem_singleton.mpr hab)
  have herase_b : ({a, b} : Finset ℕ).erase b = {a} := by
    rw [Finset.pair_comm]
    exact Finset.erase_insert (Finset.notMem_singleton.mpr hab.symm)
  have hab1 : a < b + 1 := by simpa [herase_a] using (hdiv a ha_mem).2
  have hba1 : b < a + 1 := by simpa [herase_b] using (hdiv b hb_mem).2
  exact hab (by omega)

/-- Janák's length-$5$ set $\{2, 3, 11, 23, 31\}$ satisfies `IsProperZnamSet`. -/
@[category test, AMS 11]
theorem isProperZnamSet_janak : IsProperZnamSet {2, 3, 11, 23, 31} := by
  decide

/-- The second length-$5$ set $\{2, 3, 7, 47, 395\}$ satisfies `IsProperZnamSet`. -/
@[category test, AMS 11]
theorem isProperZnamSet_2_3_7_47_395 : IsProperZnamSet {2, 3, 7, 47, 395} := by
  decide

/-- The Sylvester prefix $\{2, 3, 7, 43\}$ fails `IsProperZnamSet` because
$43 = 2 \cdot 3 \cdot 7 + 1$ is not a proper divisor. -/
@[category test, AMS 11]
theorem not_isProperZnamSet_sylvester_four : ¬ IsProperZnamSet {2, 3, 7, 43} := by
  decide

/--
**Janák–Skula Finiteness Theorem** (1978): for every cardinality $k$, only finitely many finite
sets $S \subseteq \mathbb{N}$ of size $k$ satisfy `IsProperZnamSet S` (OEIS A075441).
-/
@[category research solved, AMS 11]
theorem znam_solutions_finite (k : ℕ) :
    {S : Finset ℕ | S.card = k ∧ IsProperZnamSet S}.Finite := by
  sorry

/--
**Skula–Sun Existence Characterization** (Skula 1975 for $k < 5$; Sun 1983 for $k \ge 5$): a proper
Znám set of cardinality $k$ exists if and only if $k \ge 5$.
-/
@[category research solved, AMS 11]
theorem znam_existence_iff_five_le (k : ℕ) :
    (∃ S : Finset ℕ, S.card = k ∧ IsProperZnamSet S) ↔ 5 ≤ k := by
  sorry

/--
**Odd Znám Question**: is there any proper Znám set $S$ consisting solely of odd integers?
-/
@[category research open, question, AMS 11]
theorem odd_znam_problem :
    ∃ S : Finset ℕ, IsProperZnamSet S ∧ ∀ x ∈ S, Odd x := by
  sorry

end ZnamsProblem
