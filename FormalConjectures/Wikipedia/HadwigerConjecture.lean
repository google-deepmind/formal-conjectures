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
# Hadwiger's conjecture (1943)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Hadwiger_conjecture_(graph_theory))
* [Ha43] Hadwiger, H. (1943). "Über eine Klassifikation der Streckenkomplexe."
  *Vierteljschr. Naturforsch. Ges. Zürich* 88, pp. 133--142.
* [Wa37] Wagner, K. (1937). "Über eine Eigenschaft der ebenen Komplexe." *Math. Ann.* 114,
  pp. 570--590.
* [RST93] Robertson, N., Seymour, P. and Thomas, R. (1993). "Hadwiger's conjecture for
  $K_6$-free graphs." *Combinatorica* 13, pp. 279--361.
* [Ko84] Kostochka, A. V. (1984). "Lower bound of the Hadwiger number of graphs by their
  average degree." *Combinatorica* 4, pp. 307--316.
* [DP21] Delcourt, M. and Postle, L. (2021). "Reducing linear Hadwiger's conjecture to
  coloring small graphs." [arXiv:2108.01633](https://arxiv.org/abs/2108.01633)
* [Se16] Seymour, P. (2016). "Hadwiger's conjecture." In *Open Problems in Mathematics*,
  Springer, pp. 417--437.
-/

open SimpleGraph

namespace HadwigerConjecture

/-- The **Hadwiger number** `h(G)`: the largest `k` such that `K_k` is a minor of `G`. -/
noncomputable def hadwigerNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sSup {k | (completeGraph (Fin k)).IsMinor G}

/--
**Hadwiger's conjecture (1943).**

Every finite graph $G$ with chromatic number $\chi(G) \ge k$ has the complete graph $K_k$ as a
minor. Equivalently, $\chi(G) \le h(G)$ where $h(G)$ is the Hadwiger number.
-/
@[category research open, AMS 5]
theorem hadwiger_conjecture :
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ),
      (k : ℕ∞) ≤ G.chromaticNumber → (completeGraph (Fin k)).IsMinor G := by
  sorry

/--
**The cases $k \le 4$ (Hadwiger 1943; Dirac).**

The conjecture holds for $k \le 4$: graphs with no $K_4$ minor are series–parallel and hence
$3$-colourable.

*Reference:* [Ha43].
-/
@[category research solved, AMS 5]
theorem hadwiger_conjecture.variants.le_four
    {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4)
    (h : (k : ℕ∞) ≤ G.chromaticNumber) : (completeGraph (Fin k)).IsMinor G := by
  sorry

/--
**The case $k = 5$ (Wagner 1937; equivalent to the four colour theorem).**

Wagner showed that the case $k = 5$ is equivalent to the four colour theorem, which was proved
by Appel and Haken (1976) and Robertson, Sanders, Seymour and Thomas (1997).

*Reference:* [Wa37].
-/
@[category research solved, AMS 5, formal_proof using other_system at
"https://github.com/rocq-community/fourcolor"]
theorem hadwiger_conjecture.variants.five
    {V : Type} [Fintype V] (G : SimpleGraph V)
    (h : (5 : ℕ∞) ≤ G.chromaticNumber) : (completeGraph (Fin 5)).IsMinor G := by
  sorry

/--
**The case $k = 6$ (Robertson–Seymour–Thomas 1993).**

*Reference:* [RST93].
-/
@[category research solved, AMS 5]
theorem hadwiger_conjecture.variants.six
    {V : Type} [Fintype V] (G : SimpleGraph V)
    (h : (6 : ℕ∞) ≤ G.chromaticNumber) : (completeGraph (Fin 6)).IsMinor G := by
  sorry

/--
**The linear Hadwiger conjecture.**

There is a constant $C$ such that every graph with no $K_k$ minor is $Ck$-colourable
(see [DP21], [Ko84]).
-/
@[category research open, AMS 5]
theorem hadwiger_conjecture.variants.linear :
    ∃ C : ℕ, ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ),
      ¬ (completeGraph (Fin k)).IsMinor G → G.chromaticNumber ≤ C * k := by
  sorry

/--
**Kostochka / Thomason (1984): $O(k\sqrt{\log k})$ colours.**

There is a constant $C$ such that every graph with no $K_k$ minor ($k \ge 2$) has chromatic
number at most $C k \sqrt{\log k}$.

*Reference:* [Ko84].
-/
@[category research solved, AMS 5]
theorem hadwiger_conjecture.variants.kostochka_thomason :
    ∃ C : ℝ, 0 < C ∧ ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ), 2 ≤ k →
      ¬ (completeGraph (Fin k)).IsMinor G →
      (G.chromaticNumber.toNat : ℝ) ≤ C * k * Real.sqrt (Real.log k) := by
  sorry

/--
**The cases $k \le 1$.**

`K_0` is a minor of every graph (empty family of branch sets), and `K_1` is a minor of every
graph with a vertex, which is guaranteed by $\chi(G) \ge 1$.
-/
@[category test, AMS 5]
theorem hadwiger_conjecture.variants.le_one
    {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 1)
    (h : (k : ℕ∞) ≤ G.chromaticNumber) : (completeGraph (Fin k)).IsMinor G := by
  interval_cases k
  · exact ⟨fun i => Fin.elim0 i, ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩⟩
  · -- `χ(G) ≥ 1` forces a vertex; its singleton is a `K₁`-model.
    have hV : Nonempty V := by
      by_contra hV
      rw [not_nonempty_iff] at hV
      have : G.chromaticNumber = 0 := chromaticNumber_eq_zero_of_isEmpty
      rw [this] at h
      exact absurd h (by simp)
    obtain ⟨v⟩ := hV
    refine ⟨fun _ => {v}, ⟨fun _ => Set.singleton_nonempty v, fun _ => ?_,
      fun i j hij => absurd (Subsingleton.elim i j) hij, fun i j hij => ?_⟩⟩
    · exact (isMinorModel_singleton G).connected v
    · exact absurd (Subsingleton.elim i j) hij.ne

/--
**The case $k = 2$.**

A graph with chromatic number at least $2$ has an edge, and the two endpoints of an edge form
a $K_2$-model.
-/
@[category test, AMS 5]
theorem hadwiger_conjecture.variants.two
    {V : Type} [Fintype V] (G : SimpleGraph V)
    (h : (2 : ℕ∞) ≤ G.chromaticNumber) : (completeGraph (Fin 2)).IsMinor G := by
  -- `χ(G) ≥ 2` forces an edge: otherwise `G = ⊥` is `1`-colourable.
  obtain ⟨u, v, huv⟩ : ∃ u v, G.Adj u v := by
    by_contra hno
    push Not at hno
    have hbot : G = ⊥ := by
      ext a b
      simp [hno a b]
    have h1 : G.chromaticNumber ≤ 1 := by
      subst hbot
      exact_mod_cast Colorable.chromaticNumber_le ⟨⟨fun _ => 0, fun h => by simp at h⟩⟩
    exact absurd (h.trans h1) (by decide)
  refine ⟨fun i => if i = 0 then {u} else {v}, ?_, ?_, ?_, ?_⟩
  · intro i
    split <;> exact Set.singleton_nonempty _
  · intro i
    by_cases hi : i = 0
    · rw [if_pos hi]; exact (isMinorModel_singleton G).connected u
    · rw [if_neg hi]; exact (isMinorModel_singleton G).connected v
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact G.ne_of_adj huv
    · exact (G.ne_of_adj huv).symm
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact huv
    · exact huv.symm

end HadwigerConjecture
