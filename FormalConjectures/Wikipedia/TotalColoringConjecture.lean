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
# The total colouring conjecture (Behzad 1965, Vizing 1968)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Total_coloring)
* [Be65] Behzad, M. (1965). *Graphs and their chromatic numbers.* Ph.D. thesis, Michigan State
  University.
* [Vi68] Vizing, V. G. (1968). "Some unsolved problems in graph theory."
  *Uspekhi Mat. Nauk* 23, pp. 117--134.
* [Ko96] Kostochka, A. V. (1996). "The total chromatic number of any multigraph with maximum
  degree five is at most seven." *Discrete Math.* 162, pp. 199--214.
* [MR98] Molloy, M. and Reed, B. (1998). "A bound on the total chromatic number."
  *Combinatorica* 18, pp. 241--280.
* [Yap96] Yap, H. P. (1996). *Total colourings of graphs.* Lecture Notes in Mathematics 1623,
  Springer.
-/

@[expose] public section

open SimpleGraph

namespace TotalColoringConjecture

/--
**The total colouring conjecture (Behzad 1965, Vizing 1968).**

Every finite simple graph $G$ has a total colouring with at most $\Delta(G) + 2$ colours, i.e.
$\chi''(G) \le \Delta(G) + 2$, where $\Delta(G)$ is the maximum degree.
-/
@[category research open, AMS 5]
theorem total_coloring_conjecture :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.totalChromaticNumber ≤ G.maxDegree + 2 := by
  sorry

/--
**Maximum degree at most `5` (Rosenfeld and Vijayaditya for $\Delta \le 3$; Kostochka for
$\Delta = 4, 5$).**

The conjecture holds for every graph of maximum degree at most $5$.

*References:* [Ko96], [Yap96].
-/
@[category research solved, AMS 5]
theorem total_coloring_conjecture.variants.maxDegree_le_five
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hΔ : G.maxDegree ≤ 5) :
    G.totalChromaticNumber ≤ G.maxDegree + 2 := by
  sorry

/-- Vertex `i` of `K_n` gets `2i` and edge `{i, j}` gets `i + j`, in `ZMod m`. -/
private def completeColor (m n : ℕ) : Fin n ⊕ (completeGraph (Fin n)).edgeSet → ZMod m
  | Sum.inl i => 2 * (i : ℕ)
  | Sum.inr e => Sym2.lift ⟨fun i j : Fin n => ((i : ℕ) : ZMod m) + (j : ℕ),
      fun _ _ => add_comm _ _⟩ (e : Sym2 (Fin n))

@[category API, AMS 5]
private theorem cast_inj {m n : ℕ} (hn : n ≤ m) {i j : Fin n}
    (h : ((i : ℕ) : ZMod m) = ((j : ℕ) : ZMod m)) : i = j := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (i.isLt.trans_le hn),
    Nat.mod_eq_of_lt (j.isLt.trans_le hn)] at h
  exact Fin.ext h

/-- For odd `m ≥ n`, `completeColor m n` is a total colouring of `K_n`. -/
@[category API, AMS 5]
private theorem isTotalColoring_completeColor {m n : ℕ} (hm : Odd m) (hn : n ≤ m) :
    (completeGraph (Fin n)).IsTotalColoring (completeColor m n) := by
  have h2 : IsUnit (2 : ZMod m) := by
    have := (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.2 hm)).isUnit
    rwa [ZMod.coe_unitOfCoprime, Nat.cast_ofNat] at this
  refine ⟨fun u v huv h => ?_, fun e f hef ⟨v, hve, hvf⟩ h => ?_, fun v e hve h => ?_⟩
  · simp only [completeColor] at h
    exact (top_adj u v).1 huv (cast_inj hn (h2.mul_left_cancel h))
  · obtain ⟨a, ha⟩ := Sym2.mem_iff_exists.1 hve
    obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 hvf
    simp only [completeColor, ha, hb, Sym2.lift_mk] at h
    have hab : a = b := cast_inj hn (add_left_cancel h)
    exact hef (Subtype.ext (by rw [ha, hb, hab]))
  · obtain ⟨a, ha⟩ := Sym2.mem_iff_exists.1 hve
    have hva : v ≠ a := by
      have := e.2
      rw [ha, mem_edgeSet] at this
      exact (top_adj v a).1 this
    simp only [completeColor, ha, Sym2.lift_mk, two_mul] at h
    exact hva (cast_inj hn (add_left_cancel h))

/--
**Complete graphs.**

The total chromatic number of $K_n$ is $n$ for odd $n$ and $n + 1$ for even $n$ (see [Yap96]),
so in particular the conjecture holds for complete graphs.
-/
@[category research solved, AMS 5]
theorem total_coloring_conjecture.variants.complete_graph (n : ℕ) :
    (completeGraph (Fin n)).totalChromaticNumber ≤ (completeGraph (Fin n)).maxDegree + 2 := by
  have hc := isTotalColoring_completeColor (m := 2 * (n / 2) + 1) (n := n)
    (odd_two_mul_add_one _) (by omega)
  have hv : ∀ a b : ZMod (2 * (n / 2) + 1), a ≠ b →
      (⟨a.val, ZMod.val_lt a⟩ : Fin (2 * (n / 2) + 1)) ≠ ⟨b.val, ZMod.val_lt b⟩ :=
    fun a b hab h => hab (ZMod.val_injective _ (congrArg Fin.val h))
  have hcol : (completeGraph (Fin n)).TotalColorable (2 * (n / 2) + 1) :=
    ⟨fun x => ⟨(completeColor _ n x).val, ZMod.val_lt _⟩,
      fun u v huv => hv _ _ (hc.1 u v huv), fun e f hef h => hv _ _ (hc.2.1 e f hef h),
      fun v e h => hv _ _ (hc.2.2 v e h)⟩
  refine (Nat.sInf_le hcol).trans ?_
  rw [maxDegree_top, Fintype.card_fin]
  omega

/--
**Molloy–Reed (1998): $\chi''(G) \le \Delta(G) + C$ for an absolute constant $C$.**

There is a constant $C$ (Molloy and Reed obtain $C = 10^{26}$) such that every graph satisfies
$\chi''(G) \le \Delta(G) + C$.

*Reference:* [MR98].
-/
@[category research solved, AMS 5]
theorem total_coloring_conjecture.variants.molloy_reed :
    ∃ C : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.totalChromaticNumber ≤ G.maxDegree + C := by
  sorry

/--
**Sanity check: the trivial bound.** Colouring all vertices and edges with distinct colours
shows $\chi''(G) \le |V| + |E|$; this is `SimpleGraph.totalChromaticNumber_le_card_add_card`.
-/
@[category test, AMS 5]
theorem totalChromaticNumber_le_card_add_card
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.totalChromaticNumber ≤ Fintype.card V + Fintype.card G.edgeSet :=
  G.totalChromaticNumber_le_card_add_card

end TotalColoringConjecture
