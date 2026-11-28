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
# Erdős Problem 1011

*References:*
- [erdosproblems.com/1011](https://www.erdosproblems.com/1011)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97–109.
- [Go20] Goedgebeur, J.,
  [On minimal triangle-free 6-chromatic graphs](https://arxiv.org/abs/1707.07581).
  Journal of Graph Theory 93 (2020), 34–48.
  [Graph catalogue](https://houseofgraphs.org/TrianglefreeKChrom).
- K. Kitamura, [the five-colour threshold from order 80](https://github.com/KitaKen1/erdos-1011-lean/blob/c1a089df40579aa3cb1dc3f22c588834691d7176/lean-r5/R5Kernel/Final.lean#L6).
-/

@[expose] public section

namespace Erdos1011

open SimpleGraph

/-- Edge thresholds that force a triangle in every $n$-vertex graph of chromatic number at least
$r$. -/
def thresholds (r n : ℕ) : Set ℕ :=
  {m | ∀ G : SimpleGraph (Fin n),
    m ≤ G.edgeSet.ncard → r ≤ G.chromaticNumber → ¬ G.CliqueFree 3}

def erdos_1011.answer (r n : ℕ) : ℕ := by sorry

/--
Let $f_r(n)$ be minimal such that every graph on $n$ vertices with $\geq f_r(n)$ edges and
chromatic number $\geq r$ contains a triangle. Determine $f_r(n)$.
-/
@[category research open, question value, AMS 5]
theorem erdos_1011 (r n : ℕ) : IsLeast (thresholds r n) (erdos_1011.answer r n) := by
  sorry

/-- If $r>n$, no $n$-vertex graph has chromatic number at least $r$, so $f_r(n)=0$. -/
@[category test, AMS 5]
theorem threshold_of_lt {n r : ℕ} (h : n < r) : IsLeast (thresholds r n) 0 := by
  refine ⟨fun G _ hG ↦ ?_, fun _ _ ↦ Nat.zero_le _⟩
  have hcard : G.chromaticNumber ≤ (n : ℕ∞) := by
    simpa using G.chromaticNumber_le_card
  exact (h.not_ge (by exact_mod_cast hG.trans hcard)).elim

@[category API, AMS 5]
private lemma card_turanGraph_two (n : ℕ) : (turanGraph n 2).edgeFinset.card = n ^ 2 / 4 := by
  rw [card_edgeFinset_turanGraph]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
  obtain ⟨a, ha⟩ := Nat.odd_iff.mpr h
  rw [ha]
  have hs : (2 * a + 1) ^ 2 = 4 * (a ^ 2 + a) + 1 := by ring
  omega

/-- Turán's theorem gives $f_2(n)=\lfloor n^2/4\rfloor+1$ for $n\geq 2$. -/
@[category textbook, AMS 5]
theorem erdos_1011.variants.two {n : ℕ} (hn : 2 ≤ n) :
    IsLeast (thresholds 2 n) (n ^ 2 / 4 + 1) := by
  classical
  have ht := card_turanGraph_two n
  have bound (G : SimpleGraph (Fin n)) (h : G.CliqueFree 3) : G.edgeSet.ncard ≤ n ^ 2 / 4 := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset, ← ht, card_edgeFinset_turanGraph]
    simpa using h.card_edgeFinset_le (r := 2)
  constructor
  · intro G hm _ h
    exact (Nat.not_succ_le_self _) (hm.trans (bound G h))
  · intro m hm
    by_contra! h
    have he : (turanGraph n 2).edgeSet.ncard = n ^ 2 / 4 := by
      rwa [← coe_edgeFinset, Set.ncard_coe_finset]
    have hadj : (turanGraph n 2).Adj ⟨0, by omega⟩ ⟨1, by omega⟩ := by
      change (0 : ℕ) % 2 ≠ 1 % 2
      decide
    exact hm (turanGraph n 2) (by omega) (two_le_chromaticNumber_of_adj hadj)
      (turanGraph_cliqueFree (by decide : 0 < 2))

/-- Edges of a $72$-edge graph in the $22$-vertex catalogue of [Go20], listed once per edge. -/
private def edges : List (Fin 22 × Fin 22) :=
  [(1, 2), (2, 3), (0, 4), (1, 4), (3, 5), (4, 5), (0, 7), (3, 7), (4, 8),
    (6, 8), (7, 8), (1, 9), (3, 9), (6, 9), (0, 10), (2, 10), (5, 10), (8, 10),
    (9, 10), (0, 11), (2, 11), (6, 11), (1, 12), (5, 12), (7, 12), (11, 12), (1, 13),
    (5, 13), (6, 13), (7, 13), (0, 14), (3, 14), (6, 14), (12, 14), (0, 15), (1, 15),
    (3, 15), (8, 15), (0, 16), (2, 16), (5, 16), (6, 16), (3, 17), (4, 17), (6, 17),
    (10, 17), (12, 17), (2, 18), (5, 18), (6, 18), (7, 18), (15, 18), (0, 19), (2, 19),
    (8, 19), (9, 19), (12, 19), (13, 19), (4, 20), (9, 20), (11, 20), (13, 20), (14, 20),
    (15, 20), (16, 20), (1, 21), (8, 21), (11, 21), (14, 21), (16, 21), (17, 21), (18, 21)]

private abbrev baseGraph : SimpleGraph (Fin 22) :=
  fromRel fun x y ↦ (x, y) ∈ edges

private instance : DecidableRel baseGraph.Adj :=
  fun a b ↦ inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ edges ∨ (b, a) ∈ edges)))

@[category test, AMS 5]
private theorem repeatedColour (c : Fin 22 → BitVec 2) : ∃ e ∈ edges, c e.1 = c e.2 := by
  have h : edges.any (fun e ↦ c e.1 == c e.2) = true := by
    simp only [edges, List.any_cons, List.any_nil, Bool.or_false]
    bv_decide
  simpa using List.any_eq_true.mp h

set_option maxRecDepth 4000 in
@[category test, AMS 5]
private theorem baseChromatic : 5 ≤ baseGraph.chromaticNumber := by
  apply (le_chromaticNumber_iff_not_colorable (n := 5) (by decide)).2
  rintro ⟨c⟩
  obtain ⟨⟨a, b⟩, he, hab⟩ := repeatedColour (fun v ↦ BitVec.ofFin (c v))
  have hne : ∀ e ∈ edges, e.1 ≠ e.2 := by decide
  exact c.valid (show baseGraph.Adj a b from ⟨hne _ he, Or.inl he⟩) (congrArg BitVec.toFin hab)

/-- Identify each added vertex with vertex $0$, which has eight neighbours. -/
private def original {k : ℕ} (v : Fin (22 + k)) : Fin 22 :=
  if h : v.val < 22 then ⟨v.val, h⟩ else 0

private abbrev exampleGraph (k : ℕ) := baseGraph.comap (@original k)

private instance (k : ℕ) : DecidableRel (exampleGraph k).Adj :=
  fun a b ↦ inferInstanceAs (Decidable (baseGraph.Adj (original a) (original b)))

@[category test, AMS 5]
private theorem exampleChromatic (k : ℕ) : 5 ≤ (exampleGraph k).chromaticNumber := by
  let inc : baseGraph →g exampleGraph k :=
    ⟨Fin.castAdd k, by intro a b h; simpa [exampleGraph, original, comap_adj] using h⟩
  exact baseChromatic.trans (chromaticNumber_mono_of_hom inc)

set_option maxRecDepth 4000 in
@[category test, AMS 5]
private theorem baseTriangleFree :
    ∀ a b c : Fin 22, baseGraph.Adj a b → baseGraph.Adj a c → ¬ baseGraph.Adj b c := by
  decide +kernel

@[category test, AMS 5]
private theorem exampleTriangleFree (k : ℕ) : (exampleGraph k).CliqueFree 3 := by
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, _⟩ := is3Clique_iff.mp hs
  exact baseTriangleFree (original a) (original b) (original c) hab hac hbc

set_option maxRecDepth 10000 in
/-- At orders $22,23,24$ the witnesses have $72,80,88$ edges and avoid triangles. -/
@[category test, AMS 5]
theorem erdos_1011.variants.five_lower (k : Fin 3) {m : ℕ}
    (hm : m ∈ thresholds 5 (22 + k.val)) : 73 + 8 * k.val ≤ m := by
  have counts : ∀ i : Fin 3, (exampleGraph i.val).edgeFinset.card = 72 + 8 * i.val := by
    decide +kernel
  have he := counts k
  rw [← Set.ncard_coe_finset, coe_edgeFinset] at he
  by_contra! h
  exact hm (exampleGraph k.val) (by omega) (exampleChromatic k.val) (exampleTriangleFree k.val)

/--
Goedgebeur [Go20] enumerated the triangle-free $5$-chromatic graphs through order $24$ and
showed that a triangle-free $6$-chromatic graph needs at least $32$ vertices.
The maximum edge counts at orders $22,23,24$ are $72,80,88$, respectively.
-/
@[category research solved, AMS 5]
theorem erdos_1011.variants.five_upper :
    73 ∈ thresholds 5 22 ∧ 81 ∈ thresholds 5 23 ∧ 89 ∈ thresholds 5 24 := by
  sorry

/-- The thresholds $f_5(22),f_5(23),f_5(24)$ are $73,81,89$, respectively. -/
@[category research solved, AMS 5]
theorem erdos_1011.variants.five_small :
    IsLeast (thresholds 5 22) 73 ∧ IsLeast (thresholds 5 23) 81 ∧
      IsLeast (thresholds 5 24) 89 := by
  obtain ⟨h22, h23, h24⟩ := erdos_1011.variants.five_upper
  exact ⟨⟨h22, fun _ hm ↦ erdos_1011.variants.five_lower 0 hm⟩,
    ⟨h23, fun _ hm ↦ erdos_1011.variants.five_lower 1 hm⟩,
    ⟨h24, fun _ hm ↦ erdos_1011.variants.five_lower 2 hm⟩⟩

set_option linter.style.formal_proof_palomar false in
/-- For every $n \ge 47$, the least number of edges forcing a triangle in an $n$-vertex graph
of chromatic number at least five is $\lfloor (n-6)^2/4 \rfloor + 6$.
This extends Kitamura's five-colour theorem to orders $47$ through $79$. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/prabhavag/formal-maths/blob/4b2965cd05f301a1a30519019ecd7bc157936a12/results/erdos-1011-five-colour/lean/Proof/From47.lean#L143"]
theorem erdos_1011.variants.five_ge_47 {n : ℕ} (hn : 47 ≤ n) :
    IsLeast (thresholds 5 n) ((n - 6) ^ 2 / 4 + 6) := by
  sorry

end Erdos1011
