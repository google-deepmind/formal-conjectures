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
# Residual finiteness of hyperbolic groups

Is every hyperbolic group residually finite? Kapovich and Wise [KaWi00] proved that this question
is equivalent to asking whether every nontrivial hyperbolic group has a proper subgroup of finite
index. Both questions were answered negatively by an internal OpenAI model in September 2026
[OAI26a].

*References:*
- [BMS] G. Baumslag, A. G. Myasnikov and V. Shpilrain, *Open problems in combinatorial group
  theory*, Problem (H1),
  [online](https://shpilrain.ccny.cuny.edu/gworld/problems/probhyp.html).
- [Be04] M. Bestvina, *Questions in geometric group theory*, updated July 2004, Q 1.15,
  [pdf](https://www.math.utah.edu/~bestvina/eprints/questions-updated.pdf).
- [KaWi00] I. Kapovich and D. T. Wise, *The equivalence of some residual properties of
  word-hyperbolic groups*, J. Algebra 223 (2000), 562–583,
  [doi:10.1006/jabr.1999.8104](https://doi.org/10.1006/jabr.1999.8104).
- [OAI26a] OpenAI, *A torsion-free hyperbolic group that is not residually finite*. OpenAI Math
  Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/a-torsion-free-hyperbolic-group-that-is-not-residually-finite-September-23-2026/paper.pdf
-/

@[expose] public section

namespace HyperbolicGroupsResiduallyFinite

set_option linter.style.formal_proof_palomar false in
/--
Is every hyperbolic group residually finite?

This is Problem (H1)(a) in [BMS] and Q 1.15 in [Be04].

No. This was disproved by an internal OpenAI model in September 2026 [OAI26a], which constructs
a torsion-free hyperbolic group that is not residually finite. The
[Lean proof](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/Hyperbolic/Main.lean#L7)
of [OAI26a] defines hyperbolicity by uniformly thin geodesic triangles in a Cayley graph. That
definition is equivalent to `Group.IsHyperbolic`; the direction needed here is proved in
`ThinTriangles.isHyperbolic_of_wordHyperbolic`. The linked statement is
`hyperbolic_residuallyFinite.variants.thin_triangles`; see
`hyperbolic_residuallyFinite_of_thin_triangles`.
-/
@[category research solved, question, AMS 20, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/Hyperbolic/Main.lean#L7"]
theorem hyperbolic_residuallyFinite :
    ¬ ∀ (G : Type) [Group G] [Group.IsHyperbolic G], Group.ResiduallyFinite G := by
  sorry

/--
Does every nontrivial hyperbolic group have a proper subgroup of finite index?

This is Problem (H1)(b) in [BMS]. The trivial group has no proper subgroup, so we assume that
$G$ is nontrivial.

No. By [KaWi00] (see `hyperbolic_residuallyFinite_iff_exists_finiteIndex_ne_top`), this problem
is equivalent to `hyperbolic_residuallyFinite`, which was disproved in [OAI26a].
-/
@[category research solved, question, AMS 20]
theorem hyperbolic_exists_finiteIndex_ne_top :
    ¬ ∀ (G : Type) [Group G] [Group.IsHyperbolic G] [Nontrivial G],
      ∃ H : Subgroup G, H ≠ ⊤ ∧ H.FiniteIndex := by
  sorry

/--
Every hyperbolic group is residually finite if and only if every nontrivial hyperbolic group has a
proper subgroup of finite index.

This is the theorem of [KaWi00] that Problems (H1)(a) and (H1)(b) are equivalent.
-/
@[category research solved, AMS 20]
theorem hyperbolic_residuallyFinite_iff_exists_finiteIndex_ne_top :
    (∀ (G : Type) [Group G] [Group.IsHyperbolic G], Group.ResiduallyFinite G) ↔
      ∀ (G : Type) [Group G] [Group.IsHyperbolic G] [Nontrivial G],
        ∃ H : Subgroup G, H ≠ ⊤ ∧ H.FiniteIndex := by
  sorry

/- ## The thin-triangle statement of [OAI26a]

The definitions in `ThinTriangles` are copied from the Lean statement linked at
`hyperbolic_residuallyFinite`. There a group is hyperbolic if some finite set gives a connected
Cayley graph whose geodesic triangles are uniformly thin, measured on vertices. The lemmas below
prove that this implies `Group.IsHyperbolic`: thin triangles give the four-point condition for the
graph distance with constant `3δ + 1`, and the graph distance is the word metric. -/

namespace ThinTriangles

universe u

/-- No nonidentity element has finite order, as defined in [OAI26a]. -/
def TorsionFree (G : Type u) [Group G] : Prop :=
  ∀ (g : G) (n : ℕ), 0 < n → g ^ n = 1 → g = 1

/-- A shortest walk, as defined in [OAI26a]. -/
def Geodesic {V : Type u} (X : SimpleGraph V) {x y : V} (p : X.Walk x y) : Prop :=
  p.length = X.dist x y

/-- Each vertex of `p` is within `δ` of a vertex of `q` or `r`, as defined in [OAI26a]. -/
def SideThin {V : Type u} (X : SimpleGraph V) (δ : ℕ) {x y z : V}
    (p : X.Walk x y) (q : X.Walk y z) (r : X.Walk z x) : Prop :=
  ∀ a ∈ p.support, ∃ b, (b ∈ q.support ∨ b ∈ r.support) ∧ X.dist a b ≤ δ

/-- Hyperbolicity by uniformly thin geodesic triangles in a Cayley graph, as defined in
[OAI26a]. -/
def WordHyperbolic (G : Type u) [Group G] : Prop :=
  ∃ S : Set G, S.Finite ∧ (SimpleGraph.mulCayley S).Connected ∧
    ∃ δ : ℕ, ∀ (x y z : G)
      (p : (SimpleGraph.mulCayley S).Walk x y)
      (q : (SimpleGraph.mulCayley S).Walk y z)
      (r : (SimpleGraph.mulCayley S).Walk z x),
      Geodesic (SimpleGraph.mulCayley S) p →
      Geodesic (SimpleGraph.mulCayley S) q →
      Geodesic (SimpleGraph.mulCayley S) r →
      SideThin (SimpleGraph.mulCayley S) δ p q r ∧
      SideThin (SimpleGraph.mulCayley S) δ q r p ∧
      SideThin (SimpleGraph.mulCayley S) δ r p q

section Graph

variable {V : Type*} {X : SimpleGraph V}

/-- A vertex on a geodesic splits its length. -/
@[category API, AMS 20]
lemma dist_add_dist_of_geodesic (hX : X.Connected) {a b c : V} {p : X.Walk a b}
    (hp : Geodesic X p) (hc : c ∈ p.support) : X.dist a c + X.dist c b = X.dist a b := by
  classical
  refine le_antisymm ?_ hX.dist_triangle
  have h := congrArg SimpleGraph.Walk.length (p.take_spec hc)
  rw [SimpleGraph.Walk.length_append] at h
  have h1 := SimpleGraph.dist_le (p.takeUntil c hc)
  have h2 := SimpleGraph.dist_le (p.dropUntil c hc)
  rw [Geodesic] at hp
  omega

/-- The Gromov product of the endpoints of a geodesic is at most the distance to any of its
vertices: `(a | b)_w ≤ d(w, c)`. -/
@[category API, AMS 20]
lemma dist_add_dist_le_of_geodesic (hX : X.Connected) {a b c : V} {p : X.Walk a b}
    (hp : Geodesic X p) (hc : c ∈ p.support) (w : V) :
    X.dist w a + X.dist w b ≤ 2 * X.dist w c + X.dist a b := by
  have h1 := dist_add_dist_of_geodesic hX hp hc
  have h2 := hX.dist_triangle (u := w) (v := c) (w := a)
  have h3 := hX.dist_triangle (u := w) (v := c) (w := b)
  have h4 : X.dist c a = X.dist a c := SimpleGraph.dist_comm
  omega

/-- If geodesic triangles are `δ`-thin, then some vertex `c` of a geodesic from `a` to `b` satisfies
`d(w, c) ≤ (a | b)_w + 2δ + 1`. -/
@[category API, AMS 20]
lemma exists_dist_le_of_sideThin (hX : X.Connected) {δ : ℕ}
    (hthin : ∀ (x y z : V) (p : X.Walk x y) (q : X.Walk y z) (r : X.Walk z x),
      Geodesic X p → Geodesic X q → Geodesic X r → SideThin X δ p q r)
    {a b : V} (p : X.Walk a b) (hp : Geodesic X p) (w : V) :
    ∃ c ∈ p.support, 2 * X.dist w c + X.dist a b ≤ X.dist w a + X.dist w b + 4 * δ + 2 := by
  classical
  obtain ⟨q, hq⟩ := hX.exists_walk_length_eq_dist b w
  obtain ⟨r, hr⟩ := hX.exists_walk_length_eq_dist w a
  have hT := hthin a b w p q r hp hq hr
  have hex : ∃ i, ∃ e ∈ q.support, X.dist (p.getVert i) e ≤ δ :=
    ⟨p.length, b, q.start_mem_support, by simp [p.getVert_length]⟩
  obtain ⟨c, hc, ⟨f, hf, hcf⟩, ⟨e, he, hce⟩⟩ : ∃ c ∈ p.support,
      (∃ f ∈ r.support, X.dist c f ≤ δ) ∧ (∃ e ∈ q.support, X.dist c e ≤ δ + 1) := by
    obtain ⟨e, he, hje⟩ := Nat.find_spec hex
    rcases hj : Nat.find hex with _ | k
    · rw [hj, p.getVert_zero] at hje
      exact ⟨a, p.start_mem_support, ⟨a, r.end_mem_support, by simp⟩, ⟨e, he, by omega⟩⟩
    · have hk : ¬ ∃ e ∈ q.support, X.dist (p.getVert k) e ≤ δ :=
        Nat.find_min hex (by rw [hj]; exact Nat.lt_succ_self k)
      obtain ⟨f, hf | hf, hkf⟩ := hT _ (p.getVert_mem_support k)
      · exact absurd ⟨f, hf, hkf⟩ hk
      · refine ⟨p.getVert k, p.getVert_mem_support k, ⟨f, hf, hkf⟩, e, he, ?_⟩
        have hk1 : X.dist (p.getVert k) (p.getVert (k + 1)) ≤ 1 := by
          rcases lt_or_ge k p.length with hlt | hge
          · exact (SimpleGraph.dist_eq_one_iff_adj.2 (p.adj_getVert_succ hlt)).le
          · rw [p.getVert_of_length_le hge, p.getVert_of_length_le (by omega),
              SimpleGraph.dist_self]
            omega
        rw [hj] at hje
        have := hX.dist_triangle (u := p.getVert k) (v := p.getVert (k + 1)) (w := e)
        omega
  refine ⟨c, hc, ?_⟩
  have h1 := dist_add_dist_of_geodesic hX hp hc
  have h2 := dist_add_dist_of_geodesic hX hq he
  have h3 := dist_add_dist_of_geodesic hX hr hf
  have t1 := hX.dist_triangle (u := w) (v := f) (w := c)
  have t2 := hX.dist_triangle (u := a) (v := f) (w := c)
  have t3 := hX.dist_triangle (u := w) (v := e) (w := c)
  have t4 := hX.dist_triangle (u := c) (v := e) (w := b)
  have c1 : X.dist f c = X.dist c f := SimpleGraph.dist_comm
  have c2 : X.dist a f = X.dist f a := SimpleGraph.dist_comm
  have c3 : X.dist e c = X.dist c e := SimpleGraph.dist_comm
  have c4 : X.dist e b = X.dist b e := SimpleGraph.dist_comm
  have c5 : X.dist w e = X.dist e w := SimpleGraph.dist_comm
  have c6 : X.dist w b = X.dist b w := SimpleGraph.dist_comm
  omega

/-- If geodesic triangles are `δ`-thin, then the graph distance satisfies the four-point condition
`min ((x | y)_w, (y | z)_w) - (3δ + 1) ≤ (x | z)_w`, stated here without subtraction. -/
@[category API, AMS 20]
lemma four_point_of_sideThin (hX : X.Connected) {δ : ℕ}
    (hthin : ∀ (x y z : V) (p : X.Walk x y) (q : X.Walk y z) (r : X.Walk z x),
      Geodesic X p → Geodesic X q → Geodesic X r → SideThin X δ p q r) (w x y z : V) :
    X.dist w y + X.dist x z ≤ X.dist w x + X.dist y z + 6 * δ + 2 ∨
      X.dist w y + X.dist x z ≤ X.dist w z + X.dist x y + 6 * δ + 2 := by
  obtain ⟨p, hp⟩ := hX.exists_walk_length_eq_dist x z
  obtain ⟨q, hq⟩ := hX.exists_walk_length_eq_dist z y
  obtain ⟨r, hr⟩ := hX.exists_walk_length_eq_dist y x
  obtain ⟨c, hc, hwc⟩ := exists_dist_le_of_sideThin hX hthin p hp w
  obtain ⟨e, he | he, hce⟩ := hthin x z y p q r hp hq hr c hc
  · left
    have h := dist_add_dist_le_of_geodesic hX hq he w
    have t := hX.dist_triangle (u := w) (v := c) (w := e)
    have c1 : X.dist z y = X.dist y z := SimpleGraph.dist_comm
    omega
  · right
    have h := dist_add_dist_le_of_geodesic hX hr he w
    have t := hX.dist_triangle (u := w) (v := c) (w := e)
    have c1 : X.dist y x = X.dist x y := SimpleGraph.dist_comm
    omega

end Graph

section Group

variable {G : Type*} [Group G]

/-- If the Cayley graph of `S` is connected, then `S` generates `G`. -/
@[category API, AMS 20]
lemma closure_eq_top_of_connected {S : Set G} (hS : (SimpleGraph.mulCayley S).Connected) :
    Subgroup.closure S = ⊤ := by
  have key : ∀ {a b : G} (p : (SimpleGraph.mulCayley S).Walk a b),
      a ∈ Subgroup.closure S → b ∈ Subgroup.closure S := by
    intro a b p
    induction p with
    | nil => exact id
    | cons h _ ih =>
      intro ha
      apply ih
      obtain ⟨-, s, hs, h | h⟩ := (SimpleGraph.mulCayley_adj' _ _ _).1 h
      · rw [← h]
        exact mul_mem ha (Subgroup.subset_closure hs)
      · rw [eq_mul_inv_of_mul_eq h.symm]
        exact mul_mem ha (inv_mem (Subgroup.subset_closure hs))
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨p⟩ := hS.preconnected 1 g
  exact key p (one_mem _)

/-- For a generating family with range `S`, the word length of `a⁻¹ * b` is the distance from `a`
to `b` in the Cayley graph of `S`. -/
@[category API, AMS 20]
lemma wordLength_inv_mul_eq_dist {ι : Type*} (P : Group.Generators G ι) {S : Set G}
    (hP : Set.range P.val = S) (hS : (SimpleGraph.mulCayley S).Connected) (a b : G) :
    P.wordLength (a⁻¹ * b) = (SimpleGraph.mulCayley S).dist a b := by
  have hword : ∀ {a b : G} (p : (SimpleGraph.mulCayley S).Walk a b),
      ∃ l, l.length = p.length ∧ a * P.wordProd l = b := by
    intro a b p
    induction p with
    | nil => exact ⟨[], rfl, by simp⟩
    | cons h p ih =>
      obtain ⟨l, hl, hlb⟩ := ih
      obtain ⟨-, s, hs, h | h⟩ := (SimpleGraph.mulCayley_adj' _ _ _).1 h
      · obtain ⟨i, rfl⟩ := hP ▸ hs
        refine ⟨(i, true) :: l, by simp [hl], ?_⟩
        rw [Group.Generators.wordProd_cons, ← hlb, ← h]
        simp [mul_assoc]
      · obtain ⟨i, rfl⟩ := hP ▸ hs
        refine ⟨(i, false) :: l, by simp [hl], ?_⟩
        rw [Group.Generators.wordProd_cons, ← hlb, h]
        simp [mul_assoc]
  have hdist : ∀ (l : List (ι × Bool)) (a : G),
      (SimpleGraph.mulCayley S).dist a (a * P.wordProd l) ≤ l.length := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
      intro a
      obtain ⟨i, c⟩ := x
      have h1 : (SimpleGraph.mulCayley S).dist a (a * cond c (P.val i) (P.val i)⁻¹) ≤ 1 := by
        by_cases ha : a = a * cond c (P.val i) (P.val i)⁻¹
        · rw [← ha, SimpleGraph.dist_self]
          exact zero_le_one
        · refine (SimpleGraph.dist_eq_one_iff_adj.2 ?_).le
          refine (SimpleGraph.mulCayley_adj' _ _ _).2 ⟨ha, P.val i, hP ▸ Set.mem_range_self i, ?_⟩
          cases c
          · right
            simp
          · left
            rfl
      have h2 := hS.dist_triangle (u := a) (v := a * cond c (P.val i) (P.val i)⁻¹)
        (w := a * P.wordProd ((i, c) :: l))
      rw [Group.Generators.wordProd_cons, ← mul_assoc] at h2 ⊢
      have h3 := ih (a * cond c (P.val i) (P.val i)⁻¹)
      simp only [List.length_cons]
      omega
  refine le_antisymm ?_ ?_
  · obtain ⟨p, hp⟩ := hS.exists_walk_length_eq_dist a b
    obtain ⟨l, hl, hlb⟩ := hword p
    rw [← hp, ← hl, ← hlb, inv_mul_cancel_left]
    exact P.wordLength_wordProd_le l
  · obtain ⟨l, hl, hlg⟩ := P.exists_isGeodesic (a⁻¹ * b)
    have := hdist l a
    rw [hlg, mul_inv_cancel_left] at this
    rw [← hlg, hl.eq]
    exact this

/-- Thin geodesic triangles in a Cayley graph imply `Group.IsHyperbolic`, with constant `3δ + 1`
for the word metric of an enumeration of the generating set. -/
@[category API, AMS 20]
theorem isHyperbolic_of_wordHyperbolic (h : WordHyperbolic G) : Group.IsHyperbolic G := by
  obtain ⟨S, hfin, hS, δ, hthin⟩ := h
  have hcl := closure_eq_top_of_connected hS
  let _ := hfin.fintype
  let P : Group.Generators G (Fin (Fintype.card S)) :=
    (Group.Generators.ofSet hcl).reindex (Fintype.equivFin S).symm
  have hP : Set.range P.val = S := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Fintype.equivFin S).symm i).2
    · intro hg
      exact ⟨Fintype.equivFin S ⟨g, hg⟩, by simp [P]⟩
  refine ⟨Fintype.card S, P, ((3 * δ + 1 : ℕ) : ℝ), ?_⟩
  let _ := P.normedGroup
  have hd : ∀ a b : G, dist a b = ((SimpleGraph.mulCayley S).dist a b : ℝ) := fun a b => by
    rw [dist_eq_norm_inv_mul, ← wordLength_inv_mul_eq_dist P hP hS a b]
    rfl
  show Metric.IsHyperbolicWith G _
  intro w x y z
  simp only [Metric.gromovProduct_eq, hd]
  push_cast
  rcases four_point_of_sideThin hS (fun x y z p q r hp hq hr => (hthin x y z p q r hp hq hr).1)
    w x y z with h | h
  · have h' : ((SimpleGraph.mulCayley S).dist w y : ℝ) + (SimpleGraph.mulCayley S).dist x z ≤
        (SimpleGraph.mulCayley S).dist w x + (SimpleGraph.mulCayley S).dist y z + 6 * δ + 2 := by
      exact_mod_cast h
    have := min_le_right
      (((SimpleGraph.mulCayley S).dist w x + (SimpleGraph.mulCayley S).dist w y -
        (SimpleGraph.mulCayley S).dist x y : ℝ) / 2)
      (((SimpleGraph.mulCayley S).dist w y + (SimpleGraph.mulCayley S).dist w z -
        (SimpleGraph.mulCayley S).dist y z : ℝ) / 2)
    linarith
  · have h' : ((SimpleGraph.mulCayley S).dist w y : ℝ) + (SimpleGraph.mulCayley S).dist x z ≤
        (SimpleGraph.mulCayley S).dist w z + (SimpleGraph.mulCayley S).dist x y + 6 * δ + 2 := by
      exact_mod_cast h
    have := min_le_left
      (((SimpleGraph.mulCayley S).dist w x + (SimpleGraph.mulCayley S).dist w y -
        (SimpleGraph.mulCayley S).dist x y : ℝ) / 2)
      (((SimpleGraph.mulCayley S).dist w y + (SimpleGraph.mulCayley S).dist w z -
        (SimpleGraph.mulCayley S).dist y z : ℝ) / 2)
    linarith

end Group

end ThinTriangles

set_option linter.style.formal_proof_palomar false in
/-- There is a torsion-free group, hyperbolic in the sense of uniformly thin geodesic triangles in a
Cayley graph, that is not residually finite. The definitions are those in `ThinTriangles`.

This was proved by an internal OpenAI model in September 2026 [OAI26a]; see the linked Lean
proof. -/
@[category research solved, AMS 20, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/Hyperbolic/Main.lean#L7"]
theorem hyperbolic_residuallyFinite.variants.thin_triangles :
    ∃ (G : Type) (_ : Group G),
      ThinTriangles.TorsionFree G ∧ ThinTriangles.WordHyperbolic G ∧
        ¬ Group.ResiduallyFinite G := by
  sorry

/-- The statement of [OAI26a] answers `hyperbolic_residuallyFinite`: its group is hyperbolic by
`ThinTriangles.isHyperbolic_of_wordHyperbolic`. -/
@[category test, AMS 20]
theorem hyperbolic_residuallyFinite_of_thin_triangles
    (h : type_of% @hyperbolic_residuallyFinite.variants.thin_triangles) :
    type_of% @hyperbolic_residuallyFinite := by
  obtain ⟨G, _, -, hG, hRF⟩ := h
  intro hall
  have := ThinTriangles.isHyperbolic_of_wordHyperbolic hG
  exact hRF (hall G)

end HyperbolicGroupsResiduallyFinite
