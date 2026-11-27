/-
Copyright 2025 The Formal Conjectures Authors.

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
# Written on the Wall II - Conjecture 84

**Verbatim statement (WOWII #84, status O):**
> If G is a simple connected graph, then tree(G) ≥ 2 rad(G) / δ(G)

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj84

Here `δ(G)` is the **minimum degree** of `G` (lowercase delta in the WOWII
HTML, rendered as `<font face="Symbol">d</font>`), not the average distance.

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Proof

The conjecture is proved below. If `δ(G) ≥ 2` it follows from the fact that a shortest path
realising the eccentricity of a vertex is an induced path on `rad(G) + 1` vertices. The case
`δ(G) = 1` is the heart of the matter: we show that a connected graph `G` with a vertex `ℓ` of
degree one and radius `r ≥ 2` has an induced tree on at least `2r` vertices.

* Let `K` be a smallest connected induced subgraph of `G` containing `ℓ` whose radius is at
  least `r`. For every non-cut vertex `x ≠ ℓ` of `K`, a centre `x*` of `K - x` sees every
  vertex of `K` except `x` within distance `r - 1`. An argument of Fajtlowicz (1988) then shows
  that the set of non-cut vertices `x ≠ ℓ` of degree at least two is closed under taking
  neighbours, so it is empty: every vertex of `K` of degree at least two is a cut vertex of `K`.
* Removing the vertices of degree one from `K` gives `K'` of radius at least `r - 1`.
* (Lemma Q) Every connected `H` of radius at least `q ≥ 1` contains a connected induced `J` and
  an induced tree `T ⊆ J` together with a set `Z ⊆ T` of at least two non-cut vertices of `J`
  such that `|T| + |Z| ≥ 2q + 2`. This is proved by induction on `q`, using a minimal `J` of
  radius at least `q` and the same closure argument.
* Every `z ∈ Z` is a cut vertex of `K` while `J - z` is connected, so `z` has a neighbour in a
  component of `K - z` avoiding `J`; adding one such private neighbour for each `z ∈ Z` to `T`
  gives an induced tree of `K` on at least `|T| + |Z| ≥ 2r` vertices.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture84

open SimpleGraph

section Proof
variable {α : Type*} [DecidableEq α] {G : SimpleGraph α}

@[category API, AMS 5]
theorem isTree_insert_leaf {T : Set α} (hT : (G.induce T).IsTree) {x y : α}
    (hy : y ∈ T) (hxy : G.Adj x y) (huniq : ∀ z ∈ T, G.Adj x z → z = y) :
    (G.induce (insert x T)).IsTree := by
  constructor
  · have h1 : (G.induce T).Preconnected := hT.connected.preconnected
    have h2 : (G.induce ({x, y} : Set α)).Preconnected :=
      (induce_pair_connected_of_adj hxy).preconnected
    have h3 : (T ∩ {x, y}).Nonempty := ⟨y, hy, by simp⟩
    have := induce_union_connected h1 h2 h3
    have heq : T ∪ {x, y} = insert x T := by
      ext z
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (h | h | h)
        · exact Or.inr h
        · exact Or.inl h
        · exact Or.inr (h ▸ hy)
      · rintro (h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
    rwa [heq] at this
  · intro v c hc
    let x' : (insert x T : Set α) := ⟨x, Set.mem_insert _ _⟩
    by_cases hxs : x' ∈ c.support
    · have hc' := hc.rotate (u := x') hxs
      have hne := hc'.snd_ne_penultimate
      have hnil := hc'.not_nil
      have ha := (c.rotate x' hxs).adj_snd hnil
      have hb := (c.rotate x' hxs).adj_penultimate hnil
      rw [induce_adj] at ha hb
      have key : ∀ w : (insert x T : Set α), G.Adj x w.1 → w.1 = y := by
        intro w hw
        have hwx : w.1 ≠ x := (G.ne_of_adj hw).symm
        have hwT : w.1 ∈ T := by
          rcases w.2 with h | h
          · exact absurd h hwx
          · exact h
        exact huniq _ hwT hw
      apply hne
      apply Subtype.ext
      rw [key _ ha, key _ hb.symm]
    · let f := (Embedding.induce (G := G) (insert x T : Set α)).toHom
      have hcG : (c.map f).IsCycle :=
        (Walk.isCycle_map_iff_of_injective (Embedding.induce (G := G) _).injective).2 hc
      have hsupp : ∀ z ∈ (c.map f).support, z ∈ T := by
        intro z hz
        rw [Walk.support_map, List.mem_map] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        have hwx : w ≠ x' := fun h => hxs (h ▸ hw)
        rcases w.2 with h | h
        · exact absurd (Subtype.ext h) hwx
        · exact h
      have hcT : ((c.map f).induce T hsupp).IsCycle := by
        rw [← Walk.isCycle_map_iff_of_injective (f := (Embedding.induce (G := G) T).toHom)
          (Embedding.induce (G := G) T).injective,
          Walk.map_induce]
        exact hcG
      exact hT.isAcyclic _ hcT

omit [DecidableEq α] in
@[category API, AMS 5]
theorem isTree_singleton (v : α) : (G.induce ({v} : Set α)).IsTree := by
  have : Unique ({v} : Set α) := Set.uniqueSingleton v
  exact IsTree.of_subsingleton


/-! ### Walks inside a vertex set -/

/-- A walk all of whose vertices lie in `S`. -/
def InS (S : Finset α) {a b : α} (p : G.Walk a b) : Prop := ∀ v ∈ p.support, v ∈ S

variable (G) in
/-- `S` is connected in `G` (any two vertices of `S` are joined by a walk inside `S`). -/
def ConnS (S : Finset α) : Prop := ∀ a ∈ S, ∀ b ∈ S, ∃ p : G.Walk a b, InS S p

variable (G) in
/-- Distance inside `S`. -/
noncomputable def dS (S : Finset α) (a b : α) : ℕ :=
  sInf {n | ∃ p : G.Walk a b, InS S p ∧ p.length = n}

variable {S S' : Finset α} {a b c : α}

omit [DecidableEq α] in
@[category API, AMS 5]
lemma InS.mono (h : S ⊆ S') {p : G.Walk a b} (hp : InS S p) : InS S' p :=
  fun v hv => h (hp v hv)

omit [DecidableEq α] in
@[category API, AMS 5]
lemma InS.append {p : G.Walk a b} {q : G.Walk b c} (hp : InS S p) (hq : InS S q) :
    InS S (p.append q) := by
  intro v hv
  rw [Walk.mem_support_append_iff] at hv
  rcases hv with h | h
  · exact hp v h
  · exact hq v h

omit [DecidableEq α] in
@[category API, AMS 5]
lemma InS.reverse {p : G.Walk a b} (hp : InS S p) : InS S p.reverse :=
  fun v hv => hp v (by simpa using hv)

omit [DecidableEq α] in
@[category API, AMS 5]
lemma InS.take {p : G.Walk a b} (hp : InS S p) (n : ℕ) : InS S (p.take n) := by
  intro v hv
  rw [Walk.support_take] at hv
  exact hp v (List.mem_of_mem_take hv)

omit [DecidableEq α] in
@[category API, AMS 5]
lemma InS.drop {p : G.Walk a b} (hp : InS S p) (n : ℕ) : InS S (p.drop n) := by
  intro v hv
  rw [Walk.drop_support_eq_support_drop_min] at hv
  exact hp v (List.mem_of_mem_drop hv)

omit [DecidableEq α] in
@[category API, AMS 5]
lemma InS.start {p : G.Walk a b} (hp : InS S p) : a ∈ S := hp a p.start_mem_support

omit [DecidableEq α] in
@[category API, AMS 5]
lemma InS.finish {p : G.Walk a b} (hp : InS S p) : b ∈ S := hp b p.end_mem_support

omit [DecidableEq α] in
@[category API, AMS 5]
lemma InS.getVert {p : G.Walk a b} (hp : InS S p) (i : ℕ) : p.getVert i ∈ S :=
  hp _ (p.getVert_mem_support i)

omit [DecidableEq α] in
@[category API, AMS 5]
lemma inS_nil (ha : a ∈ S) : InS S (Walk.nil : G.Walk a a) := by
  intro v hv; simp at hv; exact hv ▸ ha

omit [DecidableEq α] in
@[category API, AMS 5]
lemma inS_edge (ha : a ∈ S) (hb : b ∈ S) (hab : G.Adj a b) :
    InS S (Walk.cons hab Walk.nil) := by
  intro v hv
  simp at hv
  rcases hv with rfl | rfl
  · exact ha
  · exact hb

omit [DecidableEq α] in
@[category API, AMS 5]
lemma dS_le (p : G.Walk a b) (hp : InS S p) : dS G S a b ≤ p.length :=
  Nat.sInf_le ⟨p, hp, rfl⟩

omit [DecidableEq α] in
@[category API, AMS 5]
lemma dS_spec (h : ∃ p : G.Walk a b, InS S p) :
    ∃ p : G.Walk a b, InS S p ∧ p.length = dS G S a b := by
  obtain ⟨p, hp⟩ := h
  have hne : ({n | ∃ p : G.Walk a b, InS S p ∧ p.length = n} : Set ℕ).Nonempty :=
    ⟨_, p, hp, rfl⟩
  exact Nat.sInf_mem hne

omit [DecidableEq α] in
@[category API, AMS 5]
lemma dS_mono (h : S ⊆ S') (hw : ∃ p : G.Walk a b, InS S p) : dS G S' a b ≤ dS G S a b := by
  obtain ⟨p, hp, hl⟩ := dS_spec hw
  rw [← hl]
  exact dS_le p (hp.mono h)

omit [DecidableEq α] in
@[category API, AMS 5]
lemma dS_triangle (h1 : ∃ p : G.Walk a b, InS S p) (h2 : ∃ p : G.Walk b c, InS S p) :
    dS G S a c ≤ dS G S a b + dS G S b c := by
  obtain ⟨p, hp, hpl⟩ := dS_spec h1
  obtain ⟨q, hq, hql⟩ := dS_spec h2
  calc dS G S a c ≤ (p.append q).length := dS_le _ (hp.append hq)
    _ = dS G S a b + dS G S b c := by rw [Walk.length_append, hpl, hql]

omit [DecidableEq α] in
@[category API, AMS 5]
lemma dS_adj_le (ha : a ∈ S) (hb : b ∈ S) (hab : G.Adj a b) : dS G S a b ≤ 1 :=
  (dS_le _ (inS_edge ha hb hab)).trans (by simp)

omit [DecidableEq α] in
@[category API, AMS 5]
lemma dS_self (ha : a ∈ S) : dS G S a a = 0 :=
  Nat.le_zero.mp ((dS_le _ (inS_nil (G := G) ha)).trans (by simp))

omit [DecidableEq α] in
@[category API, AMS 5]
lemma eq_of_dS_eq_zero (hw : ∃ p : G.Walk a b, InS S p) (h : dS G S a b = 0) : a = b := by
  obtain ⟨p, -, hl⟩ := dS_spec hw
  exact p.eq_of_length_eq_zero (hl.trans h)

omit [DecidableEq α] in
/-- Along a shortest walk inside `S`, the `i`-th vertex is at `S`-distance `i`. -/
@[category API, AMS 5]
lemma geod_getVert (p : G.Walk a b) (hp : InS S p) (hl : p.length = dS G S a b) {i : ℕ}
    (hi : i ≤ p.length) : dS G S a (p.getVert i) = i := by
  apply le_antisymm
  · calc dS G S a (p.getVert i) ≤ (p.take i).length := dS_le _ (hp.take i)
      _ = i := by rw [Walk.take_length]; omega
  · by_contra hlt
    push Not at hlt
    obtain ⟨q, hq, hql⟩ := dS_spec (S := S) ⟨p.take i, hp.take i⟩
    have h1 := dS_le (q.append (p.drop i)) (hq.append (hp.drop i))
    rw [Walk.length_append, Walk.drop_length, hql] at h1
    omega

/-- The first `i + 1` vertices of a shortest walk inside `S` induce a tree. -/
@[category API, AMS 5]
lemma geod_prefix_tree (p : G.Walk a b) (hp : InS S p) (hl : p.length = dS G S a b) :
    ∀ i ≤ p.length, (G.induce (((Finset.range (i + 1)).image p.getVert : Finset α) :
      Set α)).IsTree ∧ ((Finset.range (i + 1)).image p.getVert).card = i + 1 := by
  intro i
  induction i with
  | zero =>
    intro _
    have h0 : (Finset.range (0 + 1)).image p.getVert = {a} := by simp
    rw [h0, Finset.coe_singleton]
    exact ⟨isTree_singleton a, by simp⟩
  | succ i ih =>
    intro hi
    obtain ⟨ht, hc⟩ := ih (by omega)
    have hrange : (Finset.range (i + 1 + 1)).image p.getVert =
        insert (p.getVert (i + 1)) ((Finset.range (i + 1)).image p.getVert) := by
      rw [Finset.range_add_one, Finset.image_insert]
    have hmem : ∀ z ∈ (Finset.range (i + 1)).image p.getVert, ∃ j ≤ i, z = p.getVert j := by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨j, hj, rfl⟩ := hz
      exact ⟨j, by simp at hj; omega, rfl⟩
    have hdx : dS G S a (p.getVert (i + 1)) = i + 1 := geod_getVert p hp hl hi
    have hnot : p.getVert (i + 1) ∉ (Finset.range (i + 1)).image p.getVert := by
      intro h
      obtain ⟨j, hj, hz⟩ := hmem _ h
      have := geod_getVert p hp hl (i := j) (by omega)
      rw [← hz, hdx] at this
      omega
    refine ⟨?_, ?_⟩
    · rw [hrange, Finset.coe_insert]
      refine isTree_insert_leaf ht (y := p.getVert i) ?_ ?_ ?_
      · simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
        exact ⟨i, by omega, rfl⟩
      · exact (p.adj_getVert_succ (by omega)).symm
      · intro z hz hadj
        obtain ⟨j, hj, rfl⟩ := hmem z (by simpa using hz)
        have hw1 : ∃ q : G.Walk a (p.getVert j), InS S q := ⟨p.take j, hp.take j⟩
        have h1 := dS_triangle (S := S) hw1
          ⟨Walk.cons hadj.symm Walk.nil, inS_edge (hp.getVert j) (hp.getVert _) hadj.symm⟩
        rw [hdx, geod_getVert p hp hl (i := j) (by omega)] at h1
        have h2 := dS_adj_le (hp.getVert j) (hp.getVert (i + 1)) hadj.symm
        have : j = i := by omega
        rw [this]
    · rw [hrange, Finset.card_insert_of_notMem hnot, hc]


variable (G) in
/-- `S` is connected and every vertex of `S` has a vertex at `S`-distance at least `r`. -/
def RadGe (S : Finset α) (r : ℕ) : Prop :=
  S.Nonempty ∧ ConnS G S ∧ ∀ a ∈ S, ∃ b ∈ S, r ≤ dS G S a b

variable [DecidableRel G.Adj]

variable (G) in
/-- Degree inside `S`. -/
def degS (S : Finset α) (v : α) : ℕ := (S.filter (G.Adj v)).card

omit [DecidableRel G.Adj] in
@[category API, AMS 5]
lemma len_ge_of_mem_support {z : α} {p : G.Walk c z} (hp : InS S p) {y : α}
    (hy : y ∈ p.support) (hyz : y ≠ z) : dS G S c y + 1 ≤ p.length := by
  have h1 := dS_le (p.takeUntil y hy) (fun v hv => hp v (p.support_takeUntil_subset_support hy hv))
  have h2 : 1 ≤ (p.dropUntil y hy).length := by
    rcases Nat.eq_zero_or_pos (p.dropUntil y hy).length with h | h
    · exact absurd ((p.dropUntil y hy).eq_of_length_eq_zero h) hyz
    · exact h
  have h3 := congrArg Walk.length (p.take_spec hy)
  rw [Walk.length_append] at h3
  omega

omit [DecidableRel G.Adj] [DecidableEq α] in
@[category API, AMS 5]
lemma conn_of_hub (_hc : c ∈ S) (h : ∀ v ∈ S, ∃ p : G.Walk c v, InS S p) : ConnS G S := by
  intro u hu v hv
  obtain ⟨p, hp⟩ := h u hu
  obtain ⟨q, hq⟩ := h v hv
  exact ⟨p.reverse.append q, hp.reverse.append hq⟩

omit [DecidableEq α] [DecidableRel G.Adj] in
@[category API, AMS 5]
lemma mem_support_getVert {p : G.Walk a b} {v : α} (hv : v ∈ p.support) :
    ∃ i ≤ p.length, p.getVert i = v := by
  obtain ⟨i, h1, h2⟩ := Walk.mem_support_iff_exists_getVert.1 hv
  exact ⟨i, h2, h1⟩

@[category API, AMS 5]
lemma two_le_degS {S : Finset α} {v x y : α} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (hvx : G.Adj v x) (hvy : G.Adj v y) : 2 ≤ degS G S v := by
  unfold degS
  have : ({x, y} : Finset α) ⊆ S.filter (G.Adj v) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact Finset.mem_filter.2 ⟨hx, hvx⟩
    · exact Finset.mem_filter.2 ⟨hy, hvy⟩
  have h2 := Finset.card_le_card this
  rw [Finset.card_pair hxy] at h2
  exact h2

/-- An internal vertex of a shortest walk inside `S` has two neighbours in `S`. -/
@[category API, AMS 5]
lemma internal_deg {p : G.Walk a b} (hp : InS S p) (hl : p.length = dS G S a b) {i : ℕ}
    (h0 : 0 < i) (hi : i < p.length) : 2 ≤ degS G S (p.getVert i) := by
  have hadj1 : G.Adj (p.getVert (i - 1)) (p.getVert i) := by
    have := p.adj_getVert_succ (i := i - 1) (by omega)
    rwa [Nat.sub_add_cancel h0] at this
  have hadj2 : G.Adj (p.getVert i) (p.getVert (i + 1)) := p.adj_getVert_succ hi
  refine two_le_degS (hp.getVert (i - 1)) (hp.getVert (i + 1)) ?_ hadj1.symm hadj2
  intro h
  have e1 := geod_getVert p hp hl (i := i - 1) (by omega)
  have e2 := geod_getVert p hp hl (i := i + 1) (by omega)
  rw [h] at e1
  omega

@[category API, AMS 5]
lemma closure_step {K : Finset α} {r : ℕ} (hr : 2 ≤ r) (hK : RadGe G K r)
    {x : α} (hxK : x ∈ K) (hxc : ConnS G (K.erase x)) (hxne : (K.erase x).Nonempty)
    (hxcrit : ¬ RadGe G (K.erase x) r) (hdeg : 2 ≤ degS G K x)
    {y : α} (hyK : y ∈ K) (hxy : G.Adj x y) :
    ConnS G (K.erase y) ∧ 2 ≤ degS G K y := by
  have hex : ∃ c ∈ K.erase x, ∀ b ∈ K.erase x, dS G (K.erase x) c b < r := by
    by_contra hcon
    push Not at hcon
    exact hxcrit ⟨hxne, hxc, hcon⟩
  obtain ⟨c, hcK, hc⟩ := hex
  have hcK' : c ∈ K := Finset.mem_of_mem_erase hcK
  have hle : ∀ b ∈ K, b ≠ x → dS G K c b ≤ r - 1 := by
    intro b hb hbx
    have hb' : b ∈ K.erase x := Finset.mem_erase.2 ⟨hbx, hb⟩
    have h1 := dS_mono (Finset.erase_subset x K) (hxc c hcK b hb')
    have h2 := hc b hb'
    omega
  have hxfar : r ≤ dS G K c x := by
    obtain ⟨b, hb, hbr⟩ := hK.2.2 c hcK'
    by_cases hbx : b = x
    · rwa [hbx] at hbr
    · have := hle b hb hbx
      omega
  have hyx : y ≠ x := (G.ne_of_adj hxy).symm
  have hdy : dS G K c y = r - 1 := by
    have h1 := hle y hyK hyx
    have h2 := dS_triangle (S := K) (hK.2.1 c hcK' y hyK) ⟨_, inS_edge hyK hxK hxy.symm⟩
    have h3 := dS_adj_le (S := K) hyK hxK hxy.symm
    omega
  have hyc : y ≠ c := by
    intro h
    rw [h, dS_self hcK'] at hdy
    omega
  have hreach : ∀ v ∈ K, v ≠ x → v ≠ y → ∃ p : G.Walk c v, InS (K.erase y) p := by
    intro v hv hvx hvy
    have hv' : v ∈ K.erase x := Finset.mem_erase.2 ⟨hvx, hv⟩
    obtain ⟨p, hp, hpl⟩ := dS_spec (hxc c hcK v hv')
    refine ⟨p, fun w hw => Finset.mem_erase.2 ⟨?_, Finset.mem_of_mem_erase (hp w hw)⟩⟩
    rintro rfl
    have h1 := len_ge_of_mem_support (hp.mono (Finset.erase_subset x K)) hw (Ne.symm hvy)
    have h2 := hc v hv'
    omega
  refine ⟨?_, ?_⟩
  · have hcy : c ∈ K.erase y := Finset.mem_erase.2 ⟨hyc.symm, hcK'⟩
    refine conn_of_hub hcy ?_
    intro v hv
    have hvy : v ≠ y := Finset.ne_of_mem_erase hv
    have hvK : v ∈ K := Finset.mem_of_mem_erase hv
    by_cases hvx : v = x
    · subst hvx
      obtain ⟨w, hw, hwy⟩ := Finset.exists_mem_ne hdeg y
      rw [Finset.mem_filter] at hw
      have hwx : w ≠ v := (G.ne_of_adj hw.2).symm
      obtain ⟨p, hp⟩ := hreach w hw.1 hwx hwy
      refine ⟨p.append (Walk.cons hw.2.symm Walk.nil), hp.append ?_⟩
      exact inS_edge (Finset.mem_erase.2 ⟨hwy, hw.1⟩) hv hw.2.symm
    · exact hreach v hvK hvx hvy
  · obtain ⟨p, hp, hpl⟩ := dS_spec (hK.2.1 c hcK' y hyK)
    have hlen : p.length = r - 1 := hpl.trans hdy
    have hadj : G.Adj (p.getVert (p.length - 1)) y := by
      have := p.adj_getVert_succ (i := p.length - 1) (by omega)
      rwa [Nat.sub_add_cancel (by omega), Walk.getVert_length] at this
    have hd' := geod_getVert p hp hpl (i := p.length - 1) (by omega)
    refine two_le_degS hxK (hp.getVert (p.length - 1)) ?_ hxy.symm hadj.symm
    intro h
    rw [← h] at hd'
    omega

omit [DecidableEq α] [DecidableRel G.Adj] in
@[category API, AMS 5]
lemma propagate_walk {K : Finset α} (P : α → Prop)
    (step : ∀ x ∈ K, ∀ y ∈ K, P x → G.Adj x y → P y) :
    ∀ {u w : α} (p : G.Walk u w), InS K p → P u → P w := by
  intro u w p
  induction p with
  | nil => intro _ h; exact h
  | @cons u w' _ hadj q ih =>
    intro hp hu
    have huK : u ∈ K := hp u (by simp)
    have hwK : w' ∈ K := hp w' (by simp)
    exact ih (fun z hz => hp z (by simp [hz])) (step u huK w' hwK hu hadj)

omit [DecidableEq α] [DecidableRel G.Adj] in
@[category API, AMS 5]
lemma propagate {K : Finset α} (P : α → Prop) {x0 : α} (hx0 : x0 ∈ K) (hK : ConnS G K)
    (h0 : P x0) (step : ∀ x ∈ K, ∀ y ∈ K, P x → G.Adj x y → P y) : ∀ v ∈ K, P v := by
  intro v hv
  obtain ⟨p, hp⟩ := hK x0 hx0 v hv
  exact propagate_walk P step p hp h0

/-- Removing the vertices of degree `≤ 1` lowers the radius by at most one. -/
@[category API, AMS 5]
lemma strip {J : Finset α} {q : ℕ} (hq : 1 ≤ q) (hJ : RadGe G J (q + 1)) :
    RadGe G (J.filter (fun v => 2 ≤ degS G J v)) q := by
  set J' := J.filter (fun v => 2 ≤ degS G J v) with hJ'
  have hsub : J' ⊆ J := Finset.filter_subset _ _
  -- geodesics between vertices of `J'` stay in `J'`
  have hgeo : ∀ a ∈ J', ∀ b ∈ J', ∀ p : G.Walk a b, InS J p → p.length = dS G J a b →
      InS J' p := by
    intro a ha b hb p hp hl v hv
    obtain ⟨i, hi, rfl⟩ := mem_support_getVert hv
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · rw [h0, Walk.getVert_zero]; exact ha
    rcases eq_or_lt_of_le hi with h1 | h1
    · rw [h1, Walk.getVert_length]; exact hb
    exact Finset.mem_filter.2 ⟨hp.getVert i, internal_deg hp hl h0 h1⟩
  have hconn : ConnS G J' := by
    intro a ha b hb
    obtain ⟨p, hp, hl⟩ := dS_spec (hJ.2.1 a (hsub ha) b (hsub hb))
    exact ⟨p, hgeo a ha b hb p hp hl⟩
  obtain ⟨a0, ha0⟩ := hJ.1
  refine ⟨?_, hconn, ?_⟩
  · obtain ⟨b, hb, hbd⟩ := hJ.2.2 a0 ha0
    obtain ⟨p, hp, hl⟩ := dS_spec (hJ.2.1 a0 ha0 b hb)
    exact ⟨p.getVert 1, Finset.mem_filter.2 ⟨hp.getVert 1, internal_deg hp hl (by omega)
      (by omega)⟩⟩
  · intro a ha
    obtain ⟨b, hb, hbd⟩ := hJ.2.2 a (hsub ha)
    obtain ⟨p, hp, hl⟩ := dS_spec (hJ.2.1 a (hsub ha) b hb)
    have hb' : p.getVert (p.length - 1) ∈ J' :=
      Finset.mem_filter.2 ⟨hp.getVert _, internal_deg hp hl (by omega) (by omega)⟩
    refine ⟨_, hb', ?_⟩
    have h1 := geod_getVert p hp hl (i := p.length - 1) (by omega)
    have h2 := dS_mono hsub (hconn a ha _ hb')
    omega


/-! ### Private regions and branches -/

omit [DecidableRel G.Adj] in
/-- A walk inside `S` starting at `t` stays inside the set of vertices reachable from `t`. -/
@[category API, AMS 5]
lemma reach_of_walk {S : Finset α} {t v : α} (p : G.Walk t v) (hp : InS S p) :
    ∀ u ∈ p.support, ∃ q : G.Walk t u, InS S q := by
  intro u hu
  exact ⟨p.takeUntil u hu, fun w hw => hp w (p.support_takeUntil_subset_support hu hw)⟩

omit [DecidableRel G.Adj] in
/-- On a shortest walk inside `J` from `t` to `h`, the vertex `h` only occurs at the end. -/
@[category API, AMS 5]
lemma prefix_avoid {J : Finset α} {t h : α} (q : G.Walk t h) (hq : InS J q)
    (hl : q.length = dS G J t h) {u : α} (hu : u ∈ q.support) (huh : u ≠ h) :
    InS (J.erase h) (q.takeUntil u hu) := by
  intro w hw
  refine Finset.mem_erase.2 ⟨?_, hq w (q.support_takeUntil_subset_support hu hw)⟩
  rintro rfl
  have h1 := len_ge_of_mem_support (S := J)
    (fun x hx => hq x (q.support_takeUntil_subset_support hu hx)) hw (Ne.symm huh)
  have h2 := q.length_takeUntil_le_length hu
  omega

/-- A valid private region for `h` (relative to the ambient set `J` and the core `J0`). -/
def ValidRegion (J J0 : Finset α) (h : α) (D : Finset α) : Prop :=
  D ⊆ J.erase h ∧ (∀ w ∈ J0.erase h, w ∉ D) ∧
    (∀ v ∈ D, ∀ u, (∃ p : G.Walk v u, InS (J.erase h) p) → u ∈ D) ∧
    ConnS G (insert h D) ∧ D.Nonempty

omit [DecidableRel G.Adj] in
@[category API, AMS 5]
lemma private_region {J J0 : Finset α} {h : α} (hJ : ConnS G J) (hh : h ∈ J)
    (hcut : ¬ ConnS G (J.erase h)) (hJ0 : J0 ⊆ J) (hW : ConnS G (J0.erase h))
    (hWne : (J0.erase h).Nonempty) : ∃ D, ValidRegion (G := G) J J0 h D := by
  classical
  have hWsub : J0.erase h ⊆ J.erase h := Finset.erase_subset_erase h hJ0
  obtain ⟨w0, hw0⟩ := hWne
  -- a vertex `t` of `J.erase h` not reachable from `w0`
  have ht : ∃ t ∈ J.erase h, ¬ ∃ p : G.Walk w0 t, InS (J.erase h) p := by
    by_contra hcon
    push Not at hcon
    apply hcut
    intro a ha b hb
    obtain ⟨p, hp⟩ := hcon a ha
    obtain ⟨q, hq⟩ := hcon b hb
    exact ⟨p.reverse.append q, hp.reverse.append hq⟩
  obtain ⟨t, htJ, htw⟩ := ht
  set D := (J.erase h).filter (fun b => ∃ p : G.Walk t b, InS (J.erase h) p) with hD
  have hmemD : ∀ u, u ∈ D ↔ u ∈ J.erase h ∧ ∃ p : G.Walk t u, InS (J.erase h) p := by
    intro u; rw [hD, Finset.mem_filter]
  have htD : t ∈ D := (hmemD t).2 ⟨htJ, Walk.nil, inS_nil htJ⟩
  have hclosed : ∀ v ∈ D, ∀ u, (∃ p : G.Walk v u, InS (J.erase h) p) → u ∈ D := by
    intro v hv u ⟨p, hp⟩
    obtain ⟨-, q, hq⟩ := (hmemD v).1 hv
    exact (hmemD u).2 ⟨hp.finish, q.append p, hq.append hp⟩
  refine ⟨D, Finset.filter_subset _ _, ?_, hclosed, ?_, ⟨t, htD⟩⟩
  · intro w hw hwD
    obtain ⟨-, p, hp⟩ := (hmemD w).1 hwD
    obtain ⟨q, hq⟩ := hW w0 hw0 w hw
    exact htw ⟨q.append p.reverse, (hq.mono hWsub).append hp.reverse⟩
  · -- connected through `h`
    have hhR : h ∈ insert h D := Finset.mem_insert_self h D
    refine conn_of_hub hhR ?_
    -- shortest walk from `t` to `h` inside `J`
    obtain ⟨q, hq, hql⟩ := dS_spec (hJ t (Finset.mem_of_mem_erase htJ) h hh)
    have hqR : InS (insert h D) q := by
      intro u hu
      by_cases huh : u = h
      · rw [huh]; exact hhR
      · refine Finset.mem_insert_of_mem ((hmemD u).2 ⟨?_, _, prefix_avoid q hq hql hu huh⟩)
        exact Finset.mem_erase.2 ⟨huh, hq u hu⟩
    intro v hv
    rcases Finset.mem_insert.1 hv with rfl | hvD
    · exact ⟨Walk.nil, inS_nil hhR⟩
    · obtain ⟨-, p, hp⟩ := (hmemD v).1 hvD
      have hpR : InS (insert h D) p := by
        intro u hu
        exact Finset.mem_insert_of_mem (hclosed t htD u ⟨p.takeUntil u hu,
          fun w hw => hp w (p.support_takeUntil_subset_support hu hw)⟩)
      exact ⟨q.reverse.append p, hqR.reverse.append hpR⟩

omit [DecidableRel G.Adj] in
@[category API, AMS 5]
lemma tip_lemma {J J0 D : Finset α} {h : α} (hJ : ConnS G J) (hh : h ∈ J)
    (hD : ValidRegion (G := G) J J0 h D) :
    ∃ z ∈ D, ConnS G (J.erase z) ∧ ∃ p : G.Walk h z, InS (insert h D) p ∧
      p.length = dS G (insert h D) h z := by
  obtain ⟨hDsub, -, hclosed, hR, hDne⟩ := hD
  set R := insert h D with hRdef
  have hhR : h ∈ R := Finset.mem_insert_self h D
  obtain ⟨z, hzR, hzmax⟩ := Finset.exists_max_image R (dS G R h) ⟨h, hhR⟩
  obtain ⟨t, htD⟩ := hDne
  have hth : t ≠ h := Finset.ne_of_mem_erase (hDsub htD)
  have hzh : z ≠ h := by
    intro hz
    have h1 := hzmax t (Finset.mem_insert_of_mem htD)
    rw [hz, dS_self hhR] at h1
    exact hth (eq_of_dS_eq_zero (hR h hhR t (Finset.mem_insert_of_mem htD))
      (Nat.le_zero.mp h1)).symm
  have hzD : z ∈ D := by
    rcases Finset.mem_insert.1 hzR with h1 | h1
    · exact absurd h1 hzh
    · exact h1
  have hRJ : R ⊆ J := by
    intro u hu
    rcases Finset.mem_insert.1 hu with rfl | h1
    · exact hh
    · exact Finset.mem_of_mem_erase (hDsub h1)
  refine ⟨z, hzD, ?_, dS_spec (hR h hhR z hzR)⟩
  have hhz : h ∈ J.erase z := Finset.mem_erase.2 ⟨Ne.symm hzh, hh⟩
  refine conn_of_hub hhz ?_
  intro v hv
  have hvz : v ≠ z := Finset.ne_of_mem_erase hv
  have hvJ : v ∈ J := Finset.mem_of_mem_erase hv
  by_cases hvh : v = h
  · subst hvh; exact ⟨Walk.nil, inS_nil hhz⟩
  by_cases hvD : v ∈ D
  · obtain ⟨p, hp, hpl⟩ := dS_spec (hR h hhR v (Finset.mem_insert_of_mem hvD))
    refine ⟨p, fun w hw => Finset.mem_erase.2 ⟨?_, hRJ (hp w hw)⟩⟩
    rintro rfl
    have h1 := len_ge_of_mem_support hp hw (Ne.symm hvz)
    have h2 := hzmax v (Finset.mem_insert_of_mem hvD)
    omega
  · obtain ⟨q, hq, hql⟩ := dS_spec (hJ v hvJ h hh)
    have hqD : ∀ u ∈ q.support, u ∉ D := by
      intro u hu huD
      have huh : u ≠ h := fun e => Finset.ne_of_mem_erase (hDsub huD) e
      have hpre := prefix_avoid q hq hql hu huh
      exact hvD (hclosed u huD v ⟨(q.takeUntil u hu).reverse, hpre.reverse⟩)
    refine ⟨q.reverse, fun w hw => Finset.mem_erase.2 ⟨?_, hq w (by simpa using hw)⟩⟩
    rintro rfl
    exact hqD w (by simpa using hw) hzD

omit [DecidableRel G.Adj] in
/-- Attaching a geodesic branch at a vertex `h` of an induced tree. -/
@[category API, AMS 5]
lemma add_branch {T R : Finset α} {h z : α} (htree : (G.induce (T : Set α)).IsTree)
    (hh : h ∈ T) (p : G.Walk h z) (hp : InS R p) (hl : p.length = dS G R h z)
    (hRT : ∀ v ∈ R, v ≠ h → v ∉ T ∧ ∀ w ∈ T, G.Adj v w → w = h) :
    (G.induce ((T ∪ (Finset.range (p.length + 1)).image p.getVert : Finset α) :
      Set α)).IsTree := by
  have key : ∀ i ≤ p.length,
      (G.induce ((T ∪ (Finset.range (i + 1)).image p.getVert : Finset α) : Set α)).IsTree := by
    intro i
    induction i with
    | zero =>
      intro _
      have h0 : T ∪ (Finset.range (0 + 1)).image p.getVert = T := by
        simp [Finset.insert_eq_of_mem hh]
      rw [h0]
      exact htree
    | succ i ih =>
      intro hi
      have hrange : T ∪ (Finset.range (i + 1 + 1)).image p.getVert =
          insert (p.getVert (i + 1)) (T ∪ (Finset.range (i + 1)).image p.getVert) := by
        rw [Finset.range_add_one, Finset.image_insert, Finset.union_insert]
      rw [hrange, Finset.coe_insert]
      have hdx : dS G R h (p.getVert (i + 1)) = i + 1 := geod_getVert p hp hl hi
      have hxR : p.getVert (i + 1) ∈ R := hp.getVert _
      have hxh : p.getVert (i + 1) ≠ h := by
        intro e
        rw [e, dS_self (hp.start)] at hdx
        omega
      refine isTree_insert_leaf (ih (by omega)) (y := p.getVert i) ?_ ?_ ?_
      · simp only [Finset.coe_union, Finset.coe_image, Finset.coe_range, Set.mem_union,
          Set.mem_image, Set.mem_Iio]
        exact Or.inr ⟨i, by omega, rfl⟩
      · exact (p.adj_getVert_succ (by omega)).symm
      · intro w hw hadj
        simp only [Finset.coe_union, Finset.coe_image, Finset.coe_range, Set.mem_union,
          Set.mem_image, Set.mem_Iio, Finset.mem_coe] at hw
        rcases hw with hwT | ⟨j, hj, rfl⟩
        · have := (hRT _ hxR hxh).2 w hwT hadj
          subst this
          have h1 := dS_adj_le (S := R) hp.start hxR hadj.symm
          have hi0 : i = 0 := by omega
          rw [hi0, Walk.getVert_zero]
        · have h1 := dS_triangle (S := R) ⟨p.take j, hp.take j⟩
            ⟨Walk.cons hadj.symm Walk.nil, inS_edge (hp.getVert j) hxR hadj.symm⟩
          rw [hdx, geod_getVert p hp hl (i := j) (by omega)] at h1
          have h2 := dS_adj_le (hp.getVert j) hxR hadj.symm
          have : j = i := by omega
          rw [this]
  exact key p.length le_rfl


omit [DecidableRel G.Adj] in
@[category API, AMS 5]
lemma region_pairwise {J J0 D D' : Finset α} {h h' : α} (hJ0 : J0 ⊆ J) (hh : h ∈ J0)
    (hh' : h' ∈ J0) (hne : h ≠ h') (hD : ValidRegion (G := G) J J0 h D)
    (hD' : ValidRegion (G := G) J J0 h' D') :
    h ∉ D' ∧ (∀ y ∈ D, y ∉ D') ∧ (∀ y ∈ D, ∀ y' ∈ D', ¬ G.Adj y y') := by
  have h1 : h ∉ D' := hD'.2.1 h (Finset.mem_erase.2 ⟨hne, hh⟩)
  have h1' : h' ∉ D := hD.2.1 h' (Finset.mem_erase.2 ⟨Ne.symm hne, hh'⟩)
  have h2 : ∀ y ∈ D, y ∉ D' := by
    intro y hy hy'
    obtain ⟨p, hp⟩ := hD.2.2.2.1 y (Finset.mem_insert_of_mem hy) h (Finset.mem_insert_self h D)
    have hp' : InS (J.erase h') p := by
      intro u hu
      have huR := hp u hu
      rcases Finset.mem_insert.1 huR with e | huD
      · rw [e]; exact Finset.mem_erase.2 ⟨hne, hJ0 hh⟩
      · exact Finset.mem_erase.2 ⟨fun e => h1' (e ▸ huD), Finset.mem_of_mem_erase (hD.1 huD)⟩
    exact h1 (hD'.2.2.1 y hy' h ⟨p, hp'⟩)
  refine ⟨h1, h2, ?_⟩
  intro y hy y' hy' hadj
  have hy'J : y' ∈ J.erase h :=
    Finset.mem_erase.2 ⟨fun e => h1 (e ▸ hy'), Finset.mem_of_mem_erase (hD'.1 hy')⟩
  exact h2 y' (hD.2.2.1 y hy y' ⟨_, inS_edge (hD.1 hy) hy'J hadj⟩) hy'

omit [DecidableRel G.Adj] in
@[category API, AMS 5]
lemma region_T {J J0 T D : Finset α} {h : α} (hJ0 : J0 ⊆ J) (hT : T ⊆ J0)
    (hD : ValidRegion (G := G) J J0 h D) :
    (∀ v ∈ D, v ∉ T) ∧ (∀ v ∈ D, ∀ w ∈ T, G.Adj v w → w = h) := by
  have h1 : ∀ v ∈ D, v ∉ T := by
    intro v hv hvT
    have hvh : v ≠ h := Finset.ne_of_mem_erase (hD.1 hv)
    exact hD.2.1 v (Finset.mem_erase.2 ⟨hvh, hT hvT⟩) hv
  refine ⟨h1, ?_⟩
  intro v hv w hw hadj
  by_contra hwh
  have hwJ : w ∈ J.erase h := Finset.mem_erase.2 ⟨hwh, hJ0 (hT hw)⟩
  exact h1 w (hD.2.2.1 v hv w ⟨_, inS_edge (hD.1 hv) hwJ hadj⟩) hw

omit [DecidableRel G.Adj] in
/-- Attach private geodesic branches at all vertices of `Hs`. -/
@[category API, AMS 5]
lemma extend {J J0 T : Finset α} (hJ : ConnS G J) (hJ0 : J0 ⊆ J) (hT : T ⊆ J0)
    (htree : (G.induce (T : Set α)).IsTree) (hT2 : 2 ≤ T.card) (Hs : Finset α)
    (hHs : Hs ⊆ T) (hcut : ∀ h ∈ Hs, ¬ ConnS G (J.erase h))
    (hconn : ∀ h ∈ Hs, ConnS G (J0.erase h)) :
    ∃ T' Z : Finset α, T ⊆ T' ∧ T' ⊆ J ∧ (G.induce (T' : Set α)).IsTree ∧
      T.card + Hs.card ≤ T'.card ∧ Z ⊆ T' ∧ Hs.card ≤ Z.card ∧
      ∀ z ∈ Z, ConnS G (J.erase z) := by
  have hTJ : T ⊆ J := hT.trans hJ0
  suffices H : ∃ T' Z : Finset α, T ⊆ T' ∧ T' ⊆ J ∧ (G.induce (T' : Set α)).IsTree ∧
      T.card + Hs.card ≤ T'.card ∧ Z ⊆ T' ∧ Hs.card ≤ Z.card ∧
      (∀ z ∈ Z, ConnS G (J.erase z)) ∧ (∀ z ∈ Z, z ∉ T) ∧
      (∀ v ∈ T', v ∉ T → ∃ h' ∈ Hs, ∃ D', ValidRegion (G := G) J J0 h' D' ∧ v ∈ D') by
    obtain ⟨T', Z, a1, a2, a3, a4, a5, a6, a7, -, -⟩ := H
    exact ⟨T', Z, a1, a2, a3, a4, a5, a6, a7⟩
  induction Hs using Finset.induction_on with
  | empty =>
    exact ⟨T, ∅, subset_rfl, hTJ, htree, by simp, by simp, by simp, by simp, by simp,
      fun v hv hvT => absurd hv hvT⟩
  | @insert h Hs hhs ih =>
    have hhT : h ∈ T := hHs (Finset.mem_insert_self h Hs)
    obtain ⟨T', Z, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ih
      ((Finset.subset_insert h Hs).trans hHs)
      (fun x hx => hcut x (Finset.mem_insert_of_mem hx))
      (fun x hx => hconn x (Finset.mem_insert_of_mem hx))
    have hWne : (J0.erase h).Nonempty := by
      obtain ⟨t, ht, hth⟩ := Finset.exists_mem_ne (by omega : 1 < T.card) h
      exact ⟨t, Finset.mem_erase.2 ⟨hth, hT ht⟩⟩
    obtain ⟨D, hD⟩ := private_region hJ (hTJ hhT) (hcut h (Finset.mem_insert_self h Hs)) hJ0
      (hconn h (Finset.mem_insert_self h Hs)) hWne
    obtain ⟨z, hzD, hzc, p, hp, hpl⟩ := tip_lemma hJ (hTJ hhT) hD
    obtain ⟨hDT, hDadj⟩ := region_T hJ0 hT hD
    have hRT : ∀ v ∈ insert h D, v ≠ h → v ∉ T' ∧ ∀ w ∈ T', G.Adj v w → w = h := by
      intro v hv hvh
      have hvD : v ∈ D := by
        rcases Finset.mem_insert.1 hv with e | e
        · exact absurd e hvh
        · exact e
      refine ⟨fun hvT' => ?_, fun w hw hadj => ?_⟩
      · by_cases hvT : v ∈ T
        · exact hDT v hvD hvT
        · obtain ⟨h', hh', D', hD', hvD'⟩ := a9 v hvT' hvT
          have hne : h ≠ h' := fun e => hhs (e ▸ hh')
          exact (region_pairwise hJ0 (hT hhT) (hT (hHs (Finset.mem_insert_of_mem hh'))) hne
            hD hD').2.1 v hvD hvD'
      · by_cases hwT : w ∈ T
        · exact hDadj v hvD w hwT hadj
        · obtain ⟨h', hh', D', hD', hwD'⟩ := a9 w hw hwT
          have hne : h ≠ h' := fun e => hhs (e ▸ hh')
          exact absurd hadj ((region_pairwise hJ0 (hT hhT)
            (hT (hHs (Finset.mem_insert_of_mem hh'))) hne hD hD').2.2 v hvD w hwD')
    have htree' := add_branch a3 (a1 hhT) p hp hpl hRT
    set B := (Finset.range (p.length + 1)).image p.getVert with hB
    have hzB : z ∈ B := by
      rw [hB, Finset.mem_image]
      exact ⟨p.length, by simp, Walk.getVert_length p⟩
    have hzT' : z ∉ T' :=
      (hRT z (Finset.mem_insert_of_mem hzD) (Finset.ne_of_mem_erase (hD.1 hzD))).1
    have hBR : ∀ v ∈ B, v ∈ insert h D := by
      intro v hv
      rw [hB, Finset.mem_image] at hv
      obtain ⟨i, -, rfl⟩ := hv
      exact hp.getVert i
    have hRJ : insert h D ⊆ J := by
      intro u hu
      rcases Finset.mem_insert.1 hu with e | hu
      · rw [e]; exact hTJ hhT
      · exact Finset.mem_of_mem_erase (hD.1 hu)
    refine ⟨T' ∪ B, insert z Z, a1.trans Finset.subset_union_left, ?_, htree', ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · exact Finset.union_subset a2 (fun v hv => hRJ (hBR v hv))
    · have hsub : insert z T' ⊆ T' ∪ B :=
        Finset.insert_subset (Finset.mem_union_right _ hzB) Finset.subset_union_left
      have h2 := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hzT'] at h2
      rw [Finset.card_insert_of_notMem hhs]
      omega
    · exact Finset.insert_subset (Finset.mem_union_right _ hzB)
        (a5.trans Finset.subset_union_left)
    · have hzZ : z ∉ Z := fun h' => hzT' (a5 h')
      rw [Finset.card_insert_of_notMem hzZ, Finset.card_insert_of_notMem hhs]
      omega
    · intro w hw
      rcases Finset.mem_insert.1 hw with e | hw
      · rw [e]; exact hzc
      · exact a7 w hw
    · intro w hw
      rcases Finset.mem_insert.1 hw with e | hw
      · rw [e]; exact hDT _ hzD
      · exact a8 w hw
    · intro v hv hvT
      rcases Finset.mem_union.1 hv with hv | hv
      · obtain ⟨h', hh', D', hD', hvD'⟩ := a9 v hv hvT
        exact ⟨h', Finset.mem_insert_of_mem hh', D', hD', hvD'⟩
      · have hvR := hBR v hv
        have hvh : v ≠ h := fun e => hvT (e ▸ hhT)
        refine ⟨h, Finset.mem_insert_self h Hs, D, hD, ?_⟩
        rcases Finset.mem_insert.1 hvR with e | e
        · exact absurd e hvh
        · exact e

omit [DecidableRel G.Adj] in
@[category API, AMS 5]
lemma connS_prefix (p : G.Walk a b) (i : ℕ) :
    ConnS G ((Finset.range (i + 1)).image p.getVert) := by
  refine conn_of_hub (c := a) ?_ ?_
  · rw [Finset.mem_image]
    exact ⟨0, by simp, Walk.getVert_zero p⟩
  · intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨j, hj, rfl⟩ := hv
    refine ⟨p.take j, fun w hw => ?_⟩
    obtain ⟨k, -, rfl⟩ := mem_support_getVert hw
    rw [Walk.take_getVert, Finset.mem_image]
    refine ⟨min j k, ?_, rfl⟩
    simp only [Finset.mem_range] at hj ⊢
    omega

/-- **Lemma Q.** If `H` has radius at least `q ≥ 1`, then there are a connected `J ⊆ H` and an
induced tree `T ⊆ J` such that `|T| + |Z| ≥ 2q + 2`, where `Z ⊆ T` consists of non-cut
vertices of `J` and `|Z| ≥ 2`. -/
@[category API, AMS 5]
lemma lemmaQ (q : ℕ) (hq : 1 ≤ q) : ∀ H : Finset α, RadGe G H q →
    ∃ J T Z : Finset α, J ⊆ H ∧ T ⊆ J ∧ ConnS G J ∧ (G.induce (T : Set α)).IsTree ∧
      Z ⊆ T ∧ 2 ≤ Z.card ∧ 2 * q + 2 ≤ T.card + Z.card ∧ ∀ z ∈ Z, ConnS G (J.erase z) := by
  induction q, hq using Nat.le_induction with
  | base =>
    intro H hH
    obtain ⟨a, ha⟩ := hH.1
    obtain ⟨b, hb, hab⟩ := hH.2.2 a ha
    obtain ⟨p, hp, hpl⟩ := dS_spec (hH.2.1 a ha b hb)
    obtain ⟨htree, hcard⟩ := geod_prefix_tree p hp hpl 1 (by omega)
    set T := (Finset.range (1 + 1)).image p.getVert with hT
    have hTH : T ⊆ H := by
      intro v hv
      rw [hT, Finset.mem_image] at hv
      obtain ⟨i, -, rfl⟩ := hv
      exact hp.getVert i
    refine ⟨T, T, T, hTH, subset_rfl, connS_prefix p 1, htree, subset_rfl, by omega, by omega,
      ?_⟩
    intro z hz
    have h1 : (T.erase z).card = 1 := by rw [Finset.card_erase_of_mem hz, hcard]
    obtain ⟨x, hx⟩ := Finset.card_eq_one.1 h1
    rw [hx]
    intro u hu v hv
    rw [Finset.mem_singleton] at hu hv
    subst hu
    subst hv
    exact ⟨Walk.nil, inS_nil (Finset.mem_singleton_self _)⟩
  | succ q hq ih =>
    intro H hH
    classical
    obtain ⟨J, hJF, hJmin⟩ := Finset.exists_min_image
      (H.powerset.filter (fun S => RadGe G S (q + 1))) Finset.card
      ⟨H, Finset.mem_filter.2 ⟨Finset.mem_powerset_self H, hH⟩⟩
    rw [Finset.mem_filter, Finset.mem_powerset] at hJF
    obtain ⟨hJH, hJ⟩ := hJF
    have hcrit : ∀ x ∈ J, ¬ RadGe G (J.erase x) (q + 1) := by
      intro x hx hr
      have h1 := hJmin (J.erase x) (Finset.mem_filter.2
        ⟨Finset.mem_powerset.2 ((Finset.erase_subset x J).trans hJH), hr⟩)
      rw [Finset.card_erase_of_mem hx] at h1
      have h2 : 0 < J.card := Finset.card_pos.2 ⟨x, hx⟩
      omega
    have hJ2 : ∀ x ∈ J, (J.erase x).Nonempty := by
      intro x hx
      obtain ⟨b, hb, hbd⟩ := hJ.2.2 x hx
      refine ⟨b, Finset.mem_erase.2 ⟨?_, hb⟩⟩
      rintro rfl
      rw [dS_self hx] at hbd
      omega
    by_cases hcase : ∃ x ∈ J, ConnS G (J.erase x) ∧ 2 ≤ degS G J x
    · obtain ⟨x0, hx0, hx0P⟩ := hcase
      have hall := propagate (fun v => ConnS G (J.erase v) ∧ 2 ≤ degS G J v) hx0 hJ.2.1 hx0P
        (fun x hx y hy hPx hxy =>
          closure_step (by omega) hJ hx hPx.1 (hJ2 x hx) (hcrit x hx) hPx.2 hy hxy)
      obtain ⟨a, ha⟩ := hJ.1
      obtain ⟨b, hb, hab⟩ := hJ.2.2 a ha
      obtain ⟨p, hp, hpl⟩ := dS_spec (hJ.2.1 a ha b hb)
      obtain ⟨htree, hcard⟩ := geod_prefix_tree p hp hpl (q + 1) (by omega)
      set T := (Finset.range (q + 1 + 1)).image p.getVert with hT
      have hTJ : T ⊆ J := by
        intro v hv
        rw [hT, Finset.mem_image] at hv
        obtain ⟨i, -, rfl⟩ := hv
        exact hp.getVert i
      exact ⟨J, T, T, hJH, hTJ, hJ.2.1, htree, subset_rfl, by omega, by omega,
        fun z hz => (hall z (hTJ hz)).1⟩
    · push Not at hcase
      have hstrip := strip hq hJ
      obtain ⟨J'', T, Z, hJ''sub, hTJ'', -, htree, hZT, hZ2, hcount, hZc⟩ := ih _ hstrip
      have hJ''J : J'' ⊆ J := hJ''sub.trans (Finset.filter_subset _ _)
      have hT2 : 2 ≤ T.card := hZ2.trans (Finset.card_le_card hZT)
      obtain ⟨T', Z', h1, h2, h3, h4, h5, h6, h7⟩ := extend hJ.2.1 hJ''J hTJ'' htree hT2 Z hZT
        (fun z hz hc => by
          have hzJ' := hJ''sub (hTJ'' (hZT hz))
          rw [Finset.mem_filter] at hzJ'
          have := hcase z hzJ'.1 hc
          omega)
        hZc
      exact ⟨J, T', Z', hJH, h2, hJ.2.1, h3, h5, by omega, by omega, h7⟩

variable [Fintype α]

/-- **Main lemma.** A graph with a vertex of degree one and radius at least `r ≥ 2` has an
induced tree on at least `2r` vertices. -/
@[category API, AMS 5]
lemma main_leaf {r : ℕ} (hr : 2 ≤ r) (hG : RadGe G Finset.univ r) {l : α}
    (hl : G.degree l = 1) : ∃ T : Finset α, (G.induce (T : Set α)).IsTree ∧ 2 * r ≤ T.card := by
  classical
  obtain ⟨K, hKF, hKmin⟩ := Finset.exists_min_image
    ((Finset.univ : Finset α).powerset.filter (fun S => l ∈ S ∧ RadGe G S r)) Finset.card
    ⟨Finset.univ, Finset.mem_filter.2 ⟨Finset.mem_powerset_self _, Finset.mem_univ l, hG⟩⟩
  rw [Finset.mem_filter] at hKF
  obtain ⟨-, hlK, hK⟩ := hKF
  have hcrit : ∀ x ∈ K, x ≠ l → ¬ RadGe G (K.erase x) r := by
    intro x hx hxl hr'
    have h1 := hKmin (K.erase x) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2
      (Finset.subset_univ _), Finset.mem_erase.2 ⟨Ne.symm hxl, hlK⟩, hr'⟩)
    rw [Finset.card_erase_of_mem hx] at h1
    have h2 : 0 < K.card := Finset.card_pos.2 ⟨x, hx⟩
    omega
  have hK2 : ∀ x ∈ K, (K.erase x).Nonempty := by
    intro x hx
    obtain ⟨b, hb, hbd⟩ := hK.2.2 x hx
    refine ⟨b, Finset.mem_erase.2 ⟨?_, hb⟩⟩
    rintro rfl
    rw [dS_self hx] at hbd
    omega
  have hdegl : degS G K l ≤ 1 := by
    rw [← hl]
    unfold degS
    apply Finset.card_le_card
    intro v hv
    rw [Finset.mem_filter] at hv
    rw [mem_neighborFinset]
    exact hv.2
  have hB : ∀ x ∈ K, x ≠ l → ConnS G (K.erase x) → degS G K x < 2 := by
    intro x hx hxl hxc
    by_contra hdeg
    push Not at hdeg
    have hall := propagate (fun v => v ≠ l ∧ ConnS G (K.erase v) ∧ 2 ≤ degS G K v) hx hK.2.1
      ⟨hxl, hxc, hdeg⟩
      (fun x hx y hy hPx hxy => by
        obtain ⟨h1, h2⟩ := closure_step (by omega) hK hx hPx.2.1 (hK2 x hx)
          (hcrit x hx hPx.1) hPx.2.2 hy hxy
        refine ⟨?_, h1, h2⟩
        rintro rfl
        omega)
    exact (hall l hlK).1 rfl
  have hstrip := strip (q := r - 1) (by omega)
    (by rwa [Nat.sub_add_cancel (by omega : 1 ≤ r)])
  obtain ⟨J, T, Z, hJsub, hTJ, -, htree, hZT, hZ2, hcount, hZc⟩ :=
    lemmaQ (r - 1) (by omega) _ hstrip
  have hJK : J ⊆ K := hJsub.trans (Finset.filter_subset _ _)
  have hT2 : 2 ≤ T.card := hZ2.trans (Finset.card_le_card hZT)
  obtain ⟨T', Z', -, -, h3, h4, -, -, -⟩ := extend hK.2.1 hJK hTJ htree hT2 Z hZT
    (fun z hz hc => by
      have hzK' := hJsub (hTJ (hZT hz))
      rw [Finset.mem_filter] at hzK'
      have hzl : z ≠ l := by
        rintro rfl
        omega
      have := hB z hzK'.1 hzl hc
      omega)
    hZc
  exact ⟨T', h3, by omega⟩

omit [DecidableRel G.Adj] [DecidableEq α] in
@[category API, AMS 5]
lemma radGe_univ [Nonempty α] (hG : G.Connected) : RadGe G Finset.univ G.radius.toNat := by
  have hconn : ConnS G Finset.univ := by
    intro a _ b _
    obtain ⟨p⟩ := hG.preconnected a b
    exact ⟨p, fun v _ => Finset.mem_univ v⟩
  refine ⟨Finset.univ_nonempty, hconn, ?_⟩
  intro a _
  obtain ⟨b, hb⟩ := G.exists_edist_eq_eccent_of_finite a
  refine ⟨b, Finset.mem_univ b, ?_⟩
  obtain ⟨p, -, hpl⟩ := dS_spec (hconn a (Finset.mem_univ a) b (Finset.mem_univ b))
  have h1 : G.dist a b ≤ p.length := G.dist_le p
  have h2 : G.radius ≤ G.eccent a := G.radius_le_eccent
  have h3 : G.edist a b ≠ ⊤ := edist_ne_top_iff_reachable.2 (hG.preconnected a b)
  rw [← hb] at h2
  have h4 : G.radius.toNat ≤ (G.edist a b).toNat := ENat.toNat_le_toNat h2 h3
  have h5 : (G.edist a b).toNat = G.dist a b := rfl
  omega

/-- The full inequality behind WOWII Conjecture 84. -/
@[category API, AMS 5]
lemma exists_tree [Nontrivial α] (hG : G.Connected) (hδ : 0 < G.minDegree) :
    ∃ T : Finset α, (G.induce (T : Set α)).IsTree ∧
      2 * (G.radius.toNat : ℝ) / (G.minDegree : ℝ) ≤ T.card := by
  have hrad := radGe_univ hG
  set r := G.radius.toNat with hr
  -- a geodesic gives an induced path on `r + 1` vertices
  have hpath : ∃ T : Finset α, (G.induce (T : Set α)).IsTree ∧ r + 1 ≤ T.card := by
    obtain ⟨a, ha⟩ := hrad.1
    obtain ⟨b, hb, hab⟩ := hrad.2.2 a ha
    obtain ⟨p, hp, hpl⟩ := dS_spec (hrad.2.1 a ha b hb)
    obtain ⟨htree, hcard⟩ := geod_prefix_tree p hp hpl r (by omega)
    exact ⟨_, htree, hcard.ge⟩
  have hδpos : (0 : ℝ) < G.minDegree := by exact_mod_cast hδ
  rcases Nat.lt_or_ge G.minDegree 2 with hδ1 | hδ2
  · have hδeq : G.minDegree = 1 := by omega
    obtain ⟨l, hl⟩ := G.exists_minimal_degree_vertex
    rw [hδeq] at hl
    rcases Nat.lt_or_ge r 2 with hr1 | hr2
    · obtain ⟨T, hT, hc⟩ := hpath
      refine ⟨T, hT, ?_⟩
      rw [hδeq, Nat.cast_one, div_one]
      have : (2 * r : ℕ) ≤ T.card := by omega
      exact_mod_cast this
    · obtain ⟨T, hT, hc⟩ := main_leaf hr2 hrad hl.symm
      refine ⟨T, hT, ?_⟩
      rw [hδeq, Nat.cast_one, div_one]
      exact_mod_cast hc
  · obtain ⟨T, hT, hc⟩ := hpath
    refine ⟨T, hT, ?_⟩
    rw [div_le_iff₀ hδpos]
    have h1 : (2 : ℝ) ≤ G.minDegree := by exact_mod_cast hδ2
    have h2 : ((r : ℕ) : ℝ) + 1 ≤ T.card := by exact_mod_cast hc
    have h3 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    nlinarith

end Proof

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 84](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj84)
(status O):

For a simple connected graph `G` with positive minimum degree,
`tree(G) ≥ 2 · rad(G) / δ(G)`,
where `tree(G)` is the number of vertices in a largest induced subtree,
`rad(G)` is the radius, and `δ(G) = G.minDegree` is the minimum degree.

The hypothesis `0 < G.minDegree` follows from connectedness on a nontrivial
vertex set, but is stated explicitly so the theorem reads as a real-valued
inequality without `x / 0` corner cases.
-/
@[category research solved, AMS 5]
theorem conjecture84 (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) (hδ : 0 < G.minDegree) :
    2 * (G.radius.toNat : ℝ) / (G.minDegree : ℝ) ≤ (largestInducedTreeSize G : ℝ) := by
  obtain ⟨T, hT, hc⟩ := exists_tree h hδ
  exact hc.trans (by exact_mod_cast card_le_largestInducedTreeSize hT)

-- Sanity checks

/-- The `largestInducedTreeSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ largestInducedTreeSize G := Nat.zero_le _

/-- The largest induced tree size is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ (largestInducedTreeSize G : ℝ) :=
  Nat.cast_nonneg _

end WrittenOnTheWallII.GraphConjecture84
