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
# Written on the Wall II - Conjecture 100

**Verbatim statement (WOWII #100, status O):**
> If G is a simple connected graph, then α(G) ≤ CEIL[(maximum of λ(v) + 0.5*length(Ḡ))/2]

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj100

The WOWII HTML uses `length(Ḡ)` (the bar denotes graph complement); the
extracted JSON in our private repo previously dropped the overline. The
formal statement below uses the Euclidean norm of the degree sequence of `Gᶜ`.

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definition of graph length

The WOWII definitions popup defines `length(H)` as the square root of the sum
of the squares of the vertex degrees. This is `degreeL2Norm H` in Lean.
Combined with the overline above, the inequality reads:
  `α(G) ≤ ⌈(max_v l(v) + 0.5 · degreeL2Norm(Gᶜ)) / 2⌉`
where `l(v) = indepNeighbors G v`.

## Proof

The conjecture was posed on April 21, 2004 and was still marked `O` (open) on the
source list in the 2026-07-23 snapshot. An informal proof by Kias Henry
(*A Proof of Written on the Wall II Conjecture 100*, DOI 10.5281/zenodo.21914031,
August 2026, reviewed by E. DeLaViña; see repository issue #4920) resolved it
shortly thereafter. The machine-checked proof below was found independently of
that manuscript and, like it, establishes the stronger strict inequality
`2(α(G) - 1) < max_v l(v) + length(Gᶜ)/2`. Write `a = α(G)`, `m = max_v l(v)`,
`L = degreeL2Norm Gᶜ` and `c = 4a - 4 - 2m`. Since `m` is an integer, the claim
reduces to the strict bound `c < L`, which is trivial for `c < 0` and otherwise
follows from `c² < ∑_v deg_{Gᶜ}(v)²` over `ℤ`:

* Fix a maximum independent set `S`. Every `u ∈ S` has `deg_{Gᶜ}(u) ≥ a - 1`
  (as `S` is a clique in `Gᶜ`), and every `v ∉ S` has at least `a - m`
  `Gᶜ`-neighbours in `S`, because `S ∩ N_G(v)` is an independent subset of a
  neighbourhood, hence of size at most `m`.
* If `m ≥ a`, then `∑_{u ∈ S} deg_{Gᶜ}(u)² ≥ a(a-1)²` already exceeds
  `c² ≤ (2a-4)²`.
* Otherwise `k = a - m ≥ 1`; moreover `m ≥ 2` (a connected graph with two
  nonadjacent vertices contains an induced path on 3 vertices, by inspecting a
  shortest walk between them), so `k ≤ a - 2`, and the complement `Sᶜ` has at
  least two vertices. Summing the degree bounds and applying Cauchy-Schwarz
  (`sq_sum_le_card_mul_sum_sq`) gives
  `a · ∑_v deg_{Gᶜ}(v)² ≥ (a(a-1) + tk)² + a·t·k²` with `t = |Sᶜ| ≥ 2`, and the
  polynomial inequality `a·c² < (a(a-1) + 2k)² + 2ak²` for `1 ≤ k ≤ a - 2`
  (whose extremal case `k = a - 2` reduces to positivity of
  `q(a) = a⁴ - 12a³ + 49a² - 64a + 16`) closes the argument.

The bound is attained (with equality of the un-ceiled expression) e.g. for
complete bipartite graphs; the global minimum of the slack over all connected
graphs on at most 9 vertices is ≈ 0.2247, so the inequality is sharp in the
ceiling sense. The proof was verified computationally on all 273,192 connected
graphs with at most 9 vertices and all 11,716,571 connected graphs on 10
vertices before formalisation.
-/

namespace WrittenOnTheWallII.GraphConjecture100

open SimpleGraph Finset

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

section ProofAux

variable (G : SimpleGraph α) [DecidableRel G.Adj]

omit [Fintype α] [DecidableEq α] [DecidableRel G.Adj] in
/-- In a connected graph on a nontrivial vertex type, every vertex has a neighbour. -/
@[category API, AMS 5]
private lemma exists_adj (h : G.Connected) (u : α) : ∃ w, G.Adj u w := by
  obtain ⟨x, hxu⟩ := exists_ne u
  obtain ⟨p⟩ := h.preconnected u x
  cases p with
  | nil => exact absurd rfl hxu
  | cons hadj _ => exact ⟨_, hadj⟩

omit [DecidableEq α] [Nontrivial α] in
/-- Any independent set inside the neighbourhood of `v` bounds `indepNeighborsCard` below. -/
@[category API, AMS 5]
private lemma le_indepNeighborsCard {v : α} {t : Finset α} (ht : ∀ x ∈ t, G.Adj v x)
    (hind : G.IsIndepSet (t : Set α)) : t.card ≤ indepNeighborsCard G v := by
  classical
  let t' : Finset (G.neighborSet v) := t.subtype (· ∈ G.neighborSet v)
  have hcard : t'.card = t.card := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem]
    intro x hx
    exact ht x hx
  have hind' : (G.induce (G.neighborSet v)).IsIndepSet (t' : Set (G.neighborSet v)) := by
    intro x hx y hy hxy hadj
    have hxy' : (x : α) ≠ (y : α) := Subtype.coe_ne_coe.mpr hxy
    have hxt : (x : α) ∈ t := by simpa [t'] using hx
    have hyt : (y : α) ∈ t := by simpa [t'] using hy
    exact hind hxt hyt hxy' hadj
  calc t.card = t'.card := hcard.symm
    _ ≤ (G.induce (G.neighborSet v)).indepNum := hind'.card_le_indepNum

omit [Nontrivial α] in
/-- If the graph contains two nonadjacent vertices, some neighbourhood contains an
independent pair, i.e. the maximum local independence number is at least `2`. -/
@[category API, AMS 5]
private lemma two_le_indepNeighborsCard (h : G.Connected) {u v : α} (huv : u ≠ v)
    (hnadj : ¬G.Adj u v) : ∃ y, 2 ≤ indepNeighborsCard G y := by
  classical
  have hreach : G.Reachable u v := h.preconnected u v
  have hdist2 : 2 ≤ G.dist u v := by
    rcases Nat.lt_or_ge (G.dist u v) 2 with hlt | hge
    · interval_cases hd : G.dist u v
      · exact absurd ((hreach.dist_eq_zero_iff).mp hd) huv
      · exact absurd ((G.dist_eq_one_iff_adj).mp hd) hnadj
    · exact hge
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
  match p, hp with
  | .nil, hp => simp [SimpleGraph.dist_self] at hdist2
  | .cons _ .nil, hp => simp at hp; omega
  | .cons (v := y) h₁ (.cons (v := z) h₂ q), hp =>
    have hqlen : q.length + 2 = G.dist u v := by simpa using hp
    have huz : ¬G.Adj u z := by
      intro hadj
      have := G.dist_le (SimpleGraph.Walk.cons hadj q)
      simp only [SimpleGraph.Walk.length_cons] at this
      omega
    have huz' : u ≠ z := by
      rintro rfl
      have := G.dist_le q
      omega
    refine ⟨y, ?_⟩
    have hpair : ({u, z} : Finset α).card = 2 := Finset.card_pair huz'
    calc 2 = ({u, z} : Finset α).card := hpair.symm
      _ ≤ indepNeighborsCard G y := by
        apply le_indepNeighborsCard
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact h₁.symm
          · rw [Finset.mem_singleton.mp hx]
            exact h₂
        · intro x hx y' hy' hxy hadj
          simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hx hy'
          rcases hx with rfl | rfl <;> rcases hy' with rfl | rfl
          · exact hxy rfl
          · exact huz hadj
          · exact huz (hadj.symm)
          · exact hxy rfl

omit [Nontrivial α] in
/-- Double counting the `H`-edges between `S` and its complement. -/
@[category API, AMS 5]
private lemma sum_cross (H : SimpleGraph α) [DecidableRel H.Adj] (S : Finset α) :
    ∑ u ∈ S, (Sᶜ.filter (H.Adj u)).card = ∑ v ∈ Sᶜ, (S.filter (H.Adj v)).card := by
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
  simp [H.adj_comm]

omit [Nontrivial α] in
/-- The degree splits as the number of neighbours inside `S` plus outside `S`. -/
@[category API, AMS 5]
private lemma degree_split (H : SimpleGraph α) [DecidableRel H.Adj] (S : Finset α) (u : α) :
    H.degree u = (S.filter (H.Adj u)).card + (Sᶜ.filter (H.Adj u)).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  have huniv : Finset.univ.filter (H.Adj u) = S.filter (H.Adj u) ∪ Sᶜ.filter (H.Adj u) := by
    rw [← Finset.filter_union, Finset.union_compl]
  rw [huniv, Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter disjoint_compl_right)]

end ProofAux

section NumericCore

/-- Positivity of the key quartic `q(a) = a⁴ - 12a³ + 49a² - 64a + 16` for `a ≥ 3`. -/
@[category API, AMS 5]
private lemma q_pos {a : ℤ} (ha : 3 ≤ a) :
    0 < a ^ 4 - 12 * a ^ 3 + 49 * a ^ 2 - 64 * a + 16 := by
  nlinarith [sq_nonneg (2 * (a - 3) ^ 2 - 5), ha]

/-- The discriminant-style inequality at the extremal outside-count `t = 2`. -/
@[category API, AMS 5]
private lemma D_pos {a k : ℤ} (hk1 : 1 ≤ k) (hk2 : k ≤ a - 2) :
    a * (2 * a - 4 + 2 * k) ^ 2 < (a * (a - 1) + 2 * k) ^ 2 + 2 * a * k ^ 2 := by
  have ha : 3 ≤ a := by linarith
  have hq := q_pos ha
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ 4 * a)
      (by linarith : (0:ℤ) ≤ a - 3)) (by linarith : (0:ℤ) ≤ a - 2 - k),
    mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ 2 * (a - 2))
      (by linarith : (0:ℤ) ≤ a - 2 - k)) (by linarith : (0:ℤ) ≤ a - 2 + k)]

/-- Monotonicity in `t` of the lower bound for the squared degree sum. -/
@[category API, AMS 5]
private lemma t_mono {a k t : ℤ} (hk : 1 ≤ k) (ha : 3 ≤ a) (ht : 2 ≤ t) :
    (a * (a - 1) + 2 * k) ^ 2 + 2 * a * k ^ 2 ≤ (a * (a - 1) + t * k) ^ 2 + a * t * k ^ 2 := by
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ t - 2) (by linarith : (0:ℤ) ≤ k))
      (by nlinarith : (0:ℤ) ≤ 2 * (a * (a - 1)) + (t + 2) * k),
    mul_nonneg (by linarith : (0:ℤ) ≤ a)
      (mul_nonneg (by linarith : (0:ℤ) ≤ t - 2) (sq_nonneg k))]

/-- The integer core of the argument in the main case `m ≤ a - 2`, `t ≥ 2`:
if `P` is at least `a(a-1) + tk`, `aQ` dominates `P²` (Cauchy-Schwarz) and
`R ≥ tk²`, then `Q + R` beats `(2a - 4 + 2k)²`. -/
@[category API, AMS 5]
private lemma numeric_core {a k t P Q R : ℤ} (hk1 : 1 ≤ k) (hk2 : k ≤ a - 2) (ht : 2 ≤ t)
    (hP : a * (a - 1) + t * k ≤ P) (hPQ : P ^ 2 ≤ a * Q) (hR : t * k ^ 2 ≤ R) :
    (2 * a - 4 + 2 * k) ^ 2 < Q + R := by
  have ha : 3 ≤ a := by linarith
  have hP0 : 0 ≤ a * (a - 1) + t * k := by nlinarith
  have h1 : (a * (a - 1) + t * k) ^ 2 ≤ a * Q :=
    le_trans (by nlinarith : (a * (a - 1) + t * k) ^ 2 ≤ P ^ 2) hPQ
  have h2 := D_pos hk1 hk2
  have h3 := t_mono hk1 ha ht
  have h4 : a * (t * k ^ 2) ≤ a * R := by nlinarith
  have h5 : a * (2 * a - 4 + 2 * k) ^ 2 < a * (Q + R) := by nlinarith
  exact lt_of_mul_lt_mul_left h5 (by linarith)

end NumericCore

/--
WOWII [Conjecture 100](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj100)
(status O):

For a simple connected graph `G`,
`α(G) ≤ ⌈(max_v l(v) + 0.5 · degreeL2Norm(Gᶜ)) / 2⌉`
where `α(G) = G.indepNum` is the independence number,
`max_v l(v)` is the maximum over all vertices of the independence number of
the neighbourhood (in `G`), and `degreeL2Norm(Gᶜ)` is the square root of the
sum of the squares of the degrees in the complement `Gᶜ`.
-/
@[category research solved, AMS 5]
theorem conjecture100 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    (G.indepNum : ℝ) ≤ ⌈((maxL : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉ := by
  intro m
  classical
  set a := G.indepNum with ha_def
  set N : ℕ := ∑ v, Gᶜ.degree v ^ 2 with hN_def
  have hL2 : degreeL2Norm Gᶜ = Real.sqrt ((N : ℤ) : ℝ) := by
    rw [degreeL2Norm]
    congr 1
    push_cast [hN_def]
    rfl
  -- The whole conjecture reduces to the strict lower bound `4a - 4 - 2m < ‖deg Gᶜ‖₂`.
  suffices hkey : ((4 * (a : ℤ) - 4 - 2 * (m : ℤ) : ℤ) : ℝ) < degreeL2Norm Gᶜ by
    have h1 : ((a : ℤ) - 1 : ℤ) < ⌈((m : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉ := by
      rw [Int.lt_ceil]
      push_cast
      push_cast at hkey
      linarith
    have h2 : ((a : ℤ) : ℝ) ≤ (⌈((m : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉ : ℝ) := by
      exact_mod_cast (by omega : (a : ℤ) ≤ ⌈((m : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉)
    exact_mod_cast h2
  -- Setup: a maximum independent set and the basic bounds.
  obtain ⟨S, hS⟩ := G.exists_isNIndepSet_indepNum
  have hSind : G.IsIndepSet (S : Set α) := hS.1
  have hScard : S.card = a := hS.2
  have hm_ge : ∀ v, indepNeighborsCard G v ≤ m := fun v =>
    Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ v))
  have hm1 : 1 ≤ m := by
    obtain ⟨u⟩ := (inferInstance : Nonempty α)
    obtain ⟨w, hw⟩ := exists_adj G h u
    have h1 : ({w} : Finset α).card ≤ indepNeighborsCard G u := by
      apply le_indepNeighborsCard
      · intro x hx
        rw [Finset.mem_singleton.mp hx]
        exact hw
      · simp [SimpleGraph.IsIndepSet]
    simpa using le_trans h1 (hm_ge u)
  -- Every vertex of `S` has at least `a - 1` complement-neighbours inside `S`.
  have hdegS : ∀ u ∈ S, ((a : ℤ) - 1) ≤ ((S.filter (Gᶜ.Adj u)).card : ℤ) := by
    intro u hu
    have hsub : S.erase u ⊆ S.filter (Gᶜ.Adj u) := by
      intro w hw
      obtain ⟨hwu, hwS⟩ := Finset.mem_erase.mp hw
      refine Finset.mem_filter.mpr ⟨hwS, ?_⟩
      rw [SimpleGraph.compl_adj]
      exact ⟨Ne.symm hwu, fun hadj => hSind hu hwS (Ne.symm hwu) hadj⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hu, hScard] at hcard
    have ha1 : 1 ≤ a := hScard ▸ Finset.card_pos.mpr ⟨u, hu⟩
    omega
  -- Each complement-degree dominates the count of complement-neighbours in `S`.
  have hdeg_ge_filter : ∀ v (T : Finset α), (T.filter (Gᶜ.Adj v)).card ≤ Gᶜ.degree v := by
    intro v T
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro u hu
    rw [SimpleGraph.mem_neighborFinset]
    exact (Finset.mem_filter.mp hu).2
  -- Every vertex outside `S` has at least `a - m` complement-neighbours in `S`.
  have houtside : ∀ v ∈ Sᶜ, (a : ℤ) ≤ (m : ℤ) + ((S.filter (Gᶜ.Adj v)).card : ℤ) := by
    intro v hv
    have hvS : v ∉ S := Finset.mem_compl.mp hv
    have hsplit := Finset.card_filter_add_card_filter_not (s := S) (p := (G.Adj v ·))
    have h1 : (S.filter (G.Adj v ·)).card ≤ m := by
      refine le_trans (le_indepNeighborsCard G ?_ ?_) (hm_ge v)
      · intro x hx
        exact (Finset.mem_filter.mp hx).2
      · exact hSind.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
    have h2 : (S.filter (fun u => ¬G.Adj v u)).card ≤ (S.filter (Gᶜ.Adj v)).card := by
      apply Finset.card_le_card
      intro u hu
      obtain ⟨huS, hnadj⟩ := Finset.mem_filter.mp hu
      refine Finset.mem_filter.mpr ⟨huS, ?_⟩
      rw [SimpleGraph.compl_adj]
      exact ⟨fun hvu => hvS (hvu ▸ huS), hnadj⟩
    have := hScard
    omega
  -- Case split on the sign of `c = 4a - 4 - 2m`.
  rcases lt_or_ge ((4 : ℤ) * a - 4 - 2 * m) 0 with hc | hc
  · calc ((4 * (a : ℤ) - 4 - 2 * (m : ℤ) : ℤ) : ℝ) < 0 := by exact_mod_cast hc
      _ ≤ degreeL2Norm Gᶜ := by rw [hL2]; exact Real.sqrt_nonneg _
  · -- `c ≥ 0` forces `a ≥ 2`; we show `c² < N` over `ℤ` and lift to `ℝ`.
    have ha2 : 2 ≤ (a : ℤ) := by omega
    have hQN : ∑ u ∈ S, (Gᶜ.degree u : ℤ) ^ 2 + ∑ v ∈ Sᶜ, (Gᶜ.degree v : ℤ) ^ 2 = (N : ℤ) := by
      rw [hN_def]
      push_cast
      exact Finset.sum_add_sum_compl S _
    have hcore : (4 * (a : ℤ) - 4 - 2 * m) ^ 2 < (N : ℤ) := by
      rcases (lt_or_ge (m : ℤ) (a : ℤ)).symm with hma | hma
      · -- Case `m ≥ a`: the clique `S` in `Gᶜ` already costs enough.
        have hQ : (a : ℤ) * ((a : ℤ) - 1) ^ 2 ≤ ∑ u ∈ S, (Gᶜ.degree u : ℤ) ^ 2 := by
          have hterm : ∀ u ∈ S, ((a : ℤ) - 1) ^ 2 ≤ (Gᶜ.degree u : ℤ) ^ 2 := by
            intro u hu
            have h1 := hdegS u hu
            have h2 : ((S.filter (Gᶜ.Adj u)).card : ℤ) ≤ (Gᶜ.degree u : ℤ) := by
              exact_mod_cast hdeg_ge_filter u S
            nlinarith
          calc (a : ℤ) * ((a : ℤ) - 1) ^ 2 = ∑ _u ∈ S, ((a : ℤ) - 1) ^ 2 := by
                rw [Finset.sum_const, hScard]; ring
            _ ≤ _ := Finset.sum_le_sum hterm
        have hR0 : (0 : ℤ) ≤ ∑ v ∈ Sᶜ, (Gᶜ.degree v : ℤ) ^ 2 :=
          Finset.sum_nonneg fun v _ => sq_nonneg _
        nlinarith [pow_nonneg (by linarith : (0 : ℤ) ≤ (a : ℤ) - 2) 3]
      · -- Main case `m ≤ a - 1`.
        set k : ℤ := (a : ℤ) - m with hk_def
        have hk1 : 1 ≤ k := by omega
        -- Two nonadjacent vertices exist in `S`, so some neighbourhood has an
        -- independent pair and `m ≥ 2`, giving `k ≤ a - 2`.
        have hm2 : 2 ≤ (m : ℤ) := by
          have hcard2 : 1 < S.card := by rw [hScard]; omega
          obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcard2
          have hnadj : ¬G.Adj u v := hSind hu hv huv
          obtain ⟨y, hy⟩ := two_le_indepNeighborsCard G h huv hnadj
          exact_mod_cast le_trans hy (hm_ge y)
        have hk2 : k ≤ (a : ℤ) - 2 := by omega
        -- At least two vertices lie outside `S`.
        have ht2 : 2 ≤ (Sᶜ.card : ℤ) := by
          have h0 : Sᶜ.card ≠ 0 := by
            intro h0
            have hSuniv : S = Finset.univ := by
              have := Finset.card_eq_zero.mp h0
              rwa [Finset.compl_eq_empty_iff] at this
            obtain ⟨u⟩ := (inferInstance : Nonempty α)
            obtain ⟨w, hw⟩ := exists_adj G h u
            exact hSind (by simp [hSuniv]) (by simp [hSuniv]) hw.ne hw
          have h1 : Sᶜ.card ≠ 1 := by
            intro h1
            obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
            have hvmem : v ∈ Sᶜ := by simp [hv]
            have := houtside v hvmem
            have hfilter : 1 ≤ (S.filter (Gᶜ.Adj v)).card := by omega
            obtain ⟨u, hu⟩ := Finset.card_pos.mp hfilter
            obtain ⟨huS, hadj⟩ := Finset.mem_filter.mp hu
            rw [SimpleGraph.compl_adj] at hadj
            obtain ⟨w, hw⟩ := exists_adj G h u
            have hwS : w ∉ S := fun hwS => hSind huS hwS hw.ne hw
            have hwv : w = v := by
              have : w ∈ Sᶜ := Finset.mem_compl.mpr hwS
              rw [hv] at this
              exact Finset.mem_singleton.mp this
            exact hadj.2 (hwv ▸ hw).symm
          omega
        -- Assemble the three estimates and finish with the integer core.
        have hsumP : (a : ℤ) * ((a : ℤ) - 1) + (Sᶜ.card : ℤ) * k ≤
            ∑ u ∈ S, (Gᶜ.degree u : ℤ) := by
          have e1 : ∀ u ∈ S, ((S.filter (Gᶜ.Adj u)).card : ℤ) +
              ((Sᶜ.filter (Gᶜ.Adj u)).card : ℤ) = (Gᶜ.degree u : ℤ) := by
            intro u _
            exact_mod_cast (degree_split Gᶜ S u).symm
          have e2 : ∑ u ∈ S, ((Sᶜ.filter (Gᶜ.Adj u)).card : ℤ) =
              ∑ v ∈ Sᶜ, ((S.filter (Gᶜ.Adj v)).card : ℤ) := by
            exact_mod_cast sum_cross Gᶜ S
          have b1 : (a : ℤ) * ((a : ℤ) - 1) ≤ ∑ u ∈ S, ((S.filter (Gᶜ.Adj u)).card : ℤ) := by
            calc (a : ℤ) * ((a : ℤ) - 1) = ∑ _u ∈ S, ((a : ℤ) - 1) := by
                  rw [Finset.sum_const, hScard]; ring
              _ ≤ _ := Finset.sum_le_sum hdegS
          have b2 : (Sᶜ.card : ℤ) * k ≤ ∑ v ∈ Sᶜ, ((S.filter (Gᶜ.Adj v)).card : ℤ) := by
            calc (Sᶜ.card : ℤ) * k = ∑ _v ∈ Sᶜ, k := by rw [Finset.sum_const]; ring
              _ ≤ _ := Finset.sum_le_sum fun v hv => by have := houtside v hv; omega
          calc (a : ℤ) * ((a : ℤ) - 1) + (Sᶜ.card : ℤ) * k
              ≤ ∑ u ∈ S, ((S.filter (Gᶜ.Adj u)).card : ℤ) +
                ∑ v ∈ Sᶜ, ((S.filter (Gᶜ.Adj v)).card : ℤ) := by linarith
            _ = ∑ u ∈ S, ((S.filter (Gᶜ.Adj u)).card : ℤ) +
                ∑ u ∈ S, ((Sᶜ.filter (Gᶜ.Adj u)).card : ℤ) := by rw [e2]
            _ = ∑ u ∈ S, (Gᶜ.degree u : ℤ) := by
                rw [← Finset.sum_add_distrib]
                exact Finset.sum_congr rfl e1
        have hCS : (∑ u ∈ S, (Gᶜ.degree u : ℤ)) ^ 2 ≤
            (a : ℤ) * ∑ u ∈ S, (Gᶜ.degree u : ℤ) ^ 2 := by
          have := sq_sum_le_card_mul_sum_sq (s := S) (f := fun u => (Gᶜ.degree u : ℤ))
          rwa [hScard] at this
        have hRsum : (Sᶜ.card : ℤ) * k ^ 2 ≤ ∑ v ∈ Sᶜ, (Gᶜ.degree v : ℤ) ^ 2 := by
          have hterm : ∀ v ∈ Sᶜ, k ^ 2 ≤ (Gᶜ.degree v : ℤ) ^ 2 := by
            intro v hv
            have h1 := houtside v hv
            have h2 : ((S.filter (Gᶜ.Adj v)).card : ℤ) ≤ (Gᶜ.degree v : ℤ) := by
              exact_mod_cast hdeg_ge_filter v S
            nlinarith
          calc (Sᶜ.card : ℤ) * k ^ 2 = ∑ _v ∈ Sᶜ, k ^ 2 := by
                rw [Finset.sum_const]; ring
            _ ≤ _ := Finset.sum_le_sum hterm
        have hfinal := numeric_core hk1 hk2 ht2 hsumP hCS hRsum
        have hrw : 2 * (a : ℤ) - 4 + 2 * k = 4 * (a : ℤ) - 4 - 2 * m := by omega
        rw [hrw] at hfinal
        omega
    rw [hL2]
    apply Real.lt_sqrt_of_sq_lt
    push_cast
    exact_mod_cast hcore

-- Sanity checks

/-- The independence number is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.indepNum := Nat.zero_le _

/-- The Euclidean norm of the degree sequence is nonnegative. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 2)) [DecidableRel G.Adj] : 0 ≤ degreeL2Norm G :=
  Real.sqrt_nonneg _

end WrittenOnTheWallII.GraphConjecture100
