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
# Erdős Problem 712

*References:*
- [erdosproblems.com/712](https://www.erdosproblems.com/712)
- [Er81] Erdős, P., On the combinatorial problems which I would most like to see solved.
  Combinatorica (1981), 25-42.
-/

@[expose] public section

namespace Erdos712

open Filter Asymptotics
open scoped Topology

def erdos_712.answer : ℕ → ℕ → ℝ := sorry

/--
Determine, for any $k>r>2$, the limiting value as $n\to\infty$ of
$$\frac{\mathrm{ex}_r(n,K_k^r)}{\binom{n}{r}},$$
where $\mathrm{ex}_r(n,K_k^r)$ is the largest number of $r$-edges which can placed on $n$ vertices
so that there exists no set of $k$ vertices which is covered by all $\binom{k}{r}$ possible
$r$-edges.
-/
@[category research open, question value, AMS 5]
theorem erdos_712 :
    ∀ k r : ℕ, 2 < r → r < k →
      Tendsto (fun n ↦ (Hypergraph.cliqueExtremalNumber n r k : ℝ) / n.choose r)
        atTop (𝓝 (erdos_712.answer k r)) := by
  sorry


/-- The normalized extremal numbers have a limit in $[0,1]$. This existence result does
not determine the value asked for in Erdős Problem 712. -/
@[category textbook, AMS 5]
theorem erdos_712.variants.limit_exists (r k : ℕ) :
    ∃ π ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ ↦ (Hypergraph.cliqueExtremalNumber n r k : ℝ) / n.choose r)
        atTop (𝓝 π) := by
  sorry

open SimpleGraph Finset in
/-- For graphs (`r = 2`), the clique extremal number is the number of edges of the Turán graph:
this is Turán's theorem, transported from `SimpleGraph (Fin n)` to families of `2`-sets. -/
lemma cliqueExtremalNumber_two_eq (n r : ℕ) (hr : 0 < r) :
    Hypergraph.cliqueExtremalNumber n 2 (r + 1) = #(turanGraph n r).edgeFinset := by
  classical
  have hinj : Function.Injective (Sym2.toFinset : Sym2 (Fin n) → Finset (Fin n)) := by
    intro z z' h
    refine Sym2.ext fun x ↦ ?_
    rw [← Sym2.mem_toFinset, h, Sym2.mem_toFinset]
  unfold Hypergraph.cliqueExtremalNumber Hypergraph.extremalNumber
  apply le_antisymm
  · refine Finset.sup_le fun F hF ↦ ?_
    simp only [Finset.mem_filter, mem_powerset] at hF
    obtain ⟨hsub, hfree⟩ := hF
    let G : SimpleGraph (Fin n) := SimpleGraph.fromRel fun a b ↦ ({a, b} : Finset (Fin n)) ∈ F
    have hadj : ∀ a b, G.Adj a b ↔ a ≠ b ∧ ({a, b} : Finset (Fin n)) ∈ F := by
      intro a b
      simp [G, SimpleGraph.fromRel_adj, Finset.pair_comm]
    have hcf : G.CliqueFree (r + 1) := by
      intro S hS
      refine hfree ⟨S, hS.card_eq, fun e he ↦ ?_⟩
      rw [mem_powersetCard] at he
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he.2
      exact ((hadj a b).mp (hS.isClique (he.1 (by simp)) (he.1 (by simp)) hab)).2
    have h1 : F ⊆ G.edgeFinset.image Sym2.toFinset := by
      intro e he
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (mem_powersetCard.mp (hsub he)).2
      refine mem_image.mpr ⟨s(a, b), ?_, Sym2.toFinset_mk_eq⟩
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hadj]
      exact ⟨hab, he⟩
    have h2 := hcf.card_edgeFinset_le
    simp only [Fintype.card_fin] at h2
    rw [card_edgeFinset_turanGraph]
    exact (card_le_card h1).trans (card_image_le.trans h2)
  · rw [← card_image_of_injective (turanGraph n r).edgeFinset hinj]
    refine Finset.le_sup (f := Finset.card) ?_
    simp only [Finset.mem_filter, mem_powerset]
    refine ⟨fun e he ↦ ?_, ?_⟩
    · obtain ⟨z, hz, rfl⟩ := mem_image.mp he
      rw [mem_powersetCard]
      refine ⟨subset_univ _, Sym2.card_toFinset_of_not_isDiag z ?_⟩
      exact (turanGraph n r).not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp hz)
    · rintro ⟨S, hScard, hS⟩
      refine turanGraph_cliqueFree (n := n) hr S ⟨?_, hScard⟩
      intro a ha b hb hab
      have hmem : ({a, b} : Finset (Fin n)) ∈ S.powersetCard 2 := by
        rw [mem_powersetCard]
        exact ⟨Finset.insert_subset_iff.mpr ⟨mem_coe.mp ha, Finset.singleton_subset_iff.mpr
          (mem_coe.mp hb)⟩, Finset.card_pair hab⟩
      obtain ⟨z, hz, hzab⟩ := mem_image.mp (hS hmem)
      rw [← Sym2.toFinset_mk_eq] at hzab
      rw [hinj hzab] at hz
      exact SimpleGraph.mem_edgeFinset.mp hz

open SimpleGraph Finset in
/-- The edge density of the Turán graph, normalised by $n^2$, tends to $(r-1)/(2r)$. -/
lemma tendsto_card_edgeFinset_turanGraph_div_sq (r : ℕ) (hr : 0 < r) :
    Tendsto (fun n : ℕ ↦ (#(turanGraph n r).edgeFinset : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (((r : ℝ) - 1) / (2 * r))) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  set D : ℝ := (r : ℝ) * (r - 1) / 2 + 1 with hD
  have hlow : Tendsto (fun n : ℕ ↦ ((r : ℝ) - 1) / (2 * r) - D / (n : ℝ) ^ 2)
      atTop (𝓝 (((r : ℝ) - 1) / (2 * r))) := by
    have h0 : Tendsto (fun n : ℕ ↦ D / (n : ℝ) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
    simpa using tendsto_const_nhds.sub h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    rw [le_div_iff₀ hn', sub_mul, div_mul_cancel₀ _ hn'.ne']
    rw [card_edgeFinset_turanGraph]
    set m := n % r with hm
    have hmr : m < r := Nat.mod_lt _ hr
    have hmn : m ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (Nat.mod_le _ _) 2
    set q := (n ^ 2 - m ^ 2) * (r - 1) / (2 * r) with hq
    have h1 : (n ^ 2 - m ^ 2) * (r - 1) < q * (2 * r) + 2 * r :=
      Nat.lt_div_mul_add (by omega)
    have h2 : (((n ^ 2 - m ^ 2) * (r - 1) : ℕ) : ℝ) < ((q * (2 * r) + 2 * r : ℕ) : ℝ) := by
      exact_mod_cast h1
    rw [Nat.cast_mul, Nat.cast_sub hmn, Nat.cast_sub hr] at h2
    push_cast at h2 ⊢
    have hm' : (m : ℝ) ^ 2 ≤ (r : ℝ) ^ 2 := by
      have : (m : ℝ) ≤ r := by exact_mod_cast hmr.le
      nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have h3 : ((r : ℝ) ^ 2 - (m : ℝ) ^ 2) * ((r : ℝ) - 1) ≥ 0 :=
      mul_nonneg (by linarith) (by linarith)
    have h4 : (0 : ℝ) ≤ ((n % r).choose 2 : ℝ) := Nat.cast_nonneg _
    have h5 : ((r : ℝ) - 1) / (2 * r) * (n : ℝ) ^ 2 - D ≤ q := by
      rw [hD, div_mul_eq_mul_div, ← sub_nonneg]
      have : (q : ℝ) - (((r : ℝ) - 1) * (n : ℝ) ^ 2 / (2 * r) - ((r : ℝ) * (r - 1) / 2 + 1))
          = (2 * r * q + 2 * r - ((n : ℝ) ^ 2 - r ^ 2) * (r - 1)) / (2 * r) := by
        field_simp
        ring
      rw [this]
      apply div_nonneg _ (by positivity)
      nlinarith
    linarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ hn', div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have h := mul_card_edgeFinset_turanGraph_le (n := n) (r := r)
    have h' : ((2 * r * #(turanGraph n r).edgeFinset : ℕ) : ℝ) ≤ (((r - 1) * n ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [Nat.cast_mul (r - 1), Nat.cast_sub hr] at h'
    push_cast at h'
    linarith

/-- Turán's theorem gives the graph case:
$\mathrm{ex}_2(n,K_k)/\binom{n}{2}\to 1-1/(k-1)$. -/
@[category research solved, AMS 5]
theorem erdos_712.variants.graph_case (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ ↦ (Hypergraph.cliqueExtremalNumber n 2 k : ℝ) / n.choose 2)
      atTop (𝓝 (1 - 1 / ((k : ℝ) - 1))) := by
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  have hr : 0 < r := by omega
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  simp_rw [cliqueExtremalNumber_two_eq _ r hr]
  have hchoose : Tendsto (fun n : ℕ ↦ ((n.choose 2 : ℕ) : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (1 / 2)) := by
    have h0 : Tendsto (fun n : ℕ ↦ (1 - 1 / (n : ℝ)) / 2) atTop (𝓝 ((1 - 0) / 2)) :=
      (tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat).div_const 2
    rw [sub_zero] at h0
    refine h0.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_choose_two]
    field_simp
  have h := (tendsto_card_edgeFinset_turanGraph_div_sq r hr).div hchoose (by norm_num)
  have hval : ((r : ℝ) - 1) / (2 * r) / (1 / 2) = 1 - 1 / (((r + 1 : ℕ) : ℝ) - 1) := by
    have h1 : ((r + 1 : ℕ) : ℝ) - 1 = r := by push_cast; ring
    rw [h1]
    field_simp
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ^ 2 ≠ 0 := by positivity
  exact div_div_div_cancel_right₀ hn' _ _

/-- With denominator $n^2$, Turán's graph limit is
$\frac12(1-1/(k-1))$. The factor $\frac12$ comes from the normalization. -/
@[category research solved, AMS 5]
theorem erdos_712.variants.graph_case_div_sq (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ ↦ (Hypergraph.cliqueExtremalNumber n 2 k : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 ((1 / 2) * (1 - 1 / ((k : ℝ) - 1)))) := by
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  have hr : 0 < r := by omega
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  simp_rw [cliqueExtremalNumber_two_eq _ r hr]
  have hval : (1 / 2 : ℝ) * (1 - 1 / (((r + 1 : ℕ) : ℝ) - 1)) = ((r : ℝ) - 1) / (2 * r) := by
    have h1 : ((r + 1 : ℕ) : ℝ) - 1 = r := by push_cast; ring
    rw [h1]
    field_simp
  rw [hval]
  exact tendsto_card_edgeFinset_turanGraph_div_sq r hr

end Erdos712
