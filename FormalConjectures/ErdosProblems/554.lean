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
public import FormalConjectures.ErdosProblems.«183»

/-!
# Erdős Problem 554

*References:*
- [erdosproblems.com/554](https://www.erdosproblems.com/554)
- [Er81c] Erdős, P., *Some new problems and results in graph theory and other branches of
  combinatorial mathematics*. Combinatorics and graph theory (1981), 9–17.
- [ACJMR25] Axenovich, M., Cames van Batenburg, W., Janzer, O., Michel, L., and Rundström, M.,
  *An improved upper bound for the multicolour Ramsey number of odd cycles*.
  [arXiv:2510.17981](https://arxiv.org/abs/2510.17981).
-/

@[expose] public section

open Filter SimpleGraph
open scoped Topology

namespace Erdos554

/-- Every edge colouring of $K_m$ with $k$ colours contains a monochromatic $C_{2n+1}$.
The copy is a subgraph, with no inducedness requirement. -/
def ForcesMonochromaticOddCycle (m k n : ℕ) : Prop :=
  ∀ C : TopEdgeLabeling (Fin m) (Fin k),
    ∃ c : Fin k, cycleGraph (2 * n + 1) ⊑ C.labelGraph c

/-- $R_k(C_{2n+1})$, the smallest complete-graph order forcing the odd cycle. -/
noncomputable def oddCycleRamsey (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ForcesMonochromaticOddCycle m k n}

@[category API, AMS 5]
theorem oddCycleRamsey_le {m k n : ℕ} (h : ForcesMonochromaticOddCycle m k n) :
    oddCycleRamsey k n ≤ m := Nat.sInf_le h

@[category API, AMS 5]
theorem oddCycleRamsey_spec {k n : ℕ}
    (h : {m : ℕ | ForcesMonochromaticOddCycle m k n}.Nonempty) :
    ForcesMonochromaticOddCycle (oddCycleRamsey k n) k n := Nat.sInf_mem h

/-- With one colour, a complete graph contains $C_{2n+1}$ exactly when it has enough vertices. -/
@[category API, AMS 5]
theorem forcesMonochromaticOddCycle_one_iff (m n : ℕ) :
    ForcesMonochromaticOddCycle m 1 n ↔ 2 * n + 1 ≤ m := by
  have hlabel (C : TopEdgeLabeling (Fin m) (Fin 1)) (c : Fin 1) :
      C.labelGraph c = completeGraph (Fin m) := by
    ext x y
    simp only [TopEdgeLabeling.labelGraph_adj, top_adj]
    constructor
    · rintro ⟨h, _⟩
      exact h
    · intro h
      exact ⟨h, Subsingleton.elim _ _⟩
  constructor
  · intro h
    let C : TopEdgeLabeling (Fin m) (Fin 1) := fun _ => 0
    obtain ⟨c, hc⟩ := h C
    rw [hlabel C c, isContained_top_iff] at hc
    obtain ⟨e⟩ := hc
    simpa using Fintype.card_le_of_injective e e.injective
  · intro h C
    refine ⟨0, ?_⟩
    rw [hlabel, isContained_top_iff]
    exact ⟨Fin.castLEEmb h⟩

/-- With one colour, the odd-cycle Ramsey number is its number of vertices. -/
@[simp, category API, AMS 5]
theorem oddCycleRamsey_one (n : ℕ) : oddCycleRamsey 1 n = 2 * n + 1 := by
  apply le_antisymm
  · exact oddCycleRamsey_le ((forcesMonochromaticOddCycle_one_iff _ _).mpr le_rfl)
  · apply le_csInf
    · exact ⟨2 * n + 1, (forcesMonochromaticOddCycle_one_iff _ _).mpr le_rfl⟩
    · intro m hm
      exact (forcesMonochromaticOddCycle_one_iff _ _).mp hm

/-- $C_3$ is a triangle, so the odd-cycle definition agrees with the triangle Ramsey number. -/
@[simp, category API, AMS 5]
theorem oddCycleRamsey_triangle (k : ℕ) :
    oddCycleRamsey k 1 = Erdos183.multicolourTriangleRamsey k := by
  simp only [oddCycleRamsey, ForcesMonochromaticOddCycle, Erdos183.multicolourTriangleRamsey,
    Erdos183.ForcesMonochromaticTriangle, TopEdgeLabeling.CliqueFree, not_forall,
    not_cliqueFree_iff_top_isContained, Nat.reduceMul, Nat.reduceAdd, cycleGraph_three_eq_top]

/-- Separated exponential bases in bounds for the two Ramsey numbers force their ratio to zero. -/
@[category API, AMS 5]
theorem ratio_tendsto_zero_of_geometric_bounds (n : ℕ) (u v : ℕ → ℝ)
    {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (h : ∀ᶠ k in atTop, 0 ≤ u k ∧ 0 < v k ∧
      (oddCycleRamsey k n : ℝ) ≤ u k ^ k ∧
      v k ^ k ≤ (Erdos183.multicolourTriangleRamsey k : ℝ) ∧ u k / v k ≤ q) :
    Tendsto (fun k : ℕ => (oddCycleRamsey k n : ℝ) /
      (Erdos183.multicolourTriangleRamsey k : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun k =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁)
  filter_upwards [h] with k hk
  obtain ⟨hu, hv, hR, hT, hq⟩ := hk
  calc
    (oddCycleRamsey k n : ℝ) / (Erdos183.multicolourTriangleRamsey k : ℝ) ≤
        u k ^ k / v k ^ k := div_le_div₀ (pow_nonneg hu _) hR (pow_pos hv _) hT
    _ = (u k / v k) ^ k := (div_pow _ _ _).symm
    _ ≤ q ^ k := pow_le_pow_left₀ (div_nonneg hu hv.le) hq k

/-- Bounds by $u(k)^k$ above and $v(k)^k$ below suffice when $u(k)/v(k)\to0$. -/
@[category API, AMS 5]
theorem ratio_tendsto_zero_of_base_ratio (n : ℕ) (u v : ℕ → ℝ)
    (h : ∀ᶠ k in atTop, 0 ≤ u k ∧ 0 < v k ∧
      (oddCycleRamsey k n : ℝ) ≤ u k ^ k ∧
      v k ^ k ≤ (Erdos183.multicolourTriangleRamsey k : ℝ))
    (huv : Tendsto (fun k => u k / v k) atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => (oddCycleRamsey k n : ℝ) /
      (Erdos183.multicolourTriangleRamsey k : ℝ)) atTop (𝓝 0) := by
  apply ratio_tendsto_zero_of_geometric_bounds n u v
    (q := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hsmall : ∀ᶠ k in atTop, u k / v k < (1 / 2 : ℝ) :=
    huv.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [h, hsmall] with k hk hks
  exact ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2, hks.le⟩

/-- For $n\geq4$, the displayed cycle upper bound and triangle lower bound imply the ratio
limit. The positive exponent gap is $1/3-1/n$; both combinatorial bounds are hypotheses. -/
@[category API, AMS 5, formal_proof using lean4 at
  "https://github.com/AItoBit/erdos554-lean/blob/911121c29b7d4ddd90ec3856a821a9790ee3c7f8/Verified554.lean#L42"]
theorem ratio_tendsto_zero_of_power_log_bounds (n : ℕ) (hn : 4 ≤ n) (c : ℝ) (hc : 0 < c)
    (h : ∀ᶠ k in atTop,
      (oddCycleRamsey k n : ℝ) ≤ (4 * (n : ℝ)) ^ k * (k : ℝ) ^ ((k : ℝ) / n) ∧
      (c * (k : ℝ) ^ (1 / 3 : ℝ) / Real.log k) ^ k ≤
        (Erdos183.multicolourTriangleRamsey k : ℝ)) :
    Tendsto (fun k : ℕ => (oddCycleRamsey k n : ℝ) /
      (Erdos183.multicolourTriangleRamsey k : ℝ)) atTop (𝓝 0) := by
  sorry

/-- Let $R_k(G)$ denote the minimal $m$ such that if the edges of $K_m$ are $k$-coloured then
there is a monochromatic copy of $G$. Show that
$$\lim_{k\to\infty}\frac{R_k(C_{2n+1})}{R_k(K_3)}=0$$
for any $n\geq2$.

A problem of Erdős and Graham. The problem is open even for $n=2$. -/
@[category research open, AMS 5]
theorem erdos_554 : ∀ n : ℕ, 2 ≤ n →
    Tendsto (fun k : ℕ => (oddCycleRamsey k n : ℝ) /
      (Erdos183.multicolourTriangleRamsey k : ℝ)) atTop (𝓝 0) := by
  sorry

/-- Axenovich, Cames van Batenburg, Janzer, Michel, and Rundström [ACJMR25, Theorem 1.1]
have improved the upper bound to
$$R_k(C_{2n+1})\leq(4n-2)^k k^{k/n}+1.$$ -/
@[category research solved, AMS 5]
theorem erdos_554.variants.acjmr : ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k →
    (oddCycleRamsey k n : ℝ) ≤ (4 * (n : ℝ) - 2) ^ k * (k : ℝ) ^ ((k : ℝ) / n) + 1 := by
  sorry

end Erdos554
