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
# Erdős Problem 150

*References:*
- [erdosproblems.com/150](https://www.erdosproblems.com/150)
- [Br24] Bradač, D., *On a question of Erdős and Nešetřil about minimal cuts in a graph*.
  [arXiv:2409.02974](https://arxiv.org/abs/2409.02974) (2024).
- [Er88] Erdős, P., *Problems and results in combinatorial analysis and graph theory*.
  [Discrete Math. (1988), 81-92](https://webmail.math-inst.hu/~p_erdos/1988-27.pdf).
- [FKTV08] Fomin, Fedor V. and Kratsch, Dieter and Todinca, Ioan and Villanger, Yngve, *Exact
  algorithms for treewidth and minimum fill-in*. SIAM J. Comput. (2008), 1058-1079.
- [FoVi12] Fomin, Fedor V. and Villanger, Yngve, *Treewidth computation and extremal
  combinatorics*. Combinatorica (2012), 289-308.
- [GaMa18] Gaspers, Serge and Mackenzie, Simon, *On the number of minimal separators in graphs*.
  [J. Graph Theory (2018), 653-659](https://doi.org/10.1002/jgt.22179).
-/

@[expose] public section

open Filter

open scoped Topology

namespace Erdos150

/-- A *minimal cut* of a graph `G` is a minimal set `T` of vertices whose removal disconnects
`G`, that is, `G - T` fails to be preconnected while `G - S` is preconnected for every `S ⊂ T`. -/
def IsMinimalCut {V : Type*} (G : SimpleGraph V) (T : Set V) : Prop :=
  ¬ (G.induce Tᶜ).Preconnected ∧ ∀ S ⊂ T, (G.induce Sᶜ).Preconnected

/-- The maximum number $c(n)$ of minimal cuts a graph on $n$ vertices can have. -/
noncomputable def maxMinimalCuts (n : ℕ) : ℕ :=
  sSup {k | ∃ G : SimpleGraph (Fin n), {T : Set (Fin n) | IsMinimalCut G T}.ncard = k}

set_option linter.style.formal_proof_palomar false in
/--
A minimal cut of a graph is a minimal set of vertices whose removal disconnects the graph. Let
$c(n)$ be the maximum number of minimal cuts a graph on $n$ vertices can have.

Does $c(n)^{1/n}\to \alpha$ for some $\alpha <2$?

It is unclear in [Er88] whether Erdős knew that the limit existed, which follows from a simple
argument first given in the literature (to the best of my knowledge) by Bradač [Br24].

That $\alpha<2$ was proved by Fomin, Kratsch, Todinca, and Villanger [FKTV08], who proved
$\alpha \leq 1.7087$. This was independently studied by Bradač [Br24] (unaware of this earlier
work), who proved that $\alpha \leq 2^{H(1/3)}\approx 1.8899$, where $H(\cdot)$ is the binary
entropy function.

This was formalized in Lean by Monticone using Aristotle.
-/
@[category research solved, question, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos150.lean"]
theorem erdos_150 :
    ∃ α : ℝ, α < 2 ∧
      Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α) := by
  sorry

/-- The five pairs of nonadjacent vertices of the five-cycle are minimal cuts. -/
@[category API, AMS 5]
theorem five_le_maxMinimalCuts : 5 ≤ maxMinimalCuts 5 := by
  let G := SimpleGraph.cycleGraph 5
  let F : Finset (Finset (Fin 5)) := {{0, 2}, {0, 3}, {1, 3}, {1, 4}, {2, 4}}
  have hcuts : ∀ T ∈ F, ¬ (G.induce (↑(Tᶜ) : Set (Fin 5))).Preconnected ∧
      ∀ S ∈ T.ssubsets, (G.induce (↑(Sᶜ) : Set (Fin 5))).Preconnected := by decide +kernel
  have hsub : (fun T : Finset (Fin 5) ↦ (T : Set (Fin 5))) '' (F : Set _) ⊆
      {T | IsMinimalCut G T} := by
    rintro _ ⟨T, hT, rfl⟩
    obtain ⟨hdisc, hmin⟩ := hcuts T hT
    refine ⟨?_, fun S hS ↦ ?_⟩
    · rw [← Finset.coe_compl]
      exact hdisc
    · classical
      obtain ⟨S', rfl⟩ : ∃ S' : Finset (Fin 5), (S' : Set _) = S := ⟨S.toFinset, by simp⟩
      rw [← Finset.coe_compl]
      exact hmin S' (Finset.mem_ssubsets.mpr (by exact_mod_cast hS))
  have hF : F.card = 5 := by decide
  calc
    5 = ((fun T : Finset (Fin 5) ↦ (T : Set (Fin 5))) '' (F : Set _)).ncard := by
      rw [Set.ncard_image_of_injective _ Finset.coe_injective, Set.ncard_coe_finset, hF]
    _ ≤ {T | IsMinimalCut G T}.ncard := Set.ncard_le_ncard hsub
    _ ≤ maxMinimalCuts 5 := by
      unfold maxMinimalCuts
      refine le_csSup ?_ ⟨G, rfl⟩
      refine ⟨Nat.card (Set (Fin 5)), ?_⟩
      rintro _ ⟨H, rfl⟩
      exact Set.ncard_le_card _

/-- Erdős and Nešetřil asked whether $c(3m+2)=3^m$. The five-cycle gives $c(5) \ge 5 > 3$,
so equality fails at $m=1$. -/
@[category research solved, question, AMS 5]
theorem erdos_150.variants.erdos_nesetril :
    ¬ ∀ m : ℕ, maxMinimalCuts (3 * m + 2) = 3 ^ m := by
  intro h
  have heq : maxMinimalCuts 5 = 3 := h 1
  have hcut := five_le_maxMinimalCuts
  omega

/--
Seymour observed that $c(3m+2)\geq 3^m$, as seen by the graph of $m$ independent paths of length
$4$ joining two vertices.
-/
@[category research solved, AMS 5]
theorem erdos_150.variants.seymour (m : ℕ) : 3 ^ m ≤ maxMinimalCuts (3 * m + 2) := by
  sorry

/--
The current best-known bounds on $\alpha$ are
$$1.4457\leq \alpha \leq \frac{1+\sqrt{5}}{2}\approx 1.618.$$
The lower bound is due to Gaspers and Mackenzie [GaMa18].
-/
@[category research solved, AMS 5]
theorem erdos_150.variants.lower_bound (α : ℝ)
    (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) :
    1.4457 ≤ α := by
  sorry

/-- Seymour's lower bound is strict for every sufficiently large $m$. Bradač [Br24, p. 1]
relates the growth rate for minimal cuts to that for minimal separators. The lower bound
$1.4457$ of Gaspers and Mackenzie [GaMa18] exceeds $\sqrt[3]{3}$. -/
@[category research solved, AMS 5]
theorem erdos_150.variants.eventually_gt_seymour :
    ∀ᶠ m : ℕ in atTop, 3 ^ m < maxMinimalCuts (3 * m + 2) := by
  obtain ⟨α, -, hα⟩ := erdos_150
  have hbase : (1.445 : ℝ) < α := lt_of_lt_of_le (by norm_num) (erdos_150.variants.lower_bound α hα)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hα.eventually_const_lt hbase)
  filter_upwards [eventually_ge_atTop N] with m hm
  have hn : 3 * m + 2 ≠ 0 := by omega
  have hpow := pow_lt_pow_left₀ (hN (3 * m + 2) (by omega)) (by norm_num) hn
  rw [one_div, Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) hn] at hpow
  have hle : (3 : ℝ) ^ m ≤ 1.445 ^ (3 * m + 2) := calc
    _ ≤ ((1.445 : ℝ) ^ 3) ^ m := by
      gcongr
      norm_num
    _ ≤ _ := by
      rw [pow_add, pow_mul]
      exact le_mul_of_one_le_right (by positivity) (by norm_num)
  exact_mod_cast hle.trans_lt hpow

/--
The current best-known bounds on $\alpha$ are
$$1.4457\leq \alpha \leq \frac{1+\sqrt{5}}{2}\approx 1.618.$$
The upper bound is due to Fomin and Villanger [FoVi12] (with a simpler proof in [GaMa18]).
-/
@[category research solved, AMS 5]
theorem erdos_150.variants.upper_bound (α : ℝ)
    (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) :
    α ≤ (1 + Real.sqrt 5) / 2 := by
  sorry

end Erdos150
