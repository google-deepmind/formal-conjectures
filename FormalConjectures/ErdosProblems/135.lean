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
# Erdős Problem 135

*References:*
- [erdosproblems.com/135](https://www.erdosproblems.com/135)
- [Er97b] Erdős, Paul, *Some old and new problems in various branches of combinatorics*.
  Discrete Math. (1997), 227-231.
- [Ta24c] Tao, Terence, *Planar point sets with forbidden 4-point patterns and few distinct
  distances*. [arXiv:2409.01343](https://arxiv.org/abs/2409.01343) (2024).
-/

@[expose] public section

open Filter EuclideanGeometry

namespace Erdos135

/-- The `(p, q)` condition: every `p`-point subset of `A` determines at least `q` distinct
distances. -/
def PointsDetermine (p q : ℕ) (A : Finset ℝ²) : Prop :=
  ∀ S ⊆ A, S.card = p → q ≤ distinctDistances S

/-- The Erdős–Gyárfás condition: any four points of `A` determine at least five distinct
distances. -/
abbrev FourFive (A : Finset ℝ²) : Prop := PointsDetermine 4 5 A

/--
Tao's construction [Ta24c]: for every sufficiently large $n$ there is a set of $n$ points in
$\mathbb{R}^2$ in which any four points determine at least five distinct distances, yet which
determines only $O(n^2 / \sqrt{\log n})$ distinct distances.
-/
@[category research solved, AMS 5 52,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos135.lean"]
theorem erdos_135.variants.tao :
    ∃ K N₀ : ℝ, ∀ n : ℕ, N₀ ≤ n → ∃ A : Finset ℝ², A.card = n ∧ FourFive A ∧
      (distinctDistances A : ℝ) ≤ K * (n : ℝ) ^ 2 / Real.sqrt (Real.log n) := by
  sorry

/--
Let $A \subset \mathbb{R}^2$ be a set of $n$ points such that any subset of size $4$ determines
at least $5$ distinct distances. Must $A$ determine $\gg n^2$ many distances?

A question of Erdős and Gyárfás [Er97b]. The answer is no: Tao [Ta24c] constructed such sets
determining only $\ll n^2 / \sqrt{\log n}$ distinct distances (see `erdos_135.variants.tao`).

The hypothesis $2 \le n$ only excludes the degenerate empty and one-point sets, which
determine no distances at all.
-/
@[category research solved, AMS 5 52]
theorem erdos_135 : answer(False) ↔
    ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℝ², 2 ≤ A.card → FourFive A →
      C * (A.card : ℝ) ^ 2 ≤ distinctDistances A := by
  show False ↔ _
  refine ⟨False.elim, ?_⟩
  rintro ⟨C, hC, hQ⟩
  obtain ⟨K, N₀, hT⟩ := erdos_135.variants.tao
  -- choose `n` so large that `K / √(log n) < C`
  have hlim : Tendsto (fun n : ℕ => K / Real.sqrt (Real.log n)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      ((Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).comp
        tendsto_natCast_atTop_atTop)
  obtain ⟨n, hKC, h2, hN⟩ := ((hlim.eventually (gt_mem_nhds hC)).and
    ((eventually_ge_atTop 2).and
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop N₀ :
        ∀ᶠ n : ℕ in atTop, N₀ ≤ (n : ℝ)))).exists
  obtain ⟨A, hcard, hA, hle⟩ := hT n hN
  have h1 := hQ A (hcard ▸ h2) hA
  rw [hcard] at h1
  have hn0 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hrw : K * (n : ℝ) ^ 2 / Real.sqrt (Real.log n) =
      K / Real.sqrt (Real.log n) * (n : ℝ) ^ 2 := by
    ring
  have := mul_lt_mul_of_pos_right hKC hn0
  linarith

/-- The `(p, q)` condition passes to subsets. -/
@[category API, AMS 52]
theorem PointsDetermine.mono {p q : ℕ} {A B : Finset ℝ²} (h : PointsDetermine p q A)
    (hBA : B ⊆ A) : PointsDetermine p q B :=
  fun S hS hc => h S (hS.trans hBA) hc

end Erdos135
