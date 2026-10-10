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
# Erdős Problem 504

*References:*
- [erdosproblems.com/504](https://www.erdosproblems.com/504)
- [Sz41] Szekeres, G., *On an extremum problem in the plane*.
  Amer. J. Math. 63 (1941), 208-210.
- [ErSz60] Erdős, P. and Szekeres, G., *On some extremum problems in elementary geometry*.
  Ann. Univ. Sci. Budapest. Eötvös Sect. Math. (1960/61), 53-62.
- [Se95] Sendov, Bl., *Minimax of the angles in a plane configuration of points*.
  Acta Math. Hungar. 69 (1995), 27-46.
- [Se95b] Sendov, Bl., *Compulsory configurations of points in the plane*.
  Fundam. Prikl. Mat. 1 (1995), 491-516. [Full text](https://www.mathnet.ru/eng/fpm81).
-/

@[expose] public section

open scoped EuclideanGeometry

namespace Erdos504

/-- The angles guaranteed by every configuration of `N` distinct plane points. -/
def guaranteedAngles (N : ℕ) : Set ℝ :=
  {α | α ∈ Set.Icc 0 Real.pi ∧ ∀ S : Finset ℂ, S.card = N →
    ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S,
      x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ α ≤ EuclideanGeometry.angle x y z}

/-- Blumenthal's minimax angle. Problem statements use `N ≥ 3` so that
three distinct points can exist. -/
noncomputable def minimaxAngle (N : ℕ) : ℝ := sSup (guaranteedAngles N)

@[category API, AMS 51 52]
theorem guaranteedAngles_bddAbove (N : ℕ) : BddAbove (guaranteedAngles N) :=
  ⟨Real.pi, fun _ hα => hα.1.2⟩

@[category API, AMS 51 52]
theorem zero_mem_guaranteedAngles {N : ℕ} (hN : 3 ≤ N) :
    0 ∈ guaranteedAngles N := by
  refine ⟨⟨le_rfl, Real.pi_pos.le⟩, ?_⟩
  intro S hS
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card.mp (by omega : 2 < S.card)
  exact ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz,
    EuclideanGeometry.angle_nonneg x y z⟩

@[category API, AMS 51 52]
theorem minimaxAngle_mem_Icc {N : ℕ} (hN : 3 ≤ N) :
    minimaxAngle N ∈ Set.Icc 0 Real.pi := by
  exact ⟨le_csSup (guaranteedAngles_bddAbove N) (zero_mem_guaranteedAngles hN),
    csSup_le ⟨0, zero_mem_guaranteedAngles hN⟩ (fun _ hα => hα.1.2)⟩

@[category API, AMS 51 52]
theorem guaranteedAngles_mono {M N : ℕ} (hMN : M ≤ N) :
    guaranteedAngles M ⊆ guaranteedAngles N := by
  intro α hα
  refine ⟨hα.1, ?_⟩
  intro S hS
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq (hS.symm ▸ hMN)
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, ha⟩ := hα.2 T hcard
  exact ⟨x, hT hx, y, hT hy, z, hT hz, hxy, hyz, hxz, ha⟩

@[category API, AMS 51 52]
theorem minimaxAngle_mono {M N : ℕ} (hM : 3 ≤ M) (hMN : M ≤ N) :
    minimaxAngle M ≤ minimaxAngle N :=
  csSup_le_csSup (guaranteedAngles_bddAbove N)
    ⟨0, zero_mem_guaranteedAngles hM⟩ (guaranteedAngles_mono hMN)

/-- A universal lower bound and arbitrarily close upper configurations
determine the minimax angle. -/
@[category API, AMS 51 52]
theorem minimaxAngle_eq_of_bounds {N : ℕ} {a : ℝ} (ha : a ∈ Set.Icc 0 Real.pi)
    (hlower : ∀ S : Finset ℂ, S.card = N →
      ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S,
        x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ a ≤ EuclideanGeometry.angle x y z)
    (hupper : ∀ ε : ℝ, 0 < ε → ∃ S : Finset ℂ, S.card = N ∧
      ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → y ≠ z → x ≠ z →
        EuclideanGeometry.angle x y z < a + ε) :
    minimaxAngle N = a := by
  apply le_antisymm
  · apply csSup_le (s := guaranteedAngles N) ⟨a, ha, hlower⟩
    intro α hα
    by_contra h
    have hlt : a < α := lt_of_not_ge h
    obtain ⟨S, hS, hbound⟩ := hupper ((α - a) / 2) (by linarith)
    obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, hangle⟩ := hα.2 S hS
    have := hbound x hx y hy z hz hxy hyz hxz
    linarith
  · exact le_csSup (guaranteedAngles_bddAbove N) ⟨ha, hlower⟩

/-- An upper configuration at cardinality `M` also gives one at every smaller cardinality. -/
@[category API, AMS 51 52]
theorem exists_config_of_le_card {M N : ℕ} {a : ℝ} (hNM : N ≤ M)
    (h : ∃ S : Finset ℂ, S.card = M ∧
      ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → y ≠ z → x ≠ z →
        EuclideanGeometry.angle x y z < a) :
    ∃ T : Finset ℂ, T.card = N ∧
      ∀ x ∈ T, ∀ y ∈ T, ∀ z ∈ T, x ≠ y → y ≠ z → x ≠ z →
        EuclideanGeometry.angle x y z < a := by
  obtain ⟨S, hS, hangle⟩ := h
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq (hS.symm ▸ hNM)
  exact ⟨T, hcard, fun x hx y hy z hz => hangle x (hT hx) y (hT hy) z (hT hz)⟩

/-- A sharp cardinality bound below `a` forces an angle at least `a` above that bound. -/
@[category API, AMS 51 52]
theorem exists_angle_of_card_bound {K : ℕ} {a : ℝ}
    (hbound : ∀ S : Finset ℂ,
      (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → y ≠ z → x ≠ z →
        EuclideanGeometry.angle x y z < a) → S.card ≤ K)
    (S : Finset ℂ) (hS : K < S.card) :
    ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S,
      x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ a ≤ EuclideanGeometry.angle x y z := by
  by_contra h
  have hlt : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → y ≠ z → x ≠ z →
      EuclideanGeometry.angle x y z < a := by
    intro x hx y hy z hz hxy hyz hxz
    exact lt_of_not_ge (fun ha => h ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, ha⟩)
  exact (not_le_of_gt hS) (hbound S hlt)

@[category API, AMS 51 52]
theorem clog_eq_of_pow_bounds {n N : ℕ} (hn : 3 ≤ n)
    (hlo : 2 ^ (n - 1) < N) (hhi : N ≤ 2 ^ n) : Nat.clog 2 N = n := by
  have hu : Nat.clog 2 N ≤ n := (Nat.clog_le_iff_le_pow (by norm_num)).2 hhi
  have hl : n - 1 < Nat.clog 2 N := (Nat.lt_clog_iff_pow_lt (by norm_num)).2 hlo
  omega

@[category API, AMS 51 52]
theorem lower_branch_lt_upper_branch {n : ℕ} (hn : 3 ≤ n) :
    (1 - 2 / (2 * (n : ℝ) - 1)) * Real.pi < (1 - 1 / (n : ℝ)) * Real.pi := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  have hden : 0 < 2 * (n : ℝ) - 1 := by linarith
  have hfrac : 1 / (n : ℝ) < 2 / (2 * (n : ℝ) - 1) :=
    (div_lt_div_iff₀ hpos hden).2 (by linarith)
  exact mul_lt_mul_of_pos_right (sub_lt_sub_left hfrac 1) Real.pi_pos

/--
Let $\alpha_n$ be the supremum of all $0\leq \alpha\leq \pi$ such that in every set
$A\subset \mathbb{R}^2$ of size $n$ there exist three distinct points $x,y,z\in A$ such
that the angle determined by $xyz$ is at least $\alpha$. Determine $\alpha_n$.

Sendov [Se95] provided the definitive answer. For $n\geq 3$ and
$2^{n-1}<N\leq 2^n$, it is $\pi(1-1/n)$ when
$2^{n-1}+2^{n-3}<N$, and $\pi(1-2/(2n-1))$ otherwise.
The initial values are $\alpha_3=\pi/3$ and $\alpha_4=\pi/2$ [ErSz60].
The domain $N\geq 3$ excludes configurations with no triple of distinct points.
-/
@[category research solved, AMS 51 52]
theorem erdos_504 :
    (fun N : {N : ℕ // 3 ≤ N} => minimaxAngle N) =
      answer(fun N : {N : ℕ // 3 ≤ N} =>
        if (N : ℕ) = 3 then Real.pi / 3 else if (N : ℕ) = 4 then Real.pi / 2 else
        let n := Nat.clog 2 N
        if 2 ^ (n - 1) + 2 ^ (n - 3) < (N : ℕ) then (1 - 1 / (n : ℝ)) * Real.pi
        else (1 - 2 / (2 * (n : ℝ) - 1)) * Real.pi) := by
  sorry

/-- Sendov's formula for $2^{n-1}<N\leq 2^n$, where $n\geq 3$. -/
@[category research solved, AMS 51 52]
theorem erdos_504.variants.sendov {n N : ℕ} (hn : 3 ≤ n)
    (hlo : 2 ^ (n - 1) < N) (hhi : N ≤ 2 ^ n) :
    minimaxAngle N =
      if 2 ^ (n - 1) + 2 ^ (n - 3) < N then (1 - 1 / (n : ℝ)) * Real.pi
      else (1 - 2 / (2 * (n : ℝ) - 1)) * Real.pi := by
  sorry

/-- Sendov's capacity bound below $\pi(1-2/(2n-1))$, for $n\geq 3$.
See [Se95b], Lemmas 4.11-4.13. -/
@[category research solved, AMS 51 52]
theorem erdos_504.variants.lower_capacity {n : ℕ} (hn : 3 ≤ n) (S : Finset ℂ)
    (hangle : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → y ≠ z → x ≠ z →
      EuclideanGeometry.angle x y z < (1 - 2 / (2 * (n : ℝ) - 1)) * Real.pi) :
    S.card ≤ 2 ^ (n - 1) := by
  sorry

/-- Sendov's capacity bound below $\pi(1-1/n)$, for $n\geq 3$.
See [Se95b], Lemmas 4.11-4.13. -/
@[category research solved, AMS 51 52]
theorem erdos_504.variants.upper_capacity {n : ℕ} (hn : 3 ≤ n) (S : Finset ℂ)
    (hangle : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → y ≠ z → x ≠ z →
      EuclideanGeometry.angle x y z < (1 - 1 / (n : ℝ)) * Real.pi) :
    S.card ≤ 2 ^ (n - 1) + 2 ^ (n - 3) := by
  sorry

/-- Sendov's three-cluster construction approaches $\pi(1-2/(2n-1))$
with $2^{n-1}+2^{n-3}$ points, for $n\geq 3$.
See [Se95b], Lemmas 4.2-4.3 and 4.14. -/
@[category research solved, AMS 51 52]
theorem erdos_504.variants.three_cluster {n : ℕ} (hn : 3 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℂ, S.card = 2 ^ (n - 1) + 2 ^ (n - 3) ∧
      ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → y ≠ z → x ≠ z →
        EuclideanGeometry.angle x y z <
          (1 - 2 / (2 * (n : ℝ) - 1)) * Real.pi + ε := by
  sorry

/-- Szekeres [Sz41] constructs $2^n$ points whose angles are less than
$\pi(1-1/n)+\varepsilon$, for every $n>0$ and $\varepsilon>0$.
See also [ErSz60], page 53. -/
@[category research solved, AMS 51 52]
theorem erdos_504.variants.szekeres_upper {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℂ, S.card = 2 ^ n ∧
      ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → y ≠ z → x ≠ z →
        EuclideanGeometry.angle x y z < (1 - 1 / (n : ℝ)) * Real.pi + ε := by
  sorry

end Erdos504
