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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 17
*Reference:* [erdosproblems.com/17](https://www.erdosproblems.com/17)
-/

open Filter Asymptotics Real

namespace Erdos17

/-- A prime $p$ is a cluster prime if every even natural number
$n \le p - 3$ can be written as a difference of two primes
$q_1 - q_2$ with $q_1, q_2 \le p$. -/
def IsClusterPrime (p : ℕ) : Prop :=
  p.Prime ∧
    ∀ {n : ℕ}, Even n → n ≤ (p - 3 : ℤ) →
      ∃ q₁ q₂ : ℕ, q₁.Prime ∧ q₂.Prime ∧
        q₁ ≤ p ∧ q₂ ≤ p ∧ n = (q₁ - q₂ : ℤ)

/-- **Erdős Problem 17.** Are there infinitely many cluster primes? -/
@[category research open, AMS 11]
theorem erdos_17 : answer(sorry) ↔ {p : ℕ | IsClusterPrime p}.Infinite := by
  sorry

/-- The counting function of cluster primes $\le n$. -/
noncomputable def clusterPrimeCount (n : ℕ) : ℕ :=
  Nat.card {p : ℕ | p ≤ n ∧ IsClusterPrime p}

/--
In 1999 Blecksmith, Erdős, and Selfridge [BES99] proved the upper bound
$$\pi^{\mathcal{C}}(x) \ll_A x(\log x)^{-A}$$ for every real $A > 0$.

[BES99] Blecksmith, Richard and Erd\H os, Paul and Selfridge, J. L., Cluster primes. Amer. Math. Monthly (1999), 43--48.
-/
@[category research solved, AMS 11]
theorem erdos_17.variants.upper_BES {A : ℝ} (hA : 0 < A) :
  (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A := by
    sorry

/--
In 2003, Elsholtz [El03] refined the upper bound to
$$\pi^{\mathcal{C}}(x) \ll x\,\exp\!\bigl(-c(\log\log x)^2\bigr)$$
for every real $0 < c < 1/8$.

[El03] Elsholtz, Christian, On cluster primes. Acta Arith. (2003), 281--284.
-/
@[category research solved, AMS 11]
theorem erdos_17.variants.upper_Elsholtz :
  ∃ C : ℝ, 0 < C ∧
    ∀ c ∈ Set.Ioo 0 (1 / 8),
      IsBigOWith C atTop (fun x ↦ (clusterPrimeCount x : ℝ))
        (fun x ↦ x * exp (-c * (log (log x)) ^ 2)) := by
  sorry

/-- `IsClusterPrime` is decidable: both the universally quantified even `n` (which is bounded by
`n ≤ p - 3`) and the witnessing primes `q₁, q₂ ≤ p` range over finite sets, so the whole predicate
reduces to a bounded search. -/
instance (p : ℕ) : Decidable (IsClusterPrime p) :=
  haveI : Decidable (p.Prime ∧ ∀ n ∈ (Finset.range (p - 2)).filter (2 ∣ ·),
      ∃ q₁ ∈ Finset.range (p + 1), ∃ q₂ ∈ Finset.range (p + 1),
        q₁.Prime ∧ q₂.Prime ∧ (n : ℤ) = (q₁ : ℤ) - q₂) := inferInstance
  decidable_of_iff
    (p.Prime ∧ ∀ n ∈ (Finset.range (p - 2)).filter (2 ∣ ·),
      ∃ q₁ ∈ Finset.range (p + 1), ∃ q₂ ∈ Finset.range (p + 1),
        q₁.Prime ∧ q₂.Prime ∧ (n : ℤ) = (q₁ : ℤ) - q₂) <|
    (by
      constructor
      · rintro ⟨hp, h⟩
        refine ⟨hp, ?_⟩
        intro n hev hle
        have hn : n ∈ (Finset.range (p - 2)).filter (2 ∣ ·) :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hev.two_dvd⟩
        obtain ⟨q₁, hq₁, q₂, hq₂, hq₁p, hq₂p, heq⟩ := h n hn
        simp only [Finset.mem_range] at hq₁ hq₂
        exact ⟨q₁, q₂, hq₁p, hq₂p, by omega, by omega, heq⟩
      · rintro ⟨hp, h⟩
        refine ⟨hp, ?_⟩
        intro n hn
        obtain ⟨hnr, hdvd⟩ := Finset.mem_filter.mp hn
        simp only [Finset.mem_range] at hnr
        have hle : (n : ℤ) ≤ (p : ℤ) - 3 := by omega
        obtain ⟨q₁, q₂, hq₁, hq₂, hq₁p, hq₂p, heq⟩ := h (even_iff_two_dvd.mpr hdvd) hle
        exact ⟨q₁, Finset.mem_range.mpr (by omega), q₂, Finset.mem_range.mpr (by omega),
          hq₁, hq₂, heq⟩)

/-- $97$ is the smallest prime that is not a cluster prime. -/
@[category test, AMS 11]
theorem isClusterPrime_97_isLeast_non_cluster : IsLeast {p : ℕ | p.Prime ∧ ¬ IsClusterPrime p} 97 := by
  constructor
  · exact ⟨by norm_num, by native_decide⟩
  · have key : ∀ p < 97, p.Prime → IsClusterPrime p := by native_decide
    rintro p ⟨hpp, hnc⟩
    by_contra hlt
    push_neg at hlt
    exact hnc (key p hlt hpp)

end Erdos17
