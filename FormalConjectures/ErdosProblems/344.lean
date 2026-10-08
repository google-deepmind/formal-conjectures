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
# Erdős Problem 344

*References:*
- [erdosproblems.com/344](https://www.erdosproblems.com/344)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Er61b] Erdős, P., *On the representation of large integers as sums of distinct summands
  taken from a fixed set*. Acta Arith. (1961/62), 345-354.
- [Fo66] Folkman, J., *On the representation of integers as sums of distinct terms from a
  fixed sequence*. Canadian J. Math. 18 (1966), 643-655.
- [SzVu06] Szemerédi, E. and Vu, V., *Long arithmetic progressions in sumsets: thresholds and
  bounds*. J. Amer. Math. Soc. 19 (2006), 119-169.
- [SzVu06b] Szemerédi, E. and Vu, V., *Finite and infinite arithmetic progressions in sumsets*.
  Ann. of Math. 163 (2006), 1-35.
- [Lean formalisation (plby)](https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos344.md)
-/

@[expose] public section

open Filter

namespace Erdos344

/-- A set is subcomplete if its finite subset sums contain an infinite arithmetic progression
with positive common difference. -/
def IsSubcomplete (A : Set ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ k : ℕ, a + k * d ∈ subsetSums A

/-- The number of elements of $A$ in $\{1,\ldots,N\}$. -/
noncomputable abbrev countUpTo (A : Set ℕ) (N : ℕ) : ℕ :=
  (A ∩ Set.Icc 1 N).ncard

/--
If $A\subseteq \mathbb{N}$ is a set of integers such that
$$\lvert A\cap \{1,\ldots,N\}\rvert\gg N^{1/2}$$
for all $N$ then must $A$ be subcomplete? That is, must
$$P(A) = \left\{\sum_{n\in B}n : B\subseteq A\textrm{ finite }\right\}$$
contain an infinite arithmetic progression?

This is true, and was proved by Szemerédi and Vu [SzVu06].

We use the universal-constant, eventual form in [SzVu06b, Corollary 1.4]: one sufficiently
large positive constant works for every set. Requiring the bound for every $N\geq 1$ would
make its hypothesis impossible at $N=1$ when the constant exceeds $1$.
-/
@[category research solved, AMS 5 11]
theorem erdos_344 : answer(True) ↔
    ∃ C : ℝ, 0 < C ∧ ∀ A : Set ℕ,
      (∀ᶠ N : ℕ in atTop, C * Real.sqrt N ≤ countUpTo A N) → IsSubcomplete A := by
  sorry

/--
The stronger conjecture that this is true under
$$\lvert A\cap \{1,\ldots,N\}\rvert\geq (2N)^{1/2}$$
seems to be still open (this would be best possible as shown by [Er61b]).

The bound is required for all sufficiently large $N$: at $N=1$, it is impossible since
$\lvert A\cap\{1\}\rvert\leq 1<\sqrt{2}$.
-/
@[category research open, AMS 5 11]
theorem erdos_344.variants.sqrt_two : answer(sorry) ↔
    ∀ A : Set ℕ, (∀ᶠ N : ℕ in atTop, Real.sqrt (2 * N) ≤ countUpTo A N) →
      IsSubcomplete A := by
  sorry

/-- Folkman proved this under the stronger assumption that
$$\lvert A\cap \{1,\ldots,N\}\rvert\gg N^{1/2+\epsilon}$$
for some $\epsilon>0$ [Fo66]. -/
@[category research solved, AMS 5 11]
theorem erdos_344.variants.folkman :
    ∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c → ∀ A : Set ℕ,
      (∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤ countUpTo A N) →
      IsSubcomplete A := by
  obtain ⟨C, _, h⟩ := erdos_344.mp trivial
  intro ε hε c hc A hA
  refine h A ?_
  have hpow : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  filter_upwards [hA, hpow.eventually_ge_atTop (C / c)] with N hN hNe
  have hsplit : (N : ℝ) ^ ((1 : ℝ) / 2 + ε) = Real.sqrt N * (N : ℝ) ^ ε := by
    rw [Real.rpow_add' (Nat.cast_nonneg N) (by positivity), Real.sqrt_eq_rpow]
  calc C * Real.sqrt N = c * (C / c) * Real.sqrt N := by field_simp
    _ ≤ c * (N : ℝ) ^ ε * Real.sqrt N := by gcongr
    _ = c * (N : ℝ) ^ ((1 : ℝ) / 2 + ε) := by rw [hsplit]; ring
    _ ≤ countUpTo A N := hN

@[category API, AMS 5 11]
theorem IsSubcomplete.mono {A B : Set ℕ} (hAB : A ⊆ B) (hA : IsSubcomplete A) :
    IsSubcomplete B := by
  obtain ⟨a, d, hd, hk⟩ := hA
  exact ⟨a, d, hd, fun k ↦ subsetSums_mono hAB (hk k)⟩

/-- A finite set is not subcomplete. Its finite subset sums are bounded. -/
@[category textbook, AMS 5 11]
theorem not_isSubcomplete_of_finite {A : Set ℕ} (hA : A.Finite) : ¬ IsSubcomplete A := by
  rintro ⟨a, d, hd, hk⟩
  have hbound : ∀ s ∈ subsetSums A, s ≤ ∑ n ∈ hA.toFinset, n := by
    rintro s ⟨B, hB, rfl⟩
    exact Finset.sum_le_sum_of_subset (fun x hx ↦ by simpa using hB hx)
  set S := ∑ n ∈ hA.toFinset, n
  have h1 := hbound _ (hk (S + 1))
  have h2 : S + 1 ≤ (S + 1) * d := Nat.le_mul_of_pos_right _ hd
  omega

@[category test, AMS 5 11]
theorem univ_density (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C * Real.sqrt N ≤ countUpTo Set.univ N := by
  have hlim : Tendsto (fun N : ℕ ↦ Real.sqrt N) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_ge_atTop C] with N hN
  have hc : countUpTo Set.univ N = N := by simp [countUpTo]
  rw [hc]
  calc C * Real.sqrt N ≤ Real.sqrt N * Real.sqrt N := by gcongr
    _ = N := Real.mul_self_sqrt (Nat.cast_nonneg N)

@[category test, AMS 5 11]
theorem univ_isSubcomplete : IsSubcomplete Set.univ := by
  refine ⟨0, 1, one_pos, fun k ↦ ?_⟩
  exact ⟨{k}, by simp, by simp⟩

@[category test, AMS 5 11]
theorem zero_mem_subsetSums (A : Set ℕ) : 0 ∈ subsetSums A := by
  exact ⟨∅, by simp, by simp⟩

end Erdos344
