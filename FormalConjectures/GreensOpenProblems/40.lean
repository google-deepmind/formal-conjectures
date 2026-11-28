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
# Ben Green's Open Problem 40

*References:*
- [Gr24] [Ben Green's Open Problem 40](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.40)
- [Da90] Davydov, Alexander Abramovich. "Construction of linear covering codes."
  Problemy Peredachi Informatsii 26.4 (1990): 38-55.
- [CHL97] Cohen, G., Honkala, I., Litsyn, S., & Lobstein, A. (1997). Covering codes (Vol. 54). Elsevier.
- [St94] R. Struik, Covering codes, PhD Thesis, Eindhoven University of Technology, the Netherlands, 106 pp, 1994.

-/

@[expose] public section

open Filter Topology Fintype
open scoped ENNReal Pointwise

namespace Green40


/-- The Hamming ball of radius $r$ in $\mathbb{F}_2^n$. -/
def hammingBall (n r : ℕ) : Set (𝔽₂ n) :=
  {x | hammingNorm x ≤ r}

/-- $V$ is a covering subspace of $\mathbb{F}_2^n$ by $H(r)$ if $V + H(r) = \mathbb{F}_2^n$. -/
def IsCoveringSubspace (n r : ℕ) (V : Submodule (ZMod 2) (𝔽₂ n)) : Prop :=
  (V : Set (𝔽₂ n)) + hammingBall n r = Set.univ

/-- The minimal covering density over all covering subspaces for a given n and r.
    We compute in `ℝ≥0∞` (ENNReal) to gracefully handle any potential divergence. -/
noncomputable def minDensity (n r : ℕ) : ℝ≥0∞ :=
  ⨅ (V : Submodule (ZMod 2) (𝔽₂ n)) (_ : IsCoveringSubspace n r V),
    (Nat.card V : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞)

/--
Let $f(r)$ be the smallest constant such that there exists an infinite sequence of $n$'s together
with subspaces $V_n \leq \mathbb{F}_2^n$ with $V_n + H(r) = \mathbb{F}_2^n$ and
$|V_n| = \left(f(r) + o(1)\right) \frac{2^n}{|H(r)|}$.
-/
noncomputable def f (r : ℕ) : ℝ≥0∞ :=
  liminf (fun n ↦ minDensity n r) atTop

/-- Does $f(r) \to \infty$? [Gr24]-/
@[category research open, question, AMS 5 94]
theorem green_40 : Tendsto f atTop (𝓝 ⊤) := by
  sorry

/-! Hamming parity-check construction, adapted from anatoliiohorodnyk/lean-fc-proofs
     (Apache-2.0, commit 5da9642575b26c2c816a49bcb56b33fed5456619). -/
lemma g40_norm_single (n : ℕ) (j : Fin n) : hammingNorm (Pi.single j (1 : ZMod 2) : 𝔽₂ n) = 1 := by
  unfold hammingNorm
  rw [Finset.card_eq_one]
  refine ⟨j, ?_⟩
  ext i
  by_cases h : i = j
  · subst h; simp
  · simp [h, Pi.single_apply]

lemma g40_zmod2 (a : ZMod 2) (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

lemma g40_card_ball (n : ℕ) : Nat.card (hammingBall n 1) = n + 1 := by
  let g : Option (Fin n) → 𝔽₂ n := fun o => o.elim 0 (fun i => Pi.single i 1)
  have hg : Function.Injective g := by
    intro o o' h
    cases o with
    | none =>
      cases o' with
      | none => rfl
      | some j =>
        have := congrFun h j
        simp [g] at this
    | some i =>
      cases o' with
      | none =>
        have := congrFun h i
        simp [g] at this
      | some j =>
        by_contra hij
        have hij' : i ≠ j := fun e => hij (by rw [e])
        have := congrFun h i
        simp [g, Pi.single_apply, hij'] at this
  have hrange : Set.range g = hammingBall n 1 := by
    ext x
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | none => simp [g, hammingBall]
      | some i => simp only [g, hammingBall, Set.mem_setOf_eq, Option.elim]; rw [g40_norm_single]
    · intro hx
      simp only [hammingBall, Set.mem_setOf_eq] at hx
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with h0 | h1
      · exact ⟨none, by simpa [g, eq_comm] using hammingNorm_eq_zero.mp h0⟩
      · unfold hammingNorm at h1
        obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h1
        refine ⟨some j, ?_⟩
        funext i
        simp only [g, Option.elim]
        by_cases hij : i = j
        · subst hij
          have : i ∈ ({i} : Finset (Fin n)) := Finset.mem_singleton_self i
          rw [← hj] at this
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          simp [g40_zmod2 _ this]
        · have : i ∉ ({j} : Finset (Fin n)) := by simpa using hij
          rw [← hj] at this
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at this
          simp [Pi.single_apply, hij, this]
  rw [← hrange, Nat.card_congr (Equiv.ofInjective g hg).symm]
  simp

lemma g40_card_space (n : ℕ) : Nat.card (𝔽₂ n) = 2 ^ n := by
  simp [Nat.card_fun]

lemma g40_lower (n r : ℕ) (V : Submodule (ZMod 2) (𝔽₂ n)) (hV : IsCoveringSubspace n r V) :
    2 ^ n ≤ Nat.card V * Nat.card (hammingBall n r) := by
  have h := Set.natCard_add_le (s := (V : Set (𝔽₂ n))) (t := hammingBall n r)
  rw [hV, Nat.card_univ, g40_card_space] at h
  exact h

lemma g40_ge (n r : ℕ) : 1 ≤ minDensity n r := by
  unfold minDensity
  refine le_iInf₂ fun V hV => ?_
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
  exact_mod_cast g40_lower n r V hV

lemma g40_two_add {k : ℕ} (x : Fin k → ZMod 2) : x + x = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x i = a
  fin_cases a <;> rfl

/-- The Hamming code of length `2^m - 1`. -/
lemma g40_hamming (m : ℕ) : ∃ V : Submodule (ZMod 2) (𝔽₂ (2 ^ m - 1)),
    IsCoveringSubspace (2 ^ m - 1) 1 V ∧ Nat.card V * 2 ^ m = 2 ^ (2 ^ m - 1) := by
  set n := 2 ^ m - 1 with hn
  have hcard : Fintype.card {v : Fin m → ZMod 2 // v ≠ 0} = n := by
    rw [Fintype.card_subtype_compl, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    simp [hn]
  let e : Fin n ≃ {v : Fin m → ZMod 2 // v ≠ 0} := (Fintype.equivFinOfCardEq hcard).symm
  let H : 𝔽₂ n →ₗ[ZMod 2] (Fin m → ZMod 2) := ∑ i, (LinearMap.proj i).smulRight (e i).1
  have hH : ∀ x, H x = ∑ i, x i • (e i).1 := by
    intro x; simp [H]
  have hHs : ∀ j, H (Pi.single j 1) = (e j).1 := by
    intro j; rw [hH]; simp [Pi.single_apply]
  refine ⟨LinearMap.ker H, ?_, ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    rw [Set.mem_add]
    by_cases hx : H x = 0
    · exact ⟨x, by simpa using hx, 0, by simp [hammingBall, hammingNorm_zero], add_zero x⟩
    · set j := e.symm ⟨H x, hx⟩
      have hej : (e j).1 = H x := by simp [j]
      refine ⟨x + Pi.single j 1, ?_, Pi.single j 1, ?_, ?_⟩
      · simp only [SetLike.mem_coe, LinearMap.mem_ker, map_add, hHs, hej]
        exact g40_two_add (H x)
      · simp [hammingBall, g40_norm_single]
      · rw [add_assoc, g40_two_add, add_zero]
  · have hsurj : LinearMap.range H = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro s
      by_cases hs : s = 0
      · exact ⟨0, by simp [hs]⟩
      · exact ⟨Pi.single (e.symm ⟨s, hs⟩) 1, by rw [hHs]; simp⟩
    have hrk := LinearMap.finrank_range_add_finrank_ker H
    rw [hsurj, finrank_top] at hrk
    simp only [Module.finrank_fin_fun] at hrk
    have hcV : Nat.card (LinearMap.ker H) = 2 ^ (n - m) := by
      haveI := Fintype.ofFinite (LinearMap.ker H)
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
      congr 1; omega
    have hmn : m ≤ n := by have := Nat.lt_two_pow_self (n := m); omega
    rw [hcV, ← pow_add]; congr 1; omega

lemma g40_le (m : ℕ) : minDensity (2 ^ m - 1) 1 ≤ 1 := by
  obtain ⟨V, hV, hc⟩ := g40_hamming m
  unfold minDensity
  refine (iInf₂_le V hV).trans ?_
  rw [g40_card_ball]
  have h1 : 2 ^ m - 1 + 1 = 2 ^ m := Nat.sub_add_cancel Nat.one_le_two_pow
  have : (Nat.card V : ℝ≥0∞) * ((2 ^ m - 1 + 1 : ℕ) : ℝ≥0∞) = 2 ^ (2 ^ m - 1) := by
    rw [h1]; exact_mod_cast hc
  rw [this, ENNReal.div_self (by simp) (by simp)]

theorem g40_main : f 1 = 1 := by
  unfold f
  apply le_antisymm
  · apply Filter.liminf_le_of_frequently_le'
    rw [Filter.frequently_atTop]
    intro a
    refine ⟨2 ^ (a + 1) - 1, ?_, g40_le (a + 1)⟩
    have := Nat.lt_two_pow_self (n := a + 1); omega
  · exact Filter.le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall fun n => g40_ge n 1)



set_option linter.style.formal_proof_palomar false in
/-- The only value known is $f(1) = 1$, which follows from the existence of the Hamming code [Gr24]. -/
@[category research solved, AMS 5 94, formal_proof using lean4 at "https://github.com/anatoliiohorodnyk/lean-fc-proofs/blob/5da9642575b26c2c816a49bcb56b33fed5456619/Proofs/T_Green40_green_40_sanity_f_one.lean#L216"]
theorem green_40.sanity_f_one : f 1 = 1 := by
  exact g40_main

set_option linter.style.formal_proof_palomar false in
/-- $f(r) \le r^r / r! \sim e^r$ [Gr24]. -/
@[category research solved, AMS 5 94, formal_proof using lean4 at "https://github.com/anatoliiohorodnyk/lean-fc-proofs/blob/5da9642575b26c2c816a49bcb56b33fed5456619/Proofs/T_Green40_green_40_upper_bound.lean#L245"]
theorem green_40.upper_bound (r : ℕ) : f r ≤ (r ^ r : ℝ≥0∞) / (r.factorial : ℝ≥0∞) := by
  sorry

/-- The possibility that f(r) = 1 for all r has not been ruled out [Gr24] -/
@[category research open, question, AMS 5 94]
theorem green_40.f_eq_one_for_all : ∀ r, f r = 1 := by
  sorry

/-- It is not known whether f(2) = 1 [Gr24] -/
@[category research open, question, AMS 5 94]
theorem green_40.f_two_eq_one : f 2 = 1 := by
  sorry

/-- The best-known upper bound for $f(2)$ is $1.4238$ [CHL97]. -/
@[category research solved, AMS 5 94]
theorem green_40.upper_bound_f_two : f 2 ≤ (1.4238 : ℝ≥0∞) := by
  sorry

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- Variant with arbitrary subsets
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

def hammingBallFinset (n r : ℕ) : Finset (𝔽₂ n) :=
  Finset.univ.filter (fun x => hammingNorm x ≤ r)

def IsCoveringFinset (n r : ℕ) (V : Finset (𝔽₂ n)) : Prop :=
  V + hammingBallFinset n r = Finset.univ

noncomputable def minDensityFinset (n r : ℕ) : ℝ≥0∞ :=
  ⨅ (V : Finset (𝔽₂ n)) (_ : IsCoveringFinset n r V),
    (V.card : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞)

noncomputable def f_tilde (r : ℕ) : ℝ≥0∞ :=
  liminf (fun n ↦ minDensityFinset n r) atTop

/-- Does $\tilde{f}(r) \to \infty$? [Gr24] -/
@[category research open, question, AMS 5 94]
theorem green_40.variants.arbitrary_subsets : Tendsto f_tilde atTop (𝓝 ⊤) := by
  sorry

/-- It is known that $\tilde{f}(2) = 1$ [St94]. -/
@[category research solved, AMS 5 94]
theorem green_40.variants.arbitrary_subsets_sanity_f_tilde_two : f_tilde 2 = 1 := by
  sorry

/-- We evidently have $\tilde{f}(r) \le f(r)$ [Gr24]. -/
@[category research solved, AMS 5 94]
theorem green_40.f_tilde_le_f (r : ℕ) : f_tilde r ≤ f r := by
  refine Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n => ?_)
  refine le_iInf₂ fun V hV => ?_
  have hfin : (V : Set (𝔽₂ n)).Finite := Set.toFinite _
  have hcov : IsCoveringFinset n r hfin.toFinset := by
    unfold IsCoveringFinset
    ext x
    simp only [Finset.mem_univ, iff_true]
    have hx : x ∈ (V : Set (𝔽₂ n)) + hammingBall n r := hV ▸ Set.mem_univ x
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    exact Finset.mem_add.mpr
      ⟨a, hfin.mem_toFinset.mpr ha, b, by simpa [hammingBallFinset, hammingBall] using hb, hab⟩
  have hcard : (hfin.toFinset.card : ℝ≥0∞) = (Nat.card V : ℝ≥0∞) := by
    have h : Nat.card V = hfin.toFinset.card := by
      rw [show Nat.card V = Nat.card (V : Set (𝔽₂ n)) from rfl, Nat.card_coe_set_eq,
        Set.ncard_eq_toFinset_card _ hfin]
    exact_mod_cast congrArg Nat.cast h.symm
  calc minDensityFinset n r
      ≤ (hfin.toFinset.card : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) /
          (2 ^ n : ℝ≥0∞) :=
        iInf₂_le hfin.toFinset hcov
    _ = (Nat.card V : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) /
          (2 ^ n : ℝ≥0∞) := by
        rw [hcard]

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- Variant for all n
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

noncomputable def f_all (r : ℕ) : ℝ≥0∞ :=
  limsup (fun n ↦ minDensity n r) atTop

/-- Does $f_{\text{all}}(r) \to \infty$? [Gr24]

The target filter is `𝓝 ⊤`, as in `green_40` and `green_40.variants.arbitrary_subsets`. On
`ℝ≥0∞`, `atTop` is the principal ultrafilter at `⊤`, so `Tendsto f_all atTop atTop` would say
that `f_all r = ⊤` for all large `r` rather than that `f_all r → ∞`. -/
@[category research open, question, AMS 5 94]
theorem green_40.variants.all_n : Tendsto f_all atTop (𝓝 ⊤) := by
  sorry

end Green40
