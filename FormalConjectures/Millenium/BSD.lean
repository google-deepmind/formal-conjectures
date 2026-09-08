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
# The Birch and Swinnerton-Dyer (BSD) Conjecture

*References:*
- [The Clay Institute](https://www.claymath.org/millennium/birch-and-swinnerton-dyer-conjecture/),
  official problem description by Andrew Wiles:
  [PDF](https://www.claymath.org/wp-content/uploads/2022/05/birchswin.pdf)
- [BSD1965] B. J. Birch and H. P. F. Swinnerton-Dyer. "Notes on elliptic curves. II."
  Journal fur die reine und angewandte Mathematik 218 (1965), 79-108,
  [doi](https://doi.org/10.1515/crll.1965.218.79)
- [Tate1966] John Tate. "On the conjectures of Birch and Swinnerton-Dyer and a geometric analog."
  Seminaire Bourbaki, Vol. 9, Exp. No. 306 (1966), 415-440,
  [numdam](https://www.numdam.org/item/SB_1964-1966__9__415_0/)
- [Gross2011] Benedict H. Gross. "Lectures on the conjecture of Birch and Swinnerton-Dyer."
  Arithmetic of L-functions, IAS/Park City Math. Ser. 18, AMS (2011), 169-209,
  [PDF](https://people.math.harvard.edu/~gross/preprints/lectures-pcmi.pdf)
- [Ang2025] David Kurniadi Angdinata. "L-functions of Dirichlet twists of elliptic curves:
  computations and congruences." PhD thesis, University College London (2025),
  [PDF](https://discovery.ucl.ac.uk/10223687/1/main-pages.pdf)
- [Ada] Tom Adamczewski. "Autoformalized conjectures",
  [Birch and Swinnerton-Dyer](https://tadamcz.com/autoformalization-results/#/p/wp-birch-and-swinnerton-dyer-conjecture)
- [Silverman2009] Joseph H. Silverman. *The Arithmetic of Elliptic Curves*. 2nd ed., Graduate Texts
  in Mathematics 106, Springer (2009), [doi](https://doi.org/10.1007/978-0-387-09494-6)
-/

namespace WeierstrassCurve

section GlobalMinimal

/-- A Weierstrass equation over $\mathbb{Q}$ is *globally minimal* if its coefficients lie in
$\mathbb{Z}$ and $|\Delta|$ is least among all Weierstrass equations with coefficients in
$\mathbb{Z}$ that are isomorphic to it over $\mathbb{Q}$.

For an elliptic curve this is equivalent to the definition in [Silverman2009], Section VIII.8: an
equation with coefficients in $\mathbb{Z}$ that is minimal at every prime. See
`WeierstrassCurve.isGlobalMinimal_iff_forall_isMinimal`. -/
@[mk_iff]
class IsGlobalMinimal (W : WeierstrassCurve ℚ) : Prop extends W.IsIntegral ℤ where
  abs_Δ_le : ∀ C : VariableChange ℚ, (C • W).IsIntegral ℤ → |W.Δ| ≤ |(C • W).Δ|

/-- Every Weierstrass equation over $\mathbb{Q}$ is isomorphic to one with coefficients in
$\mathbb{Z}$. -/
@[category API, AMS 11 14]
theorem exists_isIntegral_int (W : WeierstrassCurve ℚ) :
    ∃ C : VariableChange ℚ, (C • W).IsIntegral ℤ := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors ℤ)
    {W.a₁, W.a₂, W.a₃, W.a₄, W.a₆}
  have hb0 : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero b
  have key : ∀ (n : ℕ) (a : ℚ), IsLocalization.IsInteger ℤ ((b : ℤ) • a) →
      ∃ r : ℤ, algebraMap ℤ ℚ r = ((b : ℤ) : ℚ) ^ (n + 1) * a := fun n a ⟨r, hr⟩ ↦
    ⟨(b : ℤ) ^ n * r, by push_cast at hr ⊢; linear_combination ((b : ℤ) : ℚ) ^ n * hr⟩
  refine ⟨⟨(Units.mk0 _ hb0)⁻¹, 0, 0, 0⟩, isIntegral_of_exists_lift ℤ ?_ ?_ ?_ ?_ ?_⟩
  · simpa [variableChange_a₁] using key 0 _ (hb _ (by simp))
  · simpa [variableChange_a₂] using key 1 _ (hb _ (by simp))
  · simpa [variableChange_a₃] using key 2 _ (hb _ (by simp))
  · simpa [variableChange_a₄] using key 3 _ (hb _ (by simp))
  · simpa [variableChange_a₆] using key 5 _ (hb _ (by simp))

/-- Every Weierstrass equation over $\mathbb{Q}$ is isomorphic to a globally minimal one. -/
@[category API, AMS 11 14]
theorem exists_isGlobalMinimal (W : WeierstrassCurve ℚ) :
    ∃ C : VariableChange ℚ, IsGlobalMinimal (C • W) := by
  classical
  have key : ∀ C : VariableChange ℚ, (C • W).IsIntegral ℤ → ∃ n : ℕ, |(C • W).Δ| = n :=
    fun C _ ↦ let ⟨r, hr⟩ := Δ_integral_of_isIntegral ℤ (C • W)
      ⟨r.natAbs, by simp [← hr, Nat.cast_natAbs]⟩
  obtain ⟨C₀, hC₀⟩ := W.exists_isIntegral_int
  have h : ∃ n : ℕ, ∃ C : VariableChange ℚ, (C • W).IsIntegral ℤ ∧ |(C • W).Δ| = n :=
    (key C₀ hC₀).imp fun n hn ↦ ⟨C₀, hC₀, hn⟩
  obtain ⟨C, hC, hn⟩ := Nat.find_spec h
  refine ⟨C, { toIsIntegral := hC, abs_Δ_le := fun C' hC' ↦ ?_ }⟩
  obtain ⟨n', hn'⟩ := key (C' * C) (by rwa [mul_smul])
  rw [← mul_smul, hn, hn', Nat.cast_le]
  exact Nat.find_min' h ⟨C' * C, by rwa [mul_smul], hn'⟩

/-- A globally minimal Weierstrass equation isomorphic to `W`, chosen using
`WeierstrassCurve.exists_isGlobalMinimal`. This is the global analogue of
`WeierstrassCurve.minimal`. -/
noncomputable def globalMinimal (W : WeierstrassCurve ℚ) : WeierstrassCurve ℚ :=
  W.exists_isGlobalMinimal.choose • W

instance (W : WeierstrassCurve ℚ) : W.globalMinimal.IsGlobalMinimal :=
  W.exists_isGlobalMinimal.choose_spec

instance (W : WeierstrassCurve ℚ) [W.IsElliptic] : W.globalMinimal.IsElliptic :=
  inferInstanceAs (W.exists_isGlobalMinimal.choose • W).IsElliptic

@[category API, AMS 11 14]
theorem exists_smul_eq_globalMinimal (W : WeierstrassCurve ℚ) :
    ∃ C : VariableChange ℚ, C • W = W.globalMinimal :=
  ⟨_, rfl⟩

@[category API, AMS 11 14]
theorem abs_Δ_eq_of_isGlobalMinimal (W : WeierstrassCurve ℚ) (C : VariableChange ℚ)
    [W.IsGlobalMinimal] [(C • W).IsGlobalMinimal] : |(C • W).Δ| = |W.Δ| := by
  have h := IsGlobalMinimal.abs_Δ_le (W := C • W) C⁻¹ (by rw [inv_smul_smul]; infer_instance)
  exact le_antisymm (by rwa [inv_smul_smul] at h) (IsGlobalMinimal.abs_Δ_le C inferInstance)

/-- Two globally minimal Weierstrass equations for the same elliptic curve over $\mathbb{Q}$ differ
by a change of variables with $u = \pm 1$. Compare [Silverman2009], Proposition VII.1.3(b). -/
@[category API, AMS 11 14]
theorem abs_u_eq_one_of_isGlobalMinimal (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : VariableChange ℚ) [W.IsGlobalMinimal] [(C • W).IsGlobalMinimal] :
    |(C.u : ℚ)| = 1 := by
  have h := abs_Δ_eq_of_isGlobalMinimal W C
  rw [variableChange_Δ, abs_mul, mul_eq_right₀ (abs_ne_zero.2 W.isUnit_Δ.ne_zero)] at h
  simpa [abs_pow, pow_eq_one_iff_of_nonneg] using h

open IsDedekindDomain in
/-- An elliptic curve over $\mathbb{Q}$ is globally minimal if and only if its coefficients lie in
$\mathbb{Z}$ and it is minimal at every prime. This is [Silverman2009], Corollary VIII.8.3, together
with Proposition VII.1.3; it uses that $\mathbb{Z}$ is a principal ideal domain. -/
@[category textbook, AMS 11 14]
theorem isGlobalMinimal_iff_forall_isMinimal (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    W.IsGlobalMinimal ↔ W.IsIntegral ℤ ∧ ∀ v : HeightOneSpectrum ℤ,
      (W.baseChange (v.adicCompletion ℚ)).IsMinimal (v.adicCompletionIntegers ℚ) := by
  sorry

end GlobalMinimal

end WeierstrassCurve

namespace BirchSwinnertonDyer

open scoped Topology

variable {K : Type*} [Field K] [NumberField K] {E : WeierstrassCurve K}

def IsLFunction (E : WeierstrassCurve K) (L : ℂ → ℂ) : Prop :=
  Meromorphic L ∧ ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s

@[category API, AMS 11 14]
theorem IsLFunction.unique {L L' : ℂ → ℂ} (hL : IsLFunction E L) (hL' : IsLFunction E L')
    (x : ℂ) : L =ᶠ[𝓝[≠] x] L' := by
  have h2 : meromorphicOrderAt (L - L') 2 = ⊤ := meromorphicOrderAt_eq_top_iff.2 <|
    Filter.Eventually.mono (nhdsWithin_le_nhds <| (Complex.isOpen_re_gt (3 / 2)).mem_nhds
      (by norm_num)) fun s hs => sub_eq_zero.2 ((hL.2 s hs).trans (hL'.2 s hs).symm)
  have key : meromorphicOrderAt (L - L') x = ⊤ := not_not.1 fun hx =>
    (hL.1.sub hL'.1).exists_meromorphicOrderAt_ne_top_iff_forall.1 ⟨x, hx⟩ 2 h2
  exact (meromorphicOrderAt_eq_top_iff.1 key).mono fun s hs => sub_eq_zero.1 hs

/-- **Hasse--Weil conjecture**: the $L$-function of an elliptic curve over a number field extends
to the whole plane. -/
@[category research open, AMS 11 14]
theorem exists_isLFunction (E : WeierstrassCurve K) [E.IsElliptic] : ∃ L, IsLFunction E L := by
  sorry

/-- The **Hasse--Weil conjecture** over $\mathbb{Q}$, a consequence of the modularity theorem. -/
@[category research solved, AMS 11 14]
theorem exists_isLFunction_rat (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ L, IsLFunction E L := by
  sorry

end BirchSwinnertonDyer
