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
# Cohen–Lenstra Heuristics for Quadratic Class Groups

Henri Cohen and Hendrik W. Lenstra Jr. [CL84, Co93] formulated probabilistic heuristics for the
odd part of the ideal class group $\operatorname{Cl}(\mathcal{O}_{\mathbb{Q}(\sqrt{d})})$ as
$\mathbb{Q}(\sqrt{d})$ varies over imaginary ($d < 0$) or real ($d > 0$) quadratic fields ordered
by absolute fundamental discriminant $|D(d)|$.

For an odd prime $p$ and a finite abelian $p$-group $G$, the heuristic at unit rank $u$ ($u = 0$
when $d < 0$, $u = 1$ when $d > 0$) predicts that the proportion of quadratic fields whose
$p$-Sylow class-group subgroup is isomorphic to $G$ converges to
$$w_{p, u}(G) =
  \frac{\prod_{k=1}^\infty \left(1 - p^{-(k + u)}\right)}{|G|^u \cdot |\operatorname{Aut}(G)|}.$$
The cited Wikipedia section mentions only that these heuristics exist and quotes their $\approx
75.45\%$ class-number-$1$ prediction for prime-radicand real quadratic fields; the explicit odd
$p$-part formulas formalized below come from [CL84] and [Co93, §5.10].

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Class_number_problem#Real_quadratic_fields)
- [CL84] H. Cohen and H. W. Lenstra Jr. (1984), Lecture Notes in Math. **1068**, Springer, 33–62.
- [Co93] H. Cohen (1993), Grad. Texts in Math. **138**, Springer, §5.10.
-/

@[expose] public section

namespace CohenLenstraHeuristics

open NumberField
open scoped NumberField

open scoped Classical in
/-- Negative squarefree radicands $d < 0$ with $|D(d)| \le X$. -/
noncomputable def imagQuadRadicandsUpTo (X : ℕ) : Finset ℤ :=
  (Finset.Icc (-(X : ℤ)) (-1)).filter (fun d => Squarefree d ∧ (quadFundDisc d).natAbs ≤ X)

open scoped Classical in
/-- Positive squarefree radicands $d \ge 2$ with $D(d) \le X$. -/
noncomputable def realQuadRadicandsUpTo (X : ℕ) : Finset ℤ :=
  (Finset.Icc 2 (X : ℤ)).filter (fun d => Squarefree d ∧ (quadFundDisc d).natAbs ≤ X)

/-- Predicate that $d \ne 1$ is squarefree and the $p$-Sylow subgroup of
$\operatorname{Cl}(\mathcal{O}_{\mathbb{Q}(\sqrt{d})})$ is isomorphic to $G$. -/
def HasQuadPSylowIso (p : ℕ) (G : Type*) [CommGroup G] (d : ℤ) : Prop :=
  ∃ (hsf : Squarefree d) (hne : d ≠ 1),
    letI : Fact (Squarefree d) := ⟨hsf⟩
    letI : Fact (d ≠ 1) := ⟨hne⟩
    ∃ P : Sylow p (ClassGroup (𝓞 (QuadraticAlgebra ℚ d 0))), Nonempty (P ≃* G)

/-- Cohen–Lenstra $p$-Sylow probability weight
$w_{p, u}(G) = \frac{\prod_{k=1}^\infty (1 - p^{-(k+u)})}{|G|^u \cdot |\operatorname{Aut}(G)|}$
at unit rank $u$ ($u = 0$ in the imaginary case, $u = 1$ in the real case). -/
noncomputable def cohenLenstraWeight (p u : ℕ) (G : Type*) [CommGroup G] [Finite G] : ℝ :=
  (∏' k : ℕ, (1 - (p : ℝ) ^ (-((k + u + 1 : ℕ) : ℤ)))) /
    (((Nat.card G) ^ u * Nat.card (G ≃* G) : ℕ) : ℝ)

open scoped Classical in
/-- **Cohen–Lenstra Heuristic (Imaginary Quadratic Case, $u = 0$)** [CL84; Co93, §5.10]: given an
odd prime $p$ and finite abelian $p$-group $G$, the fraction of imaginary quadratic discriminants
$|D(d)| \le X$ whose $p$-Sylow class-group subgroup is isomorphic to $G$ tends to
`cohenLenstraWeight p 0 G`. (Wikipedia notes only the existence of the heuristics and their
$\approx 75.45\%$ real-quadratic prediction; this odd-$p$-part formula comes from [CL84] and
[Co93, §5.10].) -/
@[category research open, AMS 11]
theorem cohen_lenstra_imaginary_quadratic_p_sylow_conjecture (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (G : Type*) [CommGroup G] [Fintype G] (hG : IsPGroup p G) :
    Filter.Tendsto
      (fun X : ℕ =>
        (((imagQuadRadicandsUpTo X).filter (HasQuadPSylowIso p G)).card : ℝ) /
          ((imagQuadRadicandsUpTo X).card : ℝ))
      Filter.atTop (nhds (cohenLenstraWeight p 0 G)) := by
  sorry

open scoped Classical in
/-- **Cohen–Lenstra Heuristic (Real Quadratic Case, $u = 1$)** [CL84; Co93, §5.10]: given an odd
prime $p$ and finite abelian $p$-group $G$, the fraction of real quadratic discriminants
$0 < D(d) \le X$ whose $p$-Sylow class-group subgroup is isomorphic to $G$ tends to
`cohenLenstraWeight p 1 G`. (Wikipedia notes only the existence of the heuristics and their
$\approx 75.45\%$ prediction; this odd-$p$-part formula comes from [CL84] and [Co93, §5.10].) -/
@[category research open, AMS 11]
theorem cohen_lenstra_real_quadratic_p_sylow_conjecture (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (G : Type*) [CommGroup G] [Fintype G] (hG : IsPGroup p G) :
    Filter.Tendsto
      (fun X : ℕ =>
        (((realQuadRadicandsUpTo X).filter (HasQuadPSylowIso p G)).card : ℝ) /
          ((realQuadRadicandsUpTo X).card : ℝ))
      Filter.atTop (nhds (cohenLenstraWeight p 1 G)) := by
  sorry

/-- Degenerate radicands $d = 0$ and $d = 1$ never satisfy `HasQuadPSylowIso`. -/
@[category API, AMS 11]
theorem not_hasQuadPSylowIso_zero_and_one (p : ℕ) (G : Type*) [CommGroup G] :
    ¬ HasQuadPSylowIso p G 0 ∧ ¬ HasQuadPSylowIso p G 1 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hsf, _, _⟩
    exact not_squarefree_zero hsf
  · rintro ⟨_, hne, _⟩
    exact hne rfl

/-- Small-cutoff checks for `quadFundDisc`, `imagQuadRadicandsUpTo`, and `realQuadRadicandsUpTo`. -/
@[category test, AMS 11]
theorem radicandsUpTo_initial_examples :
    quadFundDisc (-3) = -3 ∧ quadFundDisc (-1) = -4 ∧ quadFundDisc 5 = 5 ∧
      (-3 : ℤ) ∈ imagQuadRadicandsUpTo 3 ∧ (2 : ℤ) ∈ realQuadRadicandsUpTo 8 := by
  classical
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · rw [imagQuadRadicandsUpTo, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, Int.squarefree_natAbs.mp Nat.prime_three.squarefree, by decide⟩
  · rw [realQuadRadicandsUpTo, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, Int.squarefree_natAbs.mp Nat.prime_two.squarefree, by decide⟩

/-- At $p = 3$ and $u = 0$, the Euler product `cohenLenstraWeight 3 0 Unit` converges to a real in
$[1/2, 2/3]$ (verifying genuine `tprod` convergence away from $0$ and $1$). -/
@[category test, AMS 11]
theorem cohenLenstraWeight_three_zero_unit_bounds :
    (1 / 2 : ℝ) ≤ cohenLenstraWeight 3 0 Unit ∧ cohenLenstraWeight 3 0 Unit ≤ 2 / 3 := by
  let g : ℕ → ℝ := fun k => (1 / 3 : ℝ) * (1 / 3 : ℝ) ^ k
  have hunit : cohenLenstraWeight 3 0 Unit = ∏' k : ℕ, (1 - g k) := by
    simp only [cohenLenstraWeight, Nat.add_zero, pow_zero, one_mul, Nat.card_unique, Nat.cast_one,
      div_one]; congr 1; ext k; dsimp [g]
    rw [show -((k : ℤ) + 1) = -1 - (k : ℤ) by omega, zpow_sub₀ (by norm_num),
      zpow_neg_one, zpow_natCast, one_div, inv_pow, div_eq_mul_inv]
  have h0 (k : ℕ) : 0 ≤ 1 - g k := sub_nonneg.mpr
    (by dsimp [g]; nlinarith [pow_le_one₀ (by positivity : (0 : ℝ) ≤ 1 / 3) (by norm_num) (n := k)])
  have hweier (s : Finset ℕ) : 1 - ∑ k ∈ s, g k ≤ ∏ k ∈ s, (1 - g k) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hp1 : ∏ k ∈ s, (1 - g k) ≤ 1 := Finset.prod_le_one (fun k _ => h0 k)
        (fun k _ => sub_le_self 1 (by dsimp [g]; positivity))
      nlinarith [show 0 ≤ g a by dsimp [g]; positivity]
  have hbdd : BddBelow (Set.range fun s : Finset ℕ => ∏ k ∈ s, (1 - g k)) :=
    ⟨0, by rintro _ ⟨s, rfl⟩; exact Finset.prod_nonneg fun k _ => h0 k⟩
  have hanti : Antitone (fun s : Finset ℕ => ∏ k ∈ s, (1 - g k)) := fun s t hst => by
    classical dsimp only
    rw [← Finset.sdiff_union_of_subset hst, Finset.prod_union Finset.sdiff_disjoint]
    exact mul_le_of_le_one_left (Finset.prod_nonneg fun k _ => h0 k)
      (Finset.prod_le_one (fun k _ => h0 k) fun k _ => sub_le_self 1 (by dsimp [g]; positivity))
  rw [hunit, (show HasProd (fun k => 1 - g k) _ from tendsto_atTop_ciInf hanti hbdd).tprod_eq]
  refine ⟨le_ciInf fun s => ?_, (ciInf_le hbdd {0}).trans (by norm_num [g])⟩
  have hg_sum := hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num)
  have hle := mul_le_mul_of_nonneg_left
    (hg_sum.summable.sum_le_tsum s fun _ _ => by positivity) (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rw [Finset.mul_sum, hg_sum.tsum_eq] at hle
  linarith [show (1 / 3 : ℝ) * (1 - 1 / 3)⁻¹ = 1 / 2 by norm_num, hweier s]

end CohenLenstraHeuristics
