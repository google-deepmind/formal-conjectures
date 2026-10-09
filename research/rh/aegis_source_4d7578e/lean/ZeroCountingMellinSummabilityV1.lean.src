import ZeroCountingBoundV1
import MellinDecayEstimateV1

/-!
AEGIS Ω — multiplicity-safe Mellin summability and canonical height limit.

The pinned Hadamard provider already proves multiplicity-weighted inverse-square
summability for xi from its order-at-most-one growth. Transferring multiplicity
to zeta and using the critical strip gives a shorter route than reimplementing
dyadic counting. Uniform quadratic Mellin decay is sufficient; the existing
compact-smooth cubic theorem supplies it.

This establishes an absolutely convergent zero functional on the existing
compact-smooth domain and identifies its symmetric-height limit. It supplies
neither the preregistered linear shell bound, the explicit formula, positivity,
nor RH. No simple-zero assumption is made.
-/

open Set Filter Topology
open Complex

noncomputable section

/-- Reusable comparison lemma: weighted inverse-square summability and a
bounded-width strip turn quadratic height decay into absolute summability.
The nonzero premise prevents division by the totalized value at zero. -/
theorem weighted_summable_of_inverse_square_and_height_decay_v1
    {ι : Type*} (z : ι → ℂ) (m : ι → ℕ) (F : ι → ℂ)
    (hzero : ∀ i, z i ≠ 0)
    (hstrip : ∀ i, |(z i).re| ≤ 1)
    (hsum : Summable (fun i => (m i : ℝ) / ‖z i‖ ^ 2))
    {D : ℝ}
    (hdecay : ∀ i, (1 + |(z i).im|) ^ 2 * ‖F i‖ ≤ D) :
    Summable (fun i => (m i : ℂ) * F i) := by
  apply Summable.of_norm_bounded (hsum.mul_left D)
  intro i
  have hn : 0 < ‖z i‖ := norm_pos_iff.mpr (hzero i)
  have hgeom : ‖z i‖ ≤ 1 + |(z i).im| :=
    (Complex.norm_le_abs_re_add_abs_im (z i)).trans
      (add_le_add (hstrip i) le_rfl)
  have hscaled : ‖z i‖ ^ 2 * ‖F i‖ ≤ D := by
    calc
      ‖z i‖ ^ 2 * ‖F i‖ ≤ (1 + |(z i).im|) ^ 2 * ‖F i‖ := by
        gcongr
      _ ≤ D := hdecay i
  have hF : ‖F i‖ ≤ D / ‖z i‖ ^ 2 :=
    (le_div_iff₀' (pow_pos hn 2)).2 hscaled
  calc
    ‖(m i : ℂ) * F i‖ = (m i : ℝ) * ‖F i‖ := by simp
    _ ≤ (m i : ℝ) * (D / ‖z i‖ ^ 2) := by gcongr
    _ = D * ((m i : ℝ) / ‖z i‖ ^ 2) := by ring

/-- Canonical injection into the independently pinned xi provider's carrier.
The AEGIS zero definition is retained throughout the public result. -/
private def nontrivial_index_to_li_v1 :
    RiemannNontrivialZeroIndexV2 ↪ LiCriterion.NontrivialZero where
  toFun rho := by
    have hstrip :=
      riemann_zeta_nontrivial_zero_critical_strip_v1 rho.2.1 rho.2.2
    exact ⟨rho.1, rho.2.1, hstrip.1, hstrip.2⟩
  inj' := by
    intro rho sigma h
    exact Subtype.ext (congrArg (fun z : LiCriterion.NontrivialZero => z.1) h)

/-- Multiplicity-weighted inverse-square summability transferred from xi to
the existing AEGIS nontrivial-zeta-zero carrier. -/
theorem riemann_zeta_weighted_inverse_square_summable_v1 :
    Summable (fun rho : RiemannNontrivialZeroIndexV2 =>
      (analyticOrderNatAt riemannZeta rho.1 : ℝ) / ‖rho.1‖ ^ 2) := by
  have hxi := LiCriterion.xi_weighted_genus_one_of_hadamard_order_one
    LiCriterion.XiGrowth.riemannXi_hasFiniteOrder
    LiCriterion.XiGrowth.riemannXi_order_le_one
  have hpull := hxi.comp_injective nontrivial_index_to_li_v1.injective
  change Summable (fun rho : RiemannNontrivialZeroIndexV2 =>
    (analyticOrderNatAt LiCriterion.riemannXi rho.1 : ℝ) / ‖rho.1‖ ^ 2) at hpull
  have hmult : ∀ rho : RiemannNontrivialZeroIndexV2,
      analyticOrderNatAt LiCriterion.riemannXi rho.1 =
        analyticOrderNatAt riemannZeta rho.1 := by
    intro rho
    exact li_xi_zeta_multiplicity_eq_v1 (nontrivial_index_to_li_v1 rho)
  simpa only [hmult] using hpull

/-- A supplied uniform quadratic Mellin estimate suffices on the canonical
zero carrier. The inverse-square provider is stronger than a bare quadratic
cumulative count and is explicitly used in this theorem. -/
theorem zero_summable_of_uniform_mellin_quadratic_decay_v1
    {f : ℝ → ℂ} {D : ℝ}
    (hdecay : ∀ rho : RiemannNontrivialZeroIndexV2,
      (1 + |rho.1.im|) ^ 2 * ‖mellin f rho.1‖ ≤ D) :
    Summable (WeilZeroIndexSummandV1 f) := by
  apply weighted_summable_of_inverse_square_and_height_decay_v1
    (fun rho : RiemannNontrivialZeroIndexV2 => rho.1)
    (fun rho => analyticOrderNatAt riemannZeta rho.1)
    (fun rho => mellin f rho.1)
    _ _ riemann_zeta_weighted_inverse_square_summable_v1 hdecay
  · intro rho hzero
    have hs := riemann_zeta_nontrivial_zero_critical_strip_v1 rho.2.1 rho.2.2
    rw [hzero] at hs
    norm_num at hs
  · intro rho
    have hs := riemann_zeta_nontrivial_zero_critical_strip_v1 rho.2.1 rho.2.2
    rw [abs_of_pos hs.1]
    exact hs.2.le

/-- Actual compact-smooth Mellin zero summability, with multiplicities. -/
theorem weil_compact_smooth_zero_summable_v1 (g : WeilCompactSmoothGV1) :
    Summable (WeilZeroIndexSummandV1 g.1) := by
  obtain ⟨D, hD, hdecay⟩ :=
    weil_compact_smooth_mellin_vertical_cubic_decay_v1 g
  apply zero_summable_of_uniform_mellin_quadratic_decay_v1 (D := D)
  intro rho
  have hs := riemann_zeta_nontrivial_zero_critical_strip_v1 rho.2.1 rho.2.2
  have hd := hdecay rho.1.re ⟨hs.1.le, hs.2.le⟩ rho.1.im
  have hz : ((rho.1.re : ℂ) + (rho.1.im : ℂ) * Complex.I) = rho.1 := by
    apply Complex.ext <;> simp
  rw [hz] at hd
  have ht : 1 ≤ 1 + |rho.1.im| := by linarith [abs_nonneg rho.1.im]
  have hp : (1 + |rho.1.im|) ^ 2 ≤ (1 + |rho.1.im|) ^ 3 := by
    calc
      (1 + |rho.1.im|) ^ 2 ≤ (1 + |rho.1.im|) ^ 2 * (1 + |rho.1.im|) :=
        le_mul_of_one_le_right (sq_nonneg _) ht
      _ = (1 + |rho.1.im|) ^ 3 := by ring
  exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans hd

/-- The zero series is absolutely convergent, rather than merely having a
chosen symmetric summation prescription. -/
theorem weil_compact_smooth_zero_norm_summable_v1 (g : WeilCompactSmoothGV1) :
    Summable (fun rho => ‖WeilZeroIndexSummandV1 g.1 rho‖) :=
  (weil_compact_smooth_zero_summable_v1 g).norm

/-- The existing finite symmetric-height expression converges to the canonical
unordered sum on the compact-smooth domain. -/
theorem weil_compact_smooth_height_limit_tsum_v1 (g : WeilCompactSmoothGV1) :
    HasWeilZeroHeightLimitV1 g.1
      (∑' rho, WeilZeroIndexSummandV1 g.1 rho) :=
  hasSum_implies_height_limit_v1 (weil_compact_smooth_zero_summable_v1 g).hasSum

/-- Any previously supplied symmetric-height limit on this domain is the
canonical absolutely convergent zero sum. -/
theorem weil_compact_smooth_height_limit_eq_tsum_v1
    (g : WeilCompactSmoothGV1) {L : ℂ}
    (hL : HasWeilZeroHeightLimitV1 g.1 L) :
    L = ∑' rho, WeilZeroIndexSummandV1 g.1 rho :=
  weil_zero_height_limit_unique_v1 hL (weil_compact_smooth_height_limit_tsum_v1 g)

#print axioms weighted_summable_of_inverse_square_and_height_decay_v1
#print axioms riemann_zeta_weighted_inverse_square_summable_v1
#print axioms zero_summable_of_uniform_mellin_quadratic_decay_v1
#print axioms weil_compact_smooth_zero_summable_v1
#print axioms weil_compact_smooth_zero_norm_summable_v1
#print axioms weil_compact_smooth_height_limit_tsum_v1
#print axioms weil_compact_smooth_height_limit_eq_tsum_v1
