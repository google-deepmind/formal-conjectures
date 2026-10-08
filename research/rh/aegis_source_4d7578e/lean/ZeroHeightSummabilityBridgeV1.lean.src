import ZeroHeightLimitContractV1
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Order.Filter.AtTopBot.Finset

/-!
AEGIS Ω — unconditional-summability sufficient bridge to the symmetric height limit v1.

This lane does NOT prove that the zeta-zero summand is summable. It proves only
that the already verified symmetric-height truncations form a cofinal family of
finite subsets of the subtype of nontrivial zeta zeros, and therefore that an
explicit `HasSum` premise for the multiplicity-weighted Mellin summand implies
the previously verified `T → +∞` height-limit contract.

Unconditional `HasSum` is a deliberately strong sufficient hypothesis here. It
is not asserted to be equivalent to any weaker conditionally convergent
classical zero-summation convention.

UNCONDITIONAL_SUMMABILITY_SUFFICIENT_ONLY
ACTUAL_ZERO_SUM_SUMMABILITY_OPEN
HEIGHT_LIMIT_EXISTENCE_UNCONDITIONAL_OPEN
HEIGHT_RADIAL_EQUIVALENCE_OPEN
EXPLICIT_FORMULA_OPEN
CRITICAL_LINE_RE_HALF_OPEN
RH_EQUIVALENCE_OPEN
-/

open Set Filter Topology
open Complex

noncomputable section

/-- The subtype of all nontrivial Riemann-zeta zeros, using the same exclusion
of the trivial zeros as the verified height-truncation lane. -/
def RiemannNontrivialZeroIndexV2 :=
  { rho : ℂ //
      riemannZeta rho = 0 ∧
      (¬ ∃ n : ℕ, rho = -(2 : ℂ) * (n + 1)) }

private theorem parent_height_finset_mem_iff_v1 {T : ℝ} {s : ℂ} :
    s ∈ NontrivialZeroHeightFinsetV1 T ↔ s ∈ NontrivialZeroHeightSetV1 T := by
  simp [NontrivialZeroHeightFinsetV1]

/-- Each attached member of the verified complex-valued height finset canonically
becomes an element of the subtype of nontrivial zeros. -/
private def height_attach_to_nontrivial_index_v1 (T : ℝ) :
    {s // s ∈ NontrivialZeroHeightFinsetV1 T} ↪ RiemannNontrivialZeroIndexV2 where
  toFun s :=
    ⟨s.1, by
      have hsSet : s.1 ∈ NontrivialZeroHeightSetV1 T :=
        parent_height_finset_mem_iff_v1.mp s.2
      exact ⟨hsSet.1, hsSet.2.1⟩⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun rho : RiemannNontrivialZeroIndexV2 => rho.1) hab

/-- Canonical finite-height carrier, now indexed directly by the subtype of
nontrivial zeros. It is obtained without enumerating the zero set. -/
noncomputable def NontrivialZeroHeightIndexFinsetV1 (T : ℝ) :
    Finset RiemannNontrivialZeroIndexV2 :=
  (NontrivialZeroHeightFinsetV1 T).attach.map
    (height_attach_to_nontrivial_index_v1 T)

private theorem mem_nontrivial_zero_height_index_finset_v1
    {T : ℝ} {rho : RiemannNontrivialZeroIndexV2} :
    rho ∈ NontrivialZeroHeightIndexFinsetV1 T ↔ |rho.1.im| ≤ T := by
  constructor
  · intro hrho
    rw [NontrivialZeroHeightIndexFinsetV1, Finset.mem_map] at hrho
    rcases hrho with ⟨x, hx, hxrho⟩
    have hxSet : x.1 ∈ NontrivialZeroHeightSetV1 T :=
      parent_height_finset_mem_iff_v1.mp x.2
    have hval : x.1 = rho.1 := by
      exact congrArg Subtype.val hxrho
    simpa [hval] using hxSet.2.2
  · intro him
    have hparent : rho.1 ∈ NontrivialZeroHeightFinsetV1 T :=
      parent_height_finset_mem_iff_v1.mpr ⟨rho.2.1, rho.2.2, him⟩
    let x : {s // s ∈ NontrivialZeroHeightFinsetV1 T} := ⟨rho.1, hparent⟩
    have hxattach : x ∈ (NontrivialZeroHeightFinsetV1 T).attach := by
      simp [x]
    have hxrho : height_attach_to_nontrivial_index_v1 T x = rho := by
      apply Subtype.ext
      rfl
    rw [NontrivialZeroHeightIndexFinsetV1, Finset.mem_map]
    exact ⟨x, hxattach, hxrho⟩

private theorem nontrivial_zero_height_index_finset_mono_v1 :
    Monotone NontrivialZeroHeightIndexFinsetV1 := by
  intro T U hTU rho hrho
  apply mem_nontrivial_zero_height_index_finset_v1.mpr
  exact (mem_nontrivial_zero_height_index_finset_v1.mp hrho).trans hTU

/-- The height-indexed finite carriers are cofinal among all finite subsets of
nontrivial zeta zeros. For a finite set `s`, the sum of `|Im rho|` over `s`
is a concrete height bound containing every member. -/
theorem tendsto_nontrivial_zero_height_index_finset_atTop_v1 :
    Tendsto NontrivialZeroHeightIndexFinsetV1 atTop atTop := by
  apply nontrivial_zero_height_index_finset_mono_v1.tendsto_atTop_atTop
  intro s
  refine ⟨∑ rho ∈ s, |rho.1.im|, ?_⟩
  intro rho hrho
  apply mem_nontrivial_zero_height_index_finset_v1.mpr
  exact Finset.single_le_sum (fun z _ => abs_nonneg z.1.im) hrho

/-- The multiplicity-weighted Mellin summand, now indexed by the subtype of
nontrivial zeros. -/
def WeilZeroIndexSummandV1
    (f : ℝ → ℂ) (rho : RiemannNontrivialZeroIndexV2) : ℂ :=
  (analyticOrderNatAt riemannZeta rho.1 : ℂ) * mellin f rho.1

/-- The subtype-indexed finite-height sum is exactly the previously verified
complex-valued finite-height truncation. -/
theorem nontrivial_zero_height_index_sum_eq_truncated_v1
    (f : ℝ → ℂ) (T : ℝ) :
    (NontrivialZeroHeightIndexFinsetV1 T).sum (WeilZeroIndexSummandV1 f) =
      WeilZeroHeightTruncatedSumV1 f T := by
  classical
  rw [NontrivialZeroHeightIndexFinsetV1, Finset.sum_map]
  unfold WeilZeroHeightTruncatedSumV1
  change
    (∑ x ∈ (NontrivialZeroHeightFinsetV1 T).attach,
      (analyticOrderNatAt riemannZeta x.1 : ℂ) * mellin f x.1) =
    ∑ s ∈ NontrivialZeroHeightFinsetV1 T,
      (analyticOrderNatAt riemannZeta s : ℂ) * mellin f s
  exact Finset.sum_attach (NontrivialZeroHeightFinsetV1 T)
    (fun s : ℂ => (analyticOrderNatAt riemannZeta s : ℂ) * mellin f s)

/-- A genuine unconditional `HasSum` proof for the multiplicity-weighted
nontrivial-zero summand is sufficient to produce the verified symmetric-height
limit contract. This theorem does not construct such a `HasSum` proof. -/
theorem hasSum_implies_height_limit_v1
    {f : ℝ → ℂ} {L : ℂ}
    (hsum : HasSum (WeilZeroIndexSummandV1 f) L) :
    HasWeilZeroHeightLimitV1 f L := by
  have hindexed :
      Tendsto
        (fun T : ℝ =>
          (NontrivialZeroHeightIndexFinsetV1 T).sum
            (WeilZeroIndexSummandV1 f))
        atTop (𝓝 L) := by
    exact hsum.comp tendsto_nontrivial_zero_height_index_finset_atTop_v1
  unfold HasWeilZeroHeightLimitV1
  convert hindexed using 1
  funext T
  exact (nontrivial_zero_height_index_sum_eq_truncated_v1 f T).symm

#check RiemannNontrivialZeroIndexV2
#check NontrivialZeroHeightIndexFinsetV1
#check tendsto_nontrivial_zero_height_index_finset_atTop_v1
#check WeilZeroIndexSummandV1
#check nontrivial_zero_height_index_sum_eq_truncated_v1
#check hasSum_implies_height_limit_v1
#print axioms tendsto_nontrivial_zero_height_index_finset_atTop_v1
#print axioms nontrivial_zero_height_index_sum_eq_truncated_v1
#print axioms hasSum_implies_height_limit_v1
