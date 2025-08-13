-- import Mathlib.Alhe
import Mathlib.Algebra.Opposites


private def Subgroup.toMulOpposite {G : Type*} [Group G] (H : Subgroup G) :
    Subgroup (Gᵐᵒᵖ) where
  carrier := .op '' H.carrier
  mul_mem' := by
    intro a b ⟨u, hu, hu'⟩ ⟨v, hv, hv'⟩
    rw [←hu', ←hv', ←MulOpposite.op_mul]
    use v * u
    refine ⟨H.mul_mem hv hu, rfl⟩
  one_mem' := by
    use 1
    simp [Subgroup.one_mem H]
  inv_mem' := by
    intro x ⟨u, hu, hu'⟩
    use u⁻¹
    refine ⟨H.inv_mem' hu, ?_⟩
    rw [←hu', MulOpposite.op_inv]
