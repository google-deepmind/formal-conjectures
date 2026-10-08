import RHHatPosDefV13

/-!
AEGIS Ω — algebra of hat kernels on a grid, V13.

`hatK h n v u = Σ_{i,j<n} v_i v_j T_h(u − (i−j)h)` is continuous, takes the value
`h · ρ_k` at the node `kh` (with `ρ_k = Σ_j v_{j+k} v_j`), is affine on every cell
`[kh, (k+1)h]`, and integrates over a cell by the trapezoid rule.  These are the facts a
numerical certificate needs about the positive-definite kernel of `RHHatPosDefV13`.
Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set MeasureTheory
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHHatKernelV13
open AEGIS.RHHatPosDefV13

/-- The hat kernel with weights `v`. -/
def hatK (h : ℝ) (n : ℕ) (v : ℕ → ℝ) (u : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * hatT h (u - ((i : ℝ) - j) * h)

/-- The autocorrelation sequence of `v`. -/
def rhoK (n : ℕ) (v : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, if j + k < n then v (j + k) * v j else 0

theorem hatT_continuous (h : ℝ) : Continuous (hatT h) := by
  unfold hatT; fun_prop

theorem hatK_continuous (h : ℝ) (n : ℕ) (v : ℕ → ℝ) : Continuous (hatK h n v) := by
  unfold hatK
  apply continuous_finsetSum; intro i _
  apply continuous_finsetSum; intro j _
  exact continuous_const.mul ((hatT_continuous h).comp (by fun_prop))

theorem hatT_int (h : ℝ) (hh : 0 < h) (m : ℤ) : hatT h (m * h) = if m = 0 then h else 0 := by
  unfold hatT
  split_ifs with hm
  · subst hm; simp [hh.le]
  · have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm
    rw [abs_mul, abs_of_pos hh]
    apply max_eq_left
    nlinarith

theorem hatT_affine (h : ℝ) (hh : 0 < h) (k d : ℤ) (u : ℝ) (hu1 : k * h ≤ u)
    (hu2 : u ≤ (k + 1) * h) :
    hatT h (u - d * h) = ((k + 1) * h - u) / h * hatT h (((k - d : ℤ) : ℝ) * h) +
      (u - k * h) / h * hatT h (((k + 1 - d : ℤ) : ℝ) * h) := by
  rw [hatT_int h hh, hatT_int h hh]
  rcases lt_trichotomy d k with hdk | hdk | hdk
  · -- d ≤ k - 1
    have hd : (d : ℝ) + 1 ≤ k := by exact_mod_cast hdk
    rw [if_neg (by omega), if_neg (by omega)]
    unfold hatT
    have : h ≤ u - d * h := by nlinarith
    rw [abs_of_nonneg (by linarith)]
    simp only [mul_zero, add_zero]
    exact max_eq_left (by linarith)
  · subst hdk
    rw [if_pos (by omega), if_neg (by omega)]
    unfold hatT
    rw [abs_of_nonneg (by linarith)]
    rw [max_eq_right (by nlinarith)]
    field_simp
    ring
  · rcases lt_or_eq_of_le (show k + 1 ≤ d by omega) with hdk' | hdk'
    · have hd : (k : ℝ) + 2 ≤ d := by exact_mod_cast (show k + 2 ≤ d by omega)
      rw [if_neg (by omega), if_neg (by omega)]
      unfold hatT
      have : u - d * h ≤ -h := by nlinarith
      rw [abs_of_neg (by linarith)]
      simp only [mul_zero, add_zero]
      exact max_eq_left (by linarith)
    · subst hdk'
      rw [if_neg (by omega), if_pos (by omega)]
      unfold hatT
      push_cast
      rw [abs_of_nonpos (by linarith)]
      rw [max_eq_right (by nlinarith)]
      field_simp
      ring

/-- `hatK` is affine on each grid cell. -/
theorem hatK_affine (h : ℝ) (hh : 0 < h) (n : ℕ) (v : ℕ → ℝ) (k : ℕ) (u : ℝ)
    (hu1 : k * h ≤ u) (hu2 : u ≤ (k + 1) * h) :
    hatK h n v u = ((k + 1) * h - u) / h * hatK h n v (k * h) +
      (u - k * h) / h * hatK h n v ((k + 1) * h) := by
  unfold hatK
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  have ha := hatT_affine h hh (k : ℤ) ((i : ℤ) - j) u (by exact_mod_cast hu1)
    (by exact_mod_cast hu2)
  push_cast at ha
  have e1 : (k : ℝ) * h - ((i : ℝ) - j) * h = ((k : ℝ) - (i - j)) * h := by ring
  have e2 : ((k : ℝ) + 1) * h - ((i : ℝ) - j) * h = ((k : ℝ) + 1 - (i - j)) * h := by ring
  rw [e1, e2, ha]
  ring

/-- Node values: `hatK (k h) = h · ρ_k`. -/
theorem hatK_node (h : ℝ) (hh : 0 < h) (n : ℕ) (v : ℕ → ℝ) (k : ℕ) :
    hatK h n v (k * h) = h * rhoK n v k := by
  unfold hatK rhoK
  have e : ∀ i j : ℕ, hatT h ((k : ℝ) * h - ((i : ℝ) - j) * h) =
      if i = j + k then h else 0 := by
    intro i j
    have := hatT_int h hh ((k : ℤ) - (i - j))
    push_cast at this
    rw [show (k : ℝ) * h - ((i : ℝ) - j) * h = ((k : ℝ) - (i - j)) * h by ring, this]
    congr 1
    apply propext
    omega
  simp_rw [e]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' (Finset.range n) (j + k) (fun i => v i * v j * h)]
  simp only [Finset.mem_range]
  split_ifs <;> ring

/-- Trapezoid rule on a cell. -/
theorem hatK_cell_integral (h : ℝ) (hh : 0 < h) (n : ℕ) (v : ℕ → ℝ) (k : ℕ) :
    (∫ u in Ioc ((k : ℝ) * h) ((k + 1) * h), hatK h n v u) =
      h / 2 * (hatK h n v (k * h) + hatK h n v ((k + 1) * h)) := by
  set A := hatK h n v (k * h)
  set B := hatK h n v ((k + 1) * h)
  have hle : (k : ℝ) * h ≤ (k + 1) * h := by nlinarith
  rw [← intervalIntegral.integral_of_le hle]
  have hcongr : (∫ u in (k : ℝ) * h..(k + 1) * h, hatK h n v u) =
      ∫ u in (k : ℝ) * h..(k + 1) * h, (((k + 1) * h * A - k * h * B) / h + (B - A) / h * u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hle] at hu
    simp only
    rw [hatK_affine h hh n v k u hu.1 hu.2]
    field_simp
    ring
  rw [hcongr, intervalIntegral.integral_add (f := fun _ => ((k + 1) * h * A - k * h * B) / h)
      (g := fun u => (B - A) / h * u) intervalIntegrable_const
      ((continuous_const.mul continuous_id).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- Trapezoid rule over a run of cells. -/
theorem hatK_run_integral (h : ℝ) (hh : 0 < h) (n : ℕ) (v : ℕ → ℝ) (a m : ℕ) :
    (∫ u in Ioc ((a : ℝ) * h) ((a + m : ℕ) * h), hatK h n v u) =
      ∑ k ∈ Finset.range m, h / 2 *
        (hatK h n v ((a + k : ℕ) * h) + hatK h n v ((a + k + 1 : ℕ) * h)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hle1 : (a : ℝ) * h ≤ ((a + m : ℕ) : ℝ) * h := by
      apply mul_le_mul_of_nonneg_right _ hh.le; exact_mod_cast Nat.le_add_right a m
    have hle2 : ((a + m : ℕ) : ℝ) * h ≤ ((a + (m + 1) : ℕ) : ℝ) * h := by
      apply mul_le_mul_of_nonneg_right _ hh.le; exact_mod_cast (by omega : a + m ≤ a + (m + 1))
    have hc := (hatK_continuous h n v)
    rw [← Ioc_union_Ioc_eq_Ioc hle1 hle2,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        hc.integrableOn_Ioc hc.integrableOn_Ioc, ih, Finset.sum_range_succ]
    congr 1
    have hcell := hatK_cell_integral h hh n v (a + m)
    push_cast at hcell ⊢
    rw [show ((a : ℝ) + (m + 1)) * h = ((a : ℝ) + m + 1) * h by ring, hcell]

end AEGIS.RHHatKernelV13
