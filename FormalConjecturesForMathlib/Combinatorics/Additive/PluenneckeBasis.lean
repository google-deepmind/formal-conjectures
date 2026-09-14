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

public import FormalConjecturesForMathlib.Combinatorics.Additive.Basis
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

/-! # Plünnecke's inequality for asymptotic bases

Tools for counting arguments that combine the Plünnecke–Ruzsa inequality with the hypothesis
that a set of naturals is an asymptotic additive basis.

## Main results

* `nat_pluennecke_div`: the Plünnecke–Ruzsa inequality $|kB| / |B| \le (|B + B| / |B|)^k$ for a
  nonempty finite set of naturals, stated over $\mathbb{R}$.
* `mem_nsmul_Iic`: if $a \le N$ lies in $hA$, then $a$ lies in $h(A \cap [0, N])$, because every
  summand is at most $a$.
* `ncard_inter_Iic_le` and `ncard_sumset_Iic_le`: compare counting functions on $[0, N]$ with
  counting functions on $[1, N]$.
-/

open Filter Set Asymptotics

open scoped Pointwise

/-- The Plünnecke–Ruzsa inequality over $\mathbb{R}$: for a nonempty finite set $B$ of naturals,
$|kB| / |B| \le (|B + B| / |B|)^k$. -/
lemma nat_pluennecke_div (B : Finset ℕ) (hB : B.Nonempty) (k : ℕ) :
    (↑(k • B).card : ℝ) / ↑B.card ≤ ((↑(B + B).card : ℝ) / ↑B.card) ^ k := by
  let f : ℕ →+ ℤ := Nat.castRingHom ℤ
  have hf : Function.Injective f := Nat.cast_injective
  have hB' : (B.image f).Nonempty := hB.image f
  have h_plu := Finset.pluennecke_ruzsa_inequality_nsmul_add hB' (B.image f) k
  rw [← Finset.image_add, ← Finset.image_nsmul] at h_plu
  rw [Finset.card_image_of_injective _ hf] at h_plu
  rw [Finset.card_image_of_injective _ hf] at h_plu
  rw [Finset.card_image_of_injective _ hf] at h_plu
  have h_cast : (↑(k • B).card : ℝ) = (↑(↑(k • B).card : ℚ≥0) : ℝ) := by simp
  have h_cast2 : ((↑(B + B).card : ℝ) / ↑B.card) ^ k * ↑B.card =
      (↑(((↑(B + B).card : ℚ≥0) / ↑B.card) ^ k * ↑B.card) : ℝ) := by
    push_cast; rfl
  have h_real : (↑(k • B).card : ℝ) ≤ ((↑(B + B).card : ℝ) / ↑B.card) ^ k * ↑B.card := by
    rw [h_cast, h_cast2]
    exact_mod_cast h_plu
  have hBpos : 0 < (↑B.card : ℝ) := Nat.cast_pos.mpr hB.card_pos
  exact (div_le_iff₀ hBpos).mpr h_real

/-- Each summand of a sum of naturals is at most any upper bound for the sum. -/
lemma le_of_sum_eq_nat {n : ℕ} (f : Fin n → ℕ) {a N : ℕ} (hsum : ∑ i, f i = a)
    (ha : a ≤ N) (i : Fin n) : f i ≤ N := by
  have : f i ≤ ∑ j, f j := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- If `a ≤ N` is a sum of `h` elements of `A`, then it is a sum of `h` elements of `A ∩ Iic N`. -/
lemma mem_nsmul_Iic {A : Set ℕ} {h : ℕ} {a N : ℕ}
    (ha_mem : a ∈ h • A) (ha_le : a ≤ N) :
    a ∈ h • (A ∩ Iic N) := by
  rw [Set.mem_nsmul_iff_sum] at ha_mem ⊢
  obtain ⟨f, hf, rfl⟩ := ha_mem
  refine ⟨f, fun i ↦ ⟨hf i, ?_⟩, rfl⟩
  exact le_of_sum_eq_nat f rfl ha_le i

lemma mem_finset_nsmul {s : Set ℕ} (hs : s.Finite) (n : ℕ) (a : ℕ) (ha : a ∈ n • s) :
    a ∈ n • hs.toFinset := by
  rw [← Finset.mem_coe, Finset.coe_nsmul, hs.coe_toFinset]
  exact ha

lemma sumset_Iic_subset (A : Set ℕ) (N : ℕ) :
    (A ∩ Iic N) + (A ∩ Iic N) ⊆ insert 0 ((A + A) ∩ Icc 1 (2 * N)) := by
  rintro x ⟨y, ⟨hyA, hyN⟩, z, ⟨hzA, hzN⟩, rfl⟩
  rcases eq_or_ne (y + z) 0 with h0 | _
  · exact Or.inl h0
  · right
    refine ⟨⟨y, hyA, z, hzA, rfl⟩, ?_⟩
    rw [mem_Icc]
    rw [mem_Iic] at hyN hzN
    dsimp only
    omega

lemma inter_Iic_subset (A : Set ℕ) (N : ℕ) :
    A ∩ Iic N ⊆ insert 0 (A ∩ Icc 1 N) := by
  rintro x ⟨hxA, hxN⟩
  rcases eq_or_ne x 0 with rfl | _
  · exact Or.inl rfl
  · right
    refine ⟨hxA, ?_⟩
    rw [mem_Icc]
    rw [mem_Iic] at hxN
    omega

lemma ncard_inter_Iic_le (A : Set ℕ) (N : ℕ) :
    (A ∩ Iic N).ncard ≤ (A ∩ Icc 1 N).ncard + 1 := by
  have hfin : (insert 0 (A ∩ Icc 1 N)).Finite :=
    ((finite_Icc 1 N).inter_of_right A).insert 0
  have hsub := inter_Iic_subset A N
  have hle := ncard_le_ncard hsub hfin
  have h_ins := ncard_insert_le 0 (A ∩ Icc 1 N)
  omega

lemma ncard_sumset_Iic_le (A : Set ℕ) (N : ℕ) :
    ((A ∩ Iic N) + (A ∩ Iic N)).ncard ≤ ((A + A) ∩ Icc 1 (2 * N)).ncard + 1 := by
  have hfin : (insert 0 ((A + A) ∩ Icc 1 (2 * N))).Finite :=
    ((finite_Icc 1 (2 * N)).inter_of_right (A + A)).insert 0
  have hsub := sumset_Iic_subset A N
  have hle := ncard_le_ncard hsub hfin
  have h_ins := ncard_insert_le 0 ((A + A) ∩ Icc 1 (2 * N))
  omega

lemma ncard_Icc_nat_eq (a b : ℕ) : (Icc a b).ncard = b + 1 - a := by
  rw [← Finset.coe_Icc, ncard_coe_finset, Nat.card_Icc]

/-- An asymptotic additive basis of naturals contains a positive element. -/
lemma exists_pos_mem_of_basis {A : Set ℕ} {h : ℕ}
    (hA : A.IsAsymptoticAddBasisOfOrder h) :
    ∃ a ∈ A, 1 ≤ a := by
  rw [isAsymptoticAddBasisOfOrder_iff_atTop, eventually_atTop] at hA
  obtain ⟨N₀, hN₀⟩ := hA
  have h_mem := hN₀ (N₀ + 1) (by omega)
  rw [Set.mem_nsmul_iff_sum] at h_mem
  obtain ⟨f, hf, _⟩ := h_mem
  by_contra! h_all_zero
  have h_sum_zero : ∑ i : Fin h, f i = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have := h_all_zero (f i) (hf i)
    omega
  omega

/-- An `o(N)` counting function is eventually bounded by `ε * N`. -/
lemma little_o_bound {A : Set ℕ}
    (ho : (fun N : ℕ ↦ ((A ∩ Icc 1 N).ncard : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₁, ∀ N ≥ N₁, ((A ∩ Icc 1 N).ncard : ℝ) ≤ ε * N := by
  have h := (isLittleO_iff.mp ho) hε
  rw [eventually_atTop] at h
  obtain ⟨N₁, hN₁⟩ := h
  refine ⟨N₁, fun N hN ↦ ?_⟩
  have := hN₁ N hN
  rw [Real.norm_natCast, Real.norm_natCast] at this
  exact this

lemma div_le_div_sub_one {x y b : ℝ} (hy : 1 ≤ y) (h : b + 1 ≤ (x + 1) / y) :
    b ≤ x / y := by
  have hypos : 0 < y := by linarith
  have h1 : 1 / y ≤ 1 := by
    rw [div_le_iff₀ hypos]
    linarith
  have h2 : (x + 1) / y = x / y + 1 / y := add_div x 1 y
  linarith

lemma le_of_pow_le_pow {u v : ℝ} {n : ℕ} (hv : 0 ≤ v) (hn : n ≠ 0)
    (h : u ^ n ≤ v ^ n) : u ≤ v := by
  by_contra! hlt
  have := pow_lt_pow_left₀ hlt hv hn
  linarith

/-- The quantitative bound driving the Plünnecke argument for asymptotic bases. -/
lemma bound_K_le {N N₀ : ℕ} {c K M : ℝ} {h : ℕ}
    (hc : 1 ≤ c)
    (hK_pos : 0 < K)
    (hc_le : c ≤ 1 / (2 * K) * (N : ℝ))
    (hN_ge : 2 * (K + N₀) ≤ (N : ℝ))
    (hK_def : (M + 1) ^ h + 1 ≤ K) :
    (M + 1) ^ h < (N + 1 - N₀ : ℝ) / (c + 1) := by
  have hc1 : 0 < c + 1 := by linarith
  have h1 : K * c ≤ (N : ℝ) / 2 := by
    have h_cancel : K * (1 / (2 * K) * (N : ℝ)) = (N : ℝ) / 2 := by
      have : 2 * K ≠ 0 := by linarith
      field_simp
    calc K * c
      _ ≤ K * (1 / (2 * K) * (N : ℝ)) := by nlinarith
      _ = (N : ℝ) / 2 := h_cancel
  have h2 : K + (N₀ : ℝ) ≤ (N : ℝ) / 2 := by linarith
  have h3 : K * (c + 1) + (N₀ : ℝ) ≤ (N : ℝ) := by
    calc K * (c + 1) + (N₀ : ℝ)
      _ = K * c + (K + (N₀ : ℝ)) := by ring
      _ ≤ (N : ℝ) / 2 + (N : ℝ) / 2 := by linarith
      _ = (N : ℝ) := by ring
  have h4 : K * (c + 1) ≤ (N : ℝ) - (N₀ : ℝ) := by linarith
  have h5 : K ≤ (N + 1 - N₀ : ℝ) / (c + 1) := by
    rw [le_div_iff₀ hc1]
    linarith
  linarith
