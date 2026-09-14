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
# Erdős Problem 337

*References:*
- [erdosproblems.com/337](https://www.erdosproblems.com/337)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [ErGr80b] Erdős, P. and Graham, R. L., *On bases with an exact order*. Acta Arith. (1980),
  201-207.
- [RT85] Ruzsa, I. Z. and Turjányi, S., *A note on additive bases of integers*. Publ. Math.
  Debrecen (1985), 101-104.
- [Tu84] Turjányi, S., *A note on basis sequences*. Topics in classical number theory, Vol. I, II
  (Budapest, 1981) (1984), 1571-1576.
-/

namespace Erdos337

open Filter Set Asymptotics

open scoped Pointwise

/--
Let $A\subseteq \mathbb{N}$ be an additive basis (of any finite order) such that
$\lvert A\cap \{1,\ldots,N\}\rvert=o(N)$. Is it true that
$$
\lim_{N\to \infty}\frac{\lvert (A+A)\cap \{1,\ldots,N\}\rvert}
{\lvert A\cap \{1,\ldots,N\}\rvert}=\infty?
$$

The answer is no, and a counterexample was provided by Turjányi [Tu84]. This was generalised (to
the replacement of $A+A$ by the $h$-fold sumset $hA$ for any $h\geq 2$) by Ruzsa and Turjányi
[RT85].

"Additive basis" is `Set.IsAsymptoticAddBasis`: some finite $h$ has $hA$ containing every
sufficiently large integer. The exact notion `Set.IsAddBasis`, which asks that $hA$ be all of
$\mathbb{N}$, would force $0, 1 \in A$ and is not the class these results are about.

The linked file states the basis hypothesis as `∃ N₀, Set.Ici N₀ ⊆ iterated_sumset A k` and
indexes both counting functions by a real $x$ through $\lfloor x\rfloor$, where the counting
functions here are indexed by $N : \mathbb{N}$.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/68da20b96673899166e94638f5a7fffeb7231d35/src/latest/ErdosProblems/Erdos337.lean"]
theorem erdos_337 : answer(False) ↔
    ∀ A : Set ℕ, A.IsAsymptoticAddBasis →
      (fun N : ℕ ↦ ((A ∩ Icc 1 N).ncard : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) →
      Tendsto (fun N : ℕ ↦ (((A + A) ∩ Icc 1 N).ncard : ℝ) / ((A ∩ Icc 1 N).ncard : ℝ))
        atTop atTop := by
  sorry

/--
This was generalised (to the replacement of $A+A$ by the $h$-fold sumset $hA$ for any $h\geq 2$)
by Ruzsa and Turjányi [RT85].
-/
@[category research solved, AMS 5 11]
theorem erdos_337.variants.h_fold : ∀ h : ℕ, 2 ≤ h →
    ∃ A : Set ℕ, A.IsAsymptoticAddBasis ∧
      (fun N : ℕ ↦ ((A ∩ Icc 1 N).ncard : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) ∧
      ¬ Tendsto (fun N : ℕ ↦
          ((h • A ∩ Icc 1 N).ncard : ℝ) / ((A ∩ Icc 1 N).ncard : ℝ))
        atTop atTop := by
  sorry

/--
Ruzsa and Turjányi do prove (under the same hypotheses) that
$$
\lim_{N\to \infty}\frac{\lvert (A+A+A)\cap \{1,\ldots,3N\}\rvert}
{\lvert A\cap \{1,\ldots,N\}\rvert}=\infty,
$$
and conjecture that the same should be true with $(A+A)\cap \{1,\ldots,2N\}$ in the numerator.

This follows from the Plünnecke–Ruzsa inequality applied to $B=A\cap\{0,\ldots,N\}$: if $A$ is a
basis of order $h$ then $hB$ contains every element of $\{N_0,\ldots,N\}$, so
$(\lvert B+B\rvert/\lvert B\rvert)^h\geq \lvert hB\rvert/\lvert B\rvert\gg N/\lvert B\rvert$,
which tends to infinity since $\lvert B\rvert=o(N)$.
-/
@[category research solved, AMS 5 11]
theorem erdos_337.variants.ruzsa_turjanyi :
    ∀ A : Set ℕ, A.IsAsymptoticAddBasis →
      (fun N : ℕ ↦ ((A ∩ Icc 1 N).ncard : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) →
      Tendsto (fun N : ℕ ↦
          (((A + A) ∩ Icc 1 (2 * N)).ncard : ℝ) / ((A ∩ Icc 1 N).ncard : ℝ))
        atTop atTop := by
  intro A h_basis ho
  obtain ⟨h, hA⟩ := h_basis
  have h_h_ne : h ≠ 0 := by rintro rfl; exact not_isAsymptoticAddBasisOfOrder_zero hA
  have h_h_pos : 1 ≤ h := by omega
  obtain ⟨a_pos, ha_pos_mem, _⟩ := exists_pos_mem_of_basis hA
  have hA_top := hA
  rw [isAsymptoticAddBasisOfOrder_iff_atTop, eventually_atTop] at hA_top
  obtain ⟨N₀, hN₀⟩ := hA_top
  rw [tendsto_atTop_atTop]
  intro b
  rcases le_or_gt b 0 with _ | _
  · refine ⟨a_pos, fun N hN ↦ ?_⟩
    have h_mem : a_pos ∈ A ∩ Icc 1 N := ⟨ha_pos_mem, by rw [mem_Icc]; omega⟩
    have h_nonempty : (A ∩ Icc 1 N).Nonempty := ⟨a_pos, h_mem⟩
    have hc_pos : 1 ≤ ((A ∩ Icc 1 N).ncard : ℝ) := by
      have hfin : (A ∩ Icc 1 N).Finite := (finite_Icc 1 N).inter_of_right A
      have : 0 < (A ∩ Icc 1 N).ncard := h_nonempty.ncard_pos (hs := hfin)
      have : 1 ≤ (A ∩ Icc 1 N).ncard := by omega
      exact_mod_cast this
    have hs_nonneg : 0 ≤ (((A + A) ∩ Icc 1 (2 * N)).ncard : ℝ) := Nat.cast_nonneg _
    have : 0 ≤ (((A + A) ∩ Icc 1 (2 * N)).ncard : ℝ) / ((A ∩ Icc 1 N).ncard : ℝ) :=
      div_nonneg hs_nonneg (by linarith)
    linarith
  · set M := b
    set K := (M + 1) ^ h + 1 with _
    have hM1 : 0 ≤ M + 1 := by linarith
    have hK_pos : 0 < K := by
      have : 0 ≤ (M + 1) ^ h := pow_nonneg hM1 h
      linarith
    have h_eps_pos : 0 < 1 / (2 * K) := by positivity
    obtain ⟨N₁, hN₁⟩ := little_o_bound ho h_eps_pos
    set N_bound := Nat.ceil (2 * (K + N₀)) with _
    refine ⟨max N₁ (max (max N₀ a_pos) N_bound), fun N hN ↦ ?_⟩
    have hNN₁ : N₁ ≤ N := (le_max_left N₁ _).trans hN
    have hN_rest : max (max N₀ a_pos) N_bound ≤ N := (le_max_right N₁ _).trans hN
    have hNN₀ : N₀ ≤ N := (le_max_left N₀ a_pos).trans
      ((le_max_left (max N₀ a_pos) N_bound).trans hN_rest)
    have hNa_pos : a_pos ≤ N := (le_max_right N₀ a_pos).trans
      ((le_max_left (max N₀ a_pos) N_bound).trans hN_rest)
    have hNN_bound : N_bound ≤ N :=
      (le_max_right (max N₀ a_pos) N_bound).trans hN_rest
    have hN_ge_real : 2 * (K + N₀) ≤ (N : ℝ) := by
      have : (Nat.ceil (2 * (K + N₀)) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNN_bound
      exact (Nat.le_ceil (2 * (K + N₀))).trans this
    set c := ((A ∩ Icc 1 N).ncard : ℝ)
    set s := (((A + A) ∩ Icc 1 (2 * N)).ncard : ℝ)
    set B_set := A ∩ Iic N
    have hB_fin : B_set.Finite := (finite_Iic N).inter_of_right A
    set B := hB_fin.toFinset
    have hB_card_eq : (B.card : ℝ) = (B_set.ncard : ℝ) := by
      rw [← ncard_coe_finset, Finite.coe_toFinset]
    have ha_pos_in_B : a_pos ∈ B := by
      rw [Finite.mem_toFinset]
      exact ⟨ha_pos_mem, by rw [mem_Iic]; exact hNa_pos⟩
    have hB_nonempty : B.Nonempty := ⟨a_pos, ha_pos_in_B⟩
    have hB_card_pos : 0 < (B.card : ℝ) := Nat.cast_pos.mpr hB_nonempty.card_pos
    have h_mem_pos : a_pos ∈ A ∩ Icc 1 N := ⟨ha_pos_mem, by rw [mem_Icc]; omega⟩
    have hc_pos : 1 ≤ c := by
      have hfin : (A ∩ Icc 1 N).Finite := (finite_Icc 1 N).inter_of_right A
      have h_ne : (A ∩ Icc 1 N).Nonempty := ⟨a_pos, h_mem_pos⟩
      have : 0 < (A ∩ Icc 1 N).ncard := h_ne.ncard_pos (hs := hfin)
      have : 1 ≤ (A ∩ Icc 1 N).ncard := by omega
      change 1 ≤ ((A ∩ Icc 1 N).ncard : ℝ)
      exact_mod_cast this
    have hc_le_eps : c ≤ 1 / (2 * K) * (N : ℝ) := hN₁ N hNN₁
    have hK_bound : (M + 1) ^ h < (N + 1 - N₀ : ℝ) / (c + 1) :=
      bound_K_le hc_pos hK_pos hc_le_eps hN_ge_real (by linarith)
    have h_card_le : (N + 1 - N₀ : ℝ) ≤ (↑(h • B).card : ℝ) := by
      have h_sub : Icc N₀ N ⊆ (h • B : Finset ℕ) := by
        intro x hx
        rw [mem_Icc] at hx
        have hx_A : x ∈ h • A := hN₀ x hx.1
        have hx_Iic : x ∈ h • (A ∩ Iic N) := mem_nsmul_Iic hx_A hx.2
        exact mem_finset_nsmul hB_fin h x hx_Iic
      have h_ncard_le := ncard_le_ncard h_sub (Finset.finite_toSet (h • B))
      rw [ncard_Icc_nat_eq N₀ N, ncard_coe_finset] at h_ncard_le
      have h_sub_nat : (N : ℝ) + 1 - (N₀ : ℝ) = ((N + 1 - N₀ : ℕ) : ℝ) := by
        have : N₀ ≤ N + 1 := by omega
        have h_cast := Nat.cast_sub (R := ℝ) this
        push_cast at h_cast
        exact h_cast.symm
      rw [h_sub_nat]
      exact_mod_cast h_ncard_le
    have hB_le : (B.card : ℝ) ≤ c + 1 := by
      rw [hB_card_eq]
      dsimp only [c]
      have : B_set.ncard ≤ (A ∩ Icc 1 N).ncard + 1 := ncard_inter_Iic_le A N
      exact_mod_cast this
    have hB_ge : c ≤ (B.card : ℝ) := by
      rw [hB_card_eq]
      dsimp only [c]
      have h_sub : A ∩ Icc 1 N ⊆ B_set := by
        rintro x ⟨hxA, hxIcc⟩
        rw [mem_Icc] at hxIcc
        exact ⟨hxA, by rw [mem_Iic]; omega⟩
      have : (A ∩ Icc 1 N).ncard ≤ B_set.ncard := ncard_le_ncard h_sub hB_fin
      exact_mod_cast this
    have hBB_le : (↑(B + B).card : ℝ) ≤ s + 1 := by
      have h_eq : (B + B).card = (B_set + B_set).ncard := by
        rw [← ncard_coe_finset, Finset.coe_add, Finite.coe_toFinset]
      rw [h_eq]
      dsimp only [s]
      have : (B_set + B_set).ncard ≤ ((A + A) ∩ Icc 1 (2 * N)).ncard + 1 :=
        ncard_sumset_Iic_le A N
      exact_mod_cast this
    have h_plu := nat_pluennecke_div B hB_nonempty h
    have h_div1 : (N + 1 - N₀ : ℝ) / (c + 1) ≤ (N + 1 - N₀ : ℝ) / ↑B.card := by
      have : 0 ≤ (N + 1 - N₀ : ℝ) := by linarith
      exact div_le_div_of_nonneg_left this hB_card_pos hB_le
    have h_div2 : (N + 1 - N₀ : ℝ) / ↑B.card ≤ (↑(h • B).card : ℝ) / ↑B.card :=
      div_le_div_of_nonneg_right h_card_le (by linarith)
    have h_div3 : ((↑(B + B).card : ℝ) / ↑B.card) ^ h ≤ ((s + 1) / c) ^ h := by
      have h1 : (↑(B + B).card : ℝ) / ↑B.card ≤ (s + 1) / ↑B.card :=
        div_le_div_of_nonneg_right hBB_le (by linarith)
      have h2 : (s + 1) / ↑B.card ≤ (s + 1) / c :=
        div_le_div_of_nonneg_left (by linarith) (by linarith) hB_ge
      have h_nonneg : 0 ≤ (↑(B + B).card : ℝ) / ↑B.card :=
        div_nonneg (Nat.cast_nonneg _) (by linarith)
      exact pow_le_pow_left₀ h_nonneg (h1.trans h2) h
    have h_chain : (N + 1 - N₀ : ℝ) / (c + 1) ≤ ((s + 1) / c) ^ h :=
      h_div1.trans (h_div2.trans (h_plu.trans h_div3))
    have h_pow_lt : (M + 1) ^ h < ((s + 1) / c) ^ h := hK_bound.trans_le h_chain
    have hs_c_pos : 0 ≤ (s + 1) / c := div_nonneg (by linarith) (by linarith)
    have h_M1_le : M + 1 ≤ (s + 1) / c :=
      le_of_pow_le_pow hs_c_pos h_h_ne h_pow_lt.le
    exact div_le_div_sub_one hc_pos h_M1_le

/--
Ruzsa and Turjányi do prove (under the same hypotheses) that
$$
\lim_{N\to \infty}\frac{\lvert (A+A+A)\cap \{1,\ldots,3N\}\rvert}
{\lvert A\cap \{1,\ldots,N\}\rvert}=\infty.
$$

This is weaker than `Erdos337.erdos_337.variants.ruzsa_turjanyi`: translating by a fixed
$a\in A$ with $1\leq a\leq N$ embeds $(A+A)\cap\{1,\ldots,2N\}$ into
$(A+A+A)\cap\{1,\ldots,3N\}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_337.variants.three_fold :
    ∀ A : Set ℕ, A.IsAsymptoticAddBasis →
      (fun N : ℕ ↦ ((A ∩ Icc 1 N).ncard : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) →
      Tendsto (fun N : ℕ ↦
          (((A + A + A) ∩ Icc 1 (3 * N)).ncard : ℝ) / ((A ∩ Icc 1 N).ncard : ℝ))
        atTop atTop := by
  intro A h_basis ho
  obtain ⟨h, hA⟩ := h_basis
  obtain ⟨a, haA, ha_pos⟩ := exists_pos_mem_of_basis hA
  refine tendsto_atTop_mono' _ ?_ (erdos_337.variants.ruzsa_turjanyi A ⟨h, hA⟩ ho)
  filter_upwards [eventually_ge_atTop a] with N hN
  have h_sub : (· + a) '' ((A + A) ∩ Icc 1 (2 * N)) ⊆ (A + A + A) ∩ Icc 1 (3 * N) := by
    rintro _ ⟨x, ⟨hx_mem, hx_Icc⟩, rfl⟩
    rw [mem_Icc] at hx_Icc
    show x + a ∈ (A + A + A) ∩ Icc 1 (3 * N)
    exact ⟨add_mem_add hx_mem haA, by rw [mem_Icc]; omega⟩
  have h_fin : ((A + A + A) ∩ Icc 1 (3 * N)).Finite := (finite_Icc 1 (3 * N)).inter_of_right _
  have h_card : ((A + A) ∩ Icc 1 (2 * N)).ncard ≤ ((A + A + A) ∩ Icc 1 (3 * N)).ncard := by
    have h_le := ncard_le_ncard h_sub h_fin
    rwa [ncard_image_of_injective _ (add_left_injective a)] at h_le
  gcongr

end Erdos337
