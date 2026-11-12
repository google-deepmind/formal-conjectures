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
# Erdős Problem 840

*References:*
- [erdosproblems.com/840](https://www.erdosproblems.com/840)
- [Er81h] Erdős, P., *Some problems and results on additive and multiplicative number theory*.
  Analytic number theory (Philadelphia, Pa., 1980), Lecture Notes in Math. 899 (1981), 171-182.
  [PDF](https://www.renyi.hu/~p_erdos/1981-33.pdf)
- [ErFr91] Erdős, P. and Freud, R., *On sums of a Sidon-sequence*. J. Number Theory 38 (1991),
  196-205.
- [Pi06] Pikhurko, O., *Dense edge-magic graphs and thin additive bases*. Discrete Math. 306
  (2006), 2097-2107.
-/

@[expose] public section

open Filter Asymptotics
open scoped Finset Pointwise

namespace Erdos840

/-- The constant $c$ is attained by quasi-Sidon sets: there are sets
$A_N \subseteq \{1, \ldots, N\}$ with $\lvert A_N\rvert = (1+o(1))cN^{1/2}$ and
$\lvert A_N+A_N\rvert=(1+o(1))\binom{\lvert A_N\rvert}{2}$ as $N \to \infty$. -/
def IsQuasiSidonConstant (c : ℝ) : Prop :=
  ∃ A : ℕ → Finset ℕ, (∀ N, A N ⊆ Finset.Icc 1 N) ∧
    (fun N ↦ (#(A N) : ℝ)) ~[atTop] (fun N ↦ c * Real.sqrt N) ∧
    (fun N ↦ (#(A N + A N) : ℝ)) ~[atTop] (fun N ↦ ((#(A N)).choose 2 : ℝ))

/-- The constant $0$ is attained by the empty sets, so the set of attained constants is
nonempty. -/
@[category test, AMS 5 11]
theorem isQuasiSidonConstant_zero : IsQuasiSidonConstant 0 := by
  refine ⟨fun _ ↦ ∅, fun _ ↦ Finset.empty_subset _, ?_, ?_⟩
  · simpa using (IsEquivalent.refl : (fun _ : ℕ ↦ (0 : ℝ)) ~[atTop] fun _ ↦ 0)
  · simpa using (IsEquivalent.refl : (fun _ : ℕ ↦ (0 : ℝ)) ~[atTop] fun _ ↦ 0)

def erdos_840.answer : ℝ := sorry

/--
Let $f(N)$ be the size of the largest quasi-Sidon subset $A\subset\{1,\ldots,N\}$, where we say
that $A$ is quasi-Sidon if
$$\lvert A+A\rvert=(1+o(1))\binom{\lvert A\rvert}{2}.$$
How does $f(N)$ grow?

Following [Er81h, p. 175], we ask for the largest $c$ such that there are quasi-Sidon sets
$A \subseteq \{1, \ldots, N\}$ with $\lvert A\rvert = (1+o(1))cN^{1/2}$.
-/
@[category research open, question value, AMS 5 11]
theorem erdos_840 : IsLUB {c : ℝ | IsQuasiSidonConstant c} erdos_840.answer := by
  sorry

/--
Erdős and Freud [ErFr91] proved
$$\left(\frac{2}{\sqrt{3}}+o(1)\right)N^{1/2} \leq f(N) \leq \left(2+o(1)\right)N^{1/2}.$$
(Although both bounds were already given by Erdős in [Er81h].)

This is the lower bound. The lower bound is taking a genuine Sidon set $B\subset [1,N/3]$ of size
$\sim N^{1/2}/\sqrt{3}$ and taking the union with $\{N-b : b\in B\}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_840.variants.erdos_freud_lower : IsQuasiSidonConstant (2 / Real.sqrt 3) := by
  sorry

/--
Erdős and Freud [ErFr91] proved
$$\left(\frac{2}{\sqrt{3}}+o(1)\right)N^{1/2} \leq f(N) \leq \left(2+o(1)\right)N^{1/2}.$$
(Although both bounds were already given by Erdős in [Er81h].)

This is the upper bound.
-/
@[category research solved, AMS 5 11]
theorem erdos_840.variants.erdos_freud_upper (c : ℝ) (hc : IsQuasiSidonConstant c) : c ≤ 2 := by
  by_contra! hlt
  have hc0 : 0 < c := by linarith
  obtain ⟨A, hAsub, hk, hs⟩ := hc
  -- $cN^{1/2} \to \infty$, so the constant $1$ is negligible: $|A_N| - 1 \sim cN^{1/2}$.
  have hsqrt : Tendsto (fun N : ℕ ↦ c * Real.sqrt N) atTop atTop :=
    Tendsto.const_mul_atTop hc0 (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hk1 := hk.sub_isLittleO (w := fun _ ↦ (1 : ℝ))
    (isLittleO_const_left.2 (Or.inr (tendsto_norm_atTop_atTop.comp hsqrt)))
  -- $\binom{|A_N|}{2} = |A_N|(|A_N|-1)/2 \sim (cN^{1/2})^2/2$.
  have hC := ((hk.mul hk1).div (IsEquivalent.refl (u := fun _ : ℕ ↦ (2 : ℝ)))).congr_left
    (w := fun N ↦ ((#(A N)).choose 2 : ℝ))
    (Eventually.of_forall fun N ↦ by simp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply,
      Nat.cast_choose_two])
  -- Hence $|A_N + A_N|/N \to c^2/2$.
  have hlim : Tendsto (fun N : ℕ ↦ (#(A N + A N) : ℝ) / N) atTop (nhds (c ^ 2 / 2)) := by
    refine (((hs.trans hC).div (IsEquivalent.refl (u := fun N : ℕ ↦ (N : ℝ)))).congr_right
      (w := fun _ ↦ c ^ 2 / 2) ?_).tendsto_const
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
    simp only [Pi.mul_apply, Pi.div_apply]
    rw [show c * Real.sqrt N * (c * Real.sqrt N) = c ^ 2 * (Real.sqrt N * Real.sqrt N) by ring,
      hsq]
    field_simp
  -- But $A_N + A_N \subseteq [2, 2N]$, so $|A_N + A_N|/N \leq 2$.
  have hbound : ∀ᶠ N : ℕ in atTop, (#(A N + A N) : ℝ) / N ≤ 2 := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hsub : A N + A N ⊆ Finset.Icc 2 (2 * N) := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 hx
      have ha' := Finset.mem_Icc.1 (hAsub N ha)
      have hb' := Finset.mem_Icc.1 (hAsub N hb)
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have hcard : #(A N + A N) ≤ 2 * N := by
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this
      omega
    rw [div_le_iff₀ (by exact_mod_cast hN)]
    exact_mod_cast hcard
  have := le_of_tendsto hlim hbound
  nlinarith

/--
The upper bound was improved by Pikhurko [Pi06] to
$$f(N) \leq \left(\left(\frac{1}{4}+\frac{1}{(\pi+2)^2}\right)^{-1/2}+o(1)\right)N^{1/2}$$
(the constant here is $=1.863\cdots$).
-/
@[category research solved, AMS 5 11]
theorem erdos_840.variants.pikhurko (c : ℝ) (hc : IsQuasiSidonConstant c) :
    c ≤ (1 / 4 + 1 / (Real.pi + 2) ^ 2) ^ (-(1 : ℝ) / 2) := by
  sorry

end Erdos840
