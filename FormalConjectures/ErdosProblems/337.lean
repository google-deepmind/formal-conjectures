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

/-- The $h$-fold sumset $hA=\{a_1+\cdots+a_h : a_1,\ldots,a_h\in A\}$. -/
def sumsetOfOrder (A : Set ℕ) (h : ℕ) : Set ℕ :=
  {n | ∃ f : Fin h → ℕ, (∀ i, f i ∈ A) ∧ ∑ i, f i = n}

/-- `sumsetOfOrder A 2` is the sumset `A + A`. -/
@[category API, AMS 5 11]
theorem sumsetOfOrder_two (A : Set ℕ) : sumsetOfOrder A 2 = A + A := by
  sorry

/--
Let $A\subseteq \mathbb{N}$ be an additive basis (of any finite order) such that
$\lvert A\cap \{1,\ldots,N\}\rvert=o(N)$. Is it true that
\[
\lim_{N\to \infty}\frac{\lvert (A+A)\cap \{1,\ldots,N\}\rvert}
{\lvert A\cap \{1,\ldots,N\}\rvert}=\infty?
\]

The answer is no, and a counterexample was provided by Turjányi [Tu84]. This was generalised (to
the replacement of $A+A$ by the $h$-fold sumset $hA$ for any $h\geq 2$) by Ruzsa and Turjányi
[RT85].
-/
@[category research solved, AMS 5 11]
theorem erdos_337 : answer(False) ↔
    ∀ A : Set ℕ, A.IsAddBasis →
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
    ∃ A : Set ℕ, A.IsAddBasis ∧
      (fun N : ℕ ↦ ((A ∩ Icc 1 N).ncard : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) ∧
      ¬ Tendsto (fun N : ℕ ↦
          ((sumsetOfOrder A h ∩ Icc 1 N).ncard : ℝ) / ((A ∩ Icc 1 N).ncard : ℝ))
        atTop atTop := by
  sorry

/--
Ruzsa and Turjányi do prove (under the same hypotheses) that
\[
\lim_{N\to \infty}\frac{\lvert (A+A+A)\cap \{1,\ldots,3N\}\rvert}
{\lvert A\cap \{1,\ldots,N\}\rvert}=\infty,
\]
-/
@[category research solved, AMS 5 11]
theorem erdos_337.variants.three_fold :
    ∀ A : Set ℕ, A.IsAddBasis →
      (fun N : ℕ ↦ ((A ∩ Icc 1 N).ncard : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) →
      Tendsto (fun N : ℕ ↦
          (((A + A + A) ∩ Icc 1 (3 * N)).ncard : ℝ) / ((A ∩ Icc 1 N).ncard : ℝ))
        atTop atTop := by
  sorry

/--
Ruzsa and Turjányi do prove (under the same hypotheses) that
\[
\lim_{N\to \infty}\frac{\lvert (A+A+A)\cap \{1,\ldots,3N\}\rvert}
{\lvert A\cap \{1,\ldots,N\}\rvert}=\infty,
\]
and conjecture that the same should be true with $(A+A)\cap \{1,\ldots,2N\}$ in the numerator.
-/
@[category research open, AMS 5 11]
theorem erdos_337.variants.ruzsa_turjanyi :
    ∀ A : Set ℕ, A.IsAddBasis →
      (fun N : ℕ ↦ ((A ∩ Icc 1 N).ncard : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) →
      Tendsto (fun N : ℕ ↦
          (((A + A) ∩ Icc 1 (2 * N)).ncard : ℝ) / ((A ∩ Icc 1 N).ncard : ℝ))
        atTop atTop := by
  sorry

end Erdos337
