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
# Erdős Problem 344

*References:*
- [erdosproblems.com/344](https://www.erdosproblems.com/344)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Er61b] Erdős, P., *On the representation of large integers as sums of distinct summands
  taken from a fixed set*. Acta Arith. (1961/62), 345-354.
- [Fo66] Folkman, J., *On the representation of integers as sums of distinct terms from a
  fixed sequence*. Canadian J. Math. 18 (1966), 643-655.
- [SzVu06] Szemerédi, E. and Vu, V., *Long arithmetic progressions in sumsets: thresholds and
  bounds*. J. Amer. Math. Soc. 19 (2006), 119-169.
- [SzVu06b] Szemerédi, E. and Vu, V., *Finite and infinite arithmetic progressions in sumsets*.
  Ann. of Math. 163 (2006), 1-35.
-/

@[expose] public section

open Filter

namespace Erdos344

/--
If $A\subseteq \mathbb{N}$ is a set of integers such that
$$\lvert A\cap \{1,\ldots,N\}\rvert\gg N^{1/2}$$
for all $N$ then must $A$ be subcomplete? That is, must
$$P(A) = \left\{\sum_{n\in B}n : B\subseteq A\textrm{ finite }\right\}$$
contain an infinite arithmetic progression?

This is true, and was proved by Szemerédi and Vu [SzVu06].

The implied constant is absolute, as in [SzVu06b, Corollary 1.4].
-/
@[category research solved, question, AMS 5 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos344.lean#L8994"]
theorem erdos_344 :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Set ℕ,
      (∀ᶠ N : ℕ in atTop, C * Real.sqrt N ≤ A.countUpTo N) → IsSubcomplete A := by
  sorry

/--
The stronger conjecture that this is true under
$$\lvert A\cap \{1,\ldots,N\}\rvert\geq (2N)^{1/2}$$
seems to be still open (this would be best possible as shown by [Er61b]).

The bound is required for all sufficiently large $N$: at $N=1$, it is impossible since
$\lvert A\cap\{1\}\rvert\leq 1<\sqrt{2}$.
-/
@[category research open, question, AMS 5 11]
theorem erdos_344.variants.sqrt_two :
    ∀ A : Set ℕ, (∀ᶠ N : ℕ in atTop, Real.sqrt (2 * N) ≤ A.countUpTo N) →
      IsSubcomplete A := by
  sorry

/-- Folkman proved this under the stronger assumption that
$$\lvert A\cap \{1,\ldots,N\}\rvert\gg N^{1/2+\epsilon}$$
for some $\epsilon>0$ [Fo66]. -/
@[category research solved, AMS 5 11]
theorem erdos_344.variants.folkman :
    ∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c → ∀ A : Set ℕ,
      (∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤ A.countUpTo N) →
      IsSubcomplete A := by
  obtain ⟨C, _, h⟩ := erdos_344
  intro ε hε c hc A hA
  refine h A ?_
  have hpow : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  filter_upwards [hA, hpow.eventually_ge_atTop (C / c)] with N hN hNe
  have hsplit : (N : ℝ) ^ ((1 : ℝ) / 2 + ε) = Real.sqrt N * (N : ℝ) ^ ε := by
    rw [Real.rpow_add' (Nat.cast_nonneg N) (by positivity), Real.sqrt_eq_rpow]
  calc C * Real.sqrt N = c * (C / c) * Real.sqrt N := by field_simp
    _ ≤ c * (N : ℝ) ^ ε * Real.sqrt N := by gcongr
    _ = c * (N : ℝ) ^ ((1 : ℝ) / 2 + ε) := by rw [hsplit]; ring
    _ ≤ A.countUpTo N := hN

@[category test, AMS 5 11]
theorem univ_density (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C * Real.sqrt N ≤ (Set.univ : Set ℕ).countUpTo N := by
  have hlim : Tendsto (fun N : ℕ ↦ Real.sqrt N) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_ge_atTop C] with N hN
  have hc : (Set.univ : Set ℕ).countUpTo N = N := by simp [Set.countUpTo]
  rw [hc]
  calc C * Real.sqrt N ≤ Real.sqrt N * Real.sqrt N := by gcongr
    _ = N := Real.mul_self_sqrt (Nat.cast_nonneg N)

end Erdos344
