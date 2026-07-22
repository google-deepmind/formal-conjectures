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
# Erdős Problem 1190

*References:*
- [erdosproblems.com/1190](https://www.erdosproblems.com/1190)
- [BFV13] de la Bretèche, Régis and Ford, Kevin and Vandehey, Joseph, *On non-intersecting
  arithmetic progressions*. Acta Arith. (2013), 381-392.
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
-/

open Filter Real

open scoped Topology

namespace Erdos1190

/--
$\epsilon_m$ is the supremum of $\sum \frac{1}{n_i}$ over all finite sequences
$m<n_1<\cdots<n_k$ for which there exist congruences $a_i\pmod{n_i}$ such that no integer
satisfies two such congruences.
-/
noncomputable def eps (m : ℕ) : ℝ :=
  sSup {s : ℝ | ∃ (S : Finset ℕ) (a : ℕ → ℤ), (∀ n ∈ S, m < n) ∧
    (∀ n ∈ S, ∀ n' ∈ S, n ≠ n' → ¬ ∃ x : ℤ, x ≡ a n [ZMOD n] ∧ x ≡ a n' [ZMOD n']) ∧
    (∑ n ∈ S, (n : ℝ)⁻¹) = s}

/-- $L(m)=\exp(\sqrt{\log m\log\log m})$. -/
noncomputable def L (m : ℕ) : ℝ := exp (sqrt (log (m : ℝ) * log (log (m : ℝ))))

/--
Let
\[\epsilon_m=\max \sum \frac{1}{n_i}\]
where the maximum is taken over all finite sequences $m<n_1<\cdots<n_k$ for which there exist
congruences $a_i\pmod{n_i}$ such that no integer satisfies two such congruences.

Estimate $\epsilon_m$.

The resolution of [202] by GPT-5.4 Pro implies via the same reduction that
\[\epsilon_m=L(m)^{-1+o(1)},\]
where $L(m)=\exp(\sqrt{\log m\log\log m})$.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1190.lean"]
theorem erdos_1190 : ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
    L m ^ (-1 - ε : ℝ) < eps m ∧ eps m < L m ^ (-1 + ε : ℝ) := by
  sorry

/--
Erdős [Er80] seems to credit Mirsky and Newman with the result that $\epsilon_m<1$, but gives no
reference.
-/
@[category research solved, AMS 5 11]
theorem erdos_1190.variants.lt_one (m : ℕ) (hm : 1 ≤ m) (S : Finset ℕ) (a : ℕ → ℤ)
    (hS : ∀ n ∈ S, m < n)
    (hdisj : ∀ n ∈ S, ∀ n' ∈ S, n ≠ n' → ¬ ∃ x : ℤ, x ≡ a n [ZMOD n] ∧ x ≡ a n' [ZMOD n']) :
    (∑ n ∈ S, (n : ℝ)⁻¹) < 1 := by
  sorry

/--
He could not even decide whether $\epsilon_m\to 0$ as $m\to \infty$.
-/
@[category research solved, AMS 5 11]
theorem erdos_1190.variants.tendsto_zero : Tendsto eps atTop (𝓝 0) := by
  sorry

/--
The work of de la Bretèche, Ford, and Vandehey [BFV13] implies
\[L(m)^{-1+o(1)}< \epsilon_m < L(m)^{-\sqrt{3}/2+o(1)},\]
where $L(m)=\exp(\sqrt{\log m\log\log m})$. The lower bound is implicit in their construction.
-/
@[category research solved, AMS 5 11]
theorem erdos_1190.variants.lower_bound : ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
    L m ^ (-1 - ε : ℝ) < eps m := by
  sorry

/--
The work of de la Bretèche, Ford, and Vandehey [BFV13] implies
\[L(m)^{-1+o(1)}< \epsilon_m < L(m)^{-\sqrt{3}/2+o(1)},\]
where $L(m)=\exp(\sqrt{\log m\log\log m})$. The upper bound follows immediately from their upper
bound as reported in [202] and partial summation.
-/
@[category research solved, AMS 5 11]
theorem erdos_1190.variants.upper_bound : ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
    eps m < L m ^ (-(sqrt 3 / 2) + ε : ℝ) := by
  sorry

end Erdos1190
