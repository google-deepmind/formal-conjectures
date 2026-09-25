/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 30

*References:*
- [erdosproblems.com/30](https://www.erdosproblems.com/30)
- [ErTu41] Erdős, P. and Turán, P., *On a problem of Sidon in additive number theory, and on
  some related problems*. J. London Math. Soc. 16 (1941), 212-215.
- [Li69] Lindström, B., *An inequality for $B_2$-sequences*. J. Combinatorial Theory 6 (1969),
  211-212.
- [Si38] Singer, J., *A theorem in finite projective geometry and some applications to number
  theory*. Trans. Amer. Math. Soc. 43 (1938), 377-385.
- [BFR23] Balogh, J., Füredi, Z. and Roy, S., *An upper bound on the size of Sidon sets*.
  Amer. Math. Monthly 130 (2023), 437-445.
- [OB22] O'Bryant, K., *On the size of finite Sidon sets*.
  [arXiv:2207.07800](https://arxiv.org/abs/2207.07800) (2022).
- [CHO25] Carter, D., Hunter, Z. and O'Bryant, K., *On the diameter of finite Sidon sets*.
  Acta Math. Hungar. 175 (2025), 108-126.

See also [Ben Green's Open Problem 31](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf)
(formalised in `FormalConjectures/GreensOpenProblems/31.lean`).
-/

@[expose] public section

namespace Erdos30

/--
Let $h(N)$ be the maximum size of a Sidon set in $\{1, \dots, N\}$.
-/
noncomputable abbrev h (N : ℕ) : ℕ := Finset.maxSidonSubsetCard (Finset.Icc 1 N)


open Filter
open scoped Asymptotics

/--
Is it true that, for every $\varepsilon > 0$, $h(N) = \sqrt N + O_{\varepsilon}(N^\varepsilon)$
-/
@[category research open, AMS 11]
theorem erdos_30 : answer(sorry) ↔
    ∀ᵉ (ε > 0), (fun N => h N - (N : Real).sqrt) =O[atTop] fun N => (N : ℝ)^(ε : ℝ) := by
  sorry

/--
A stronger conjecture: is it true that $h(N) = \sqrt N + O(1)$?
Erdős thought this was perhaps too optimistic.
-/
@[category research open, AMS 11]
theorem erdos_30.variants.O_one : answer(sorry) ↔
    (fun N => h N - (N : ℝ).sqrt) =O[atTop] fun _ => (1 : ℝ) := by
  sorry

/--
Erdős and Turán [ErTu41] proved $h(N) \le \sqrt N + O(N^{1/4})$.
-/
@[category research solved, AMS 11]
theorem erdos_30.variants.erdos_turan :
    (fun N => h N - (N : ℝ).sqrt) =O[atTop] fun N => (N : ℝ) ^ (4⁻¹ : ℝ) := by
  sorry

/--
The proofs of Erdős–Turán [ErTu41] and Lindström [Li69] in fact give, for all $N$,
$h(N) \le N^{1/2} + N^{1/4} + 1$.
-/
@[category research solved, AMS 11]
theorem erdos_30.variants.lindstrom (N : ℕ) :
    (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 := by
  sorry

/--
Balogh, Füredi and Roy [BFR23] proved $h(N) \le N^{1/2} + 0.998 N^{1/4}$ for all sufficiently
large $N$.
-/
@[category research solved, AMS 11]
theorem erdos_30.variants.balogh_furedi_roy :
    ∀ᶠ N in atTop, (h N : ℝ) ≤ (N : ℝ).sqrt + (0.998 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  sorry

/--
O'Bryant [OB22] proved $h(N) \le N^{1/2} + 0.99703 N^{1/4}$ for all sufficiently large $N$.
-/
@[category research solved, AMS 11]
theorem erdos_30.variants.obryant :
    ∀ᶠ N in atTop, (h N : ℝ) ≤ (N : ℝ).sqrt + (0.99703 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  sorry

/--
Carter, Hunter and O'Bryant [CHO25] proved $h(N) \le N^{1/2} + 0.98183 N^{1/4} + O(1)$.
This is the current record upper bound.
-/
@[category research solved, AMS 11]
theorem erdos_30.variants.carter_hunter_obryant :
    ∃ C : ℝ, ∀ᶠ N in atTop,
      (h N : ℝ) ≤ (N : ℝ).sqrt + (0.98183 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) + C := by
  sorry

/--
Singer's construction [Si38] shows $h(N) \ge (1 - o(1)) N^{1/2}$ for all $N$.
-/
@[category research solved, AMS 11]
theorem erdos_30.variants.singer :
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, (1 - ε) * (N : ℝ).sqrt ≤ h N := by
  sorry

/--
Combining Singer's lower bound [Si38] with the Erdős–Turán upper bound [ErTu41]:
$h(N) \sim N^{1/2}$.
-/
@[category research solved, AMS 11]
theorem erdos_30.variants.isEquivalent_sqrt :
    (fun N => (h N : ℝ)) ~[atTop] fun N => (N : ℝ).sqrt := by
  sorry

end Erdos30
