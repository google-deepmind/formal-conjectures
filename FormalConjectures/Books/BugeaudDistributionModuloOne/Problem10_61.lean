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
# Bugeaud Collection of Conjectures and Open Questions: Pisot orbits on the Cantor set

Problem 10.61, proposed by Mendès France [MF67, Problème 1, p. 41]. For a Pisot number
$\alpha > 2$ put
$$C(\alpha) = \left\{ (\alpha - 1) \sum_{k \ge 1} \varepsilon_k \alpha^{-k} :
\varepsilon_k \in \{0, 1\} \right\}.$$
The problem asks to prove that $(\xi \alpha^n)_{n \ge 1}$ is not uniformly distributed
modulo one for any $\xi \in C(\alpha)$. In the language of [MF67] this reads
$C(\alpha) \cap B(\alpha) = \emptyset$, where $B(\alpha)$ is the set of $\xi$ for which
$(\xi \alpha^n)$ is uniformly distributed modulo one.

The problem is open. It is easy for an integer base and settled for two quadratic
$\alpha$; the general Pisot case is what remains. [Ste26] reduces it to a statement about
shift-invariant measures of the full two-shift, and proves that every true instance admits
a finite certificate, so the difficulty is uniformity in $\alpha$ rather than any single
$\alpha$. The variants below state the criterion and the instances of [Ste26] that concern
Problem 10.61 directly; the reduction itself is not stated here, since it needs the symbolic
model.

Deleting the term $n = 0$ does not change uniform distribution modulo one, so the
statements indexed from $n = 1$ agree with the ones of [Ste26], which are indexed from
$n = 0$. Where an orbit is confined away from an interval the stronger form, for every
$n \ge 0$, is stated.

*References:*
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10, Problem 10.61, p. 222.
  - [MF67] Mendès France, Michel. "Nombres normaux. Applications aux fonctions
    pseudo-aléatoires." Journal d'Analyse Mathématique 20 (1967): 1-56.
  - [Kok35] Koksma, Jurjen F. "Ein mengentheoretischer Satz über die Gleichverteilung
    modulo Eins." Compositio Mathematica 2 (1935): 250-258.
  - [Ste26] Stephan, Ralf. "Criteria for the non-equidistribution of $(\xi \alpha^n)$ on
    the Cantor set $C(\alpha)$." Preprint, 2026.
    https://doi.org/10.13140/RG.2.2.13923.52001
-/

namespace Bugeaud61

/--
The point of $C(\alpha)$ with digit sequence $\varepsilon$, that is
$(\alpha - 1) \sum_{k \ge 1} \varepsilon_k \alpha^{-k}$.
-/
noncomputable def cantorPoint (α : ℝ) (ε : ℕ → Bool) : ℝ :=
  (α - 1) * ∑' k : ℕ, (if ε k then (1 : ℝ) else 0) * α⁻¹ ^ (k + 1)

/--
The set $C(\alpha)$ of Problem 10.61. For $\alpha > 2$ it is a Cantor set of Hausdorff
dimension $\log 2 / \log \alpha < 1$, normalised so that $0$ is its least and $1$ its
greatest element.
-/
noncomputable def pisotCantorSet (α : ℝ) : Set ℝ := Set.range (cantorPoint α)

/--
The Route A exponent $A(\alpha) = \log 2 / \log \alpha + \log 2 / \log(1 / \rho)$ of
[Ste26], where $\rho$ is the largest modulus of a conjugate of $\alpha$ other than
$\alpha$ itself. It is the sum of the box dimensions of $C(\alpha)$ and of the window in
which the conjugate contributions live.
-/
noncomputable def routeAExponent (α ρ : ℝ) : ℝ :=
  Real.log 2 / Real.log α + Real.log 2 / Real.log ρ⁻¹

/--
Problem 10.61. Let $\alpha > 2$ be a Pisot number. For every $\xi \in C(\alpha)$ the
sequence $(\xi \alpha^n)_{n \ge 1}$ is not uniformly distributed modulo one.
-/
@[category research open, AMS 11 37]
theorem problem_10_61 (α : ℝ) (hα : IsPisot α) (hα2 : 2 < α) :
    ∀ ξ ∈ pisotCantorSet α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1) := by
  sorry

/--
The hypothesis $\xi \in C(\alpha)$ cannot be dropped: by Koksma's metric theorem [Kok35],
for a fixed $\alpha > 1$ the sequence $(\xi \alpha^n)_{n \ge 1}$ is uniformly distributed
modulo one for Lebesgue-almost every $\xi$. Problem 10.61 asks a null set of starting
points to defeat an almost-everywhere law.
-/
@[category research solved, AMS 11 37]
theorem problem_10_61.variants.almost_every (α : ℝ) (hα : 1 < α) :
    ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1) := by
  sorry

/--
The covering criterion, [Ste26, Theorem C(i)], at a quadratic setup: $\alpha > 1$ is a root
of $X^2 - aX - b$ whose conjugate $\beta = a - \alpha$ is non-zero of modulus less than
one. If the Route A exponent $A(\alpha)$ formed from $\alpha$ and $\rho = |\beta|$ is
below $1$, then Problem 10.61 holds at $\alpha$.

[Ste26] states the criterion for a Pisot number of any degree $d \ge 2$, but proves it only
in this degree-two case.
-/
@[category research solved, AMS 11 37]
theorem problem_10_61.variants.covering_criterion {a b : ℤ} {α : ℝ}
    (hroot : α ^ 2 = a * α + b) (hα : 1 < α) (hβ : (a : ℝ) - α ≠ 0)
    (hconj : |(a : ℝ) - α| < 1) (hA : routeAExponent α |(a : ℝ) - α| < 1) :
    ∀ ξ ∈ pisotCantorSet α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1) := by
  sorry

/--
The exact range of the covering criterion, [Ste26, Theorem C(ii)]: at a quadratic setup of
norm $-b$ one has $A(\alpha) < 1$ if and only if
$(\log_2 \alpha - 1)(\log_2(\alpha / |b|) - 1) > 1$, which for units reads $\alpha > 4$.
The criterion therefore never reaches the slice $2 < \alpha \le 4$, and says nothing about
a quadratic $\alpha$ with $A(\alpha) \ge 1$.
-/
@[category research solved, AMS 11 37]
theorem problem_10_61.variants.covering_criterion_range {a b : ℤ} {α : ℝ}
    (hroot : α ^ 2 = a * α + b) (hα : 1 < α) (hconj : |(a : ℝ) - α| < 1) (hb : b ≠ 0) :
    routeAExponent α |(a : ℝ) - α| < 1 ↔
      1 < (Real.logb 2 α - 1) * (Real.logb 2 α - Real.logb 2 |(b : ℝ)| - 1) := by
  sorry

/--
[Ste26, Theorem D] at $\alpha = 2 + \sqrt 5$, the smallest $\alpha$ the covering criterion
reaches: Problem 10.61 holds there in the strong form. There is one open interval
$J \subseteq (0, 1)$, the same for every $\xi \in C(\alpha)$ and every $n \ge 0$, that
$\{\xi \alpha^n\}$ misses.
-/
@[category research solved, AMS 11 37]
theorem problem_10_61.variants.two_add_sqrt_five :
    ∃ x r : ℝ, 0 < r ∧ Set.Ioo (x - r) (x + r) ⊆ Set.Ioo 0 1 ∧
      ∀ ξ ∈ pisotCantorSet (2 + Real.sqrt 5), ∀ n : ℕ,
        Int.fract (ξ * (2 + Real.sqrt 5) ^ n) ∉ Set.Ioo (x - r) (x + r) := by
  sorry

/--
[Ste26, Theorem D] at $\alpha = 2 + \sqrt 3$: Problem 10.61 holds there, by a
confinement-gap certificate in exact $\mathbb{Z}[\sqrt 3]$ arithmetic. This $\alpha$ lies
in the slice $2 < \alpha \le 4$, which the covering criterion does not reach.
-/
@[category research solved, AMS 11 37]
theorem problem_10_61.variants.two_add_sqrt_three :
    ∀ ξ ∈ pisotCantorSet (2 + Real.sqrt 3),
      ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * (2 + Real.sqrt 3) ^ (n + 1) := by
  sorry

/--
Sanity check: $0 \in C(\alpha)$, the point with all digits zero.
-/
@[category test, AMS 11 37]
theorem zero_mem_pisotCantorSet (α : ℝ) : 0 ∈ pisotCantorSet α :=
  ⟨fun _ => false, by simp [cantorPoint]⟩

/--
Sanity check: $1 \in C(\alpha)$ for $\alpha > 1$, the point with all digits one, since
$\sum_{k \ge 1} \alpha^{-k} = 1 / (\alpha - 1)$.
-/
@[category test, AMS 11 37]
theorem one_mem_pisotCantorSet {α : ℝ} (hα : 1 < α) : 1 ∈ pisotCantorSet α := by
  have hα0 : (0 : ℝ) < α := zero_lt_one.trans hα
  have hinv : α⁻¹ < 1 := inv_lt_one_of_one_lt₀ hα
  refine ⟨fun _ => true, ?_⟩
  have hsum : ∑' k : ℕ, (if (fun _ : ℕ => true) k then (1 : ℝ) else 0) * α⁻¹ ^ (k + 1)
      = α⁻¹ * (1 - α⁻¹)⁻¹ := by
    simp only [if_true, one_mul, pow_succ']
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hinv]
  rw [cantorPoint, hsum]
  have h1 : α - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hα)
  field_simp

end Bugeaud61
