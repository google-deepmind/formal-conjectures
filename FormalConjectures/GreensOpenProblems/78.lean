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
# Ben Green's Open Problem 78

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.78)
- [JT20] Jing, Y. and Tran, C.-M., *Minimal and nearly minimal measure expansions in connected
  unimodular groups*. [arXiv:2006.01824](https://arxiv.org/abs/2006.01824)
- [JTZ23] Jing, Y., Tran, C.-M. and Zhang, R., *Measure doubling of small sets in
  $SO(3,\mathbb{R})$*. [arXiv:2304.09619](https://arxiv.org/abs/2304.09619)
-/

@[expose] public section

open MeasureTheory Pointwise

namespace Green78

/-- The rotation group $SO(3)$, as the group of real $3 \times 3$ orthogonal matrices of
determinant $1$, with the subspace topology from the matrices. -/
abbrev SO3 := ↥(Matrix.specialOrthogonalGroup (Fin 3) ℝ)

/--
Let $\varepsilon > 0$. Suppose $A \subset SO(3)$ is open and has sufficiently small (in terms of
$\varepsilon$) normalised Haar measure. Is $\mu(A \cdot A) \geqslant (4 - \varepsilon)\mu(A)$?

Reading: $\mu$ is any probability measure on $SO(3)$ invariant under left multiplication. Since
$SO(3)$ is compact, this is the normalised Haar measure, and it is unique. "Sufficiently small"
is $\mu(A) < \delta$ with $\delta$ depending only on $\varepsilon$. The answer is yes
[JTZ23, Theorem 1.1].

The Borel $\sigma$-algebra of `SO3` is taken as an instance argument (`MeasurableSpace` with
`BorelSpace`), since Mathlib has no measurable space instance for this subtype.
-/
@[category research solved, question, AMS 20 22 28]
theorem green_78 [MeasurableSpace SO3] [BorelSpace SO3] (μ : Measure SO3)
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ A : Set SO3, IsOpen A → μ.real A < δ →
      (4 - ε) * μ.real A ≤ μ.real (A * A) := by
  sorry

/--
**Jing--Tran.** [JT20, Theorem 1.3] states that there is a constant $\eta \ge 10^{-12}$ such that
for every $d > 0$ there is $C > 0$ depending only on $d$ such that if $G$ is a connected compact
simple Lie group of dimension at most $d$ and $A \subset G$ is compact with $0 < \mu_G(A) < C$,
then $\mu_G(A^2) > (2 + \eta)\mu_G(A)$. We state the case $G = SO(3)$ (connected, compact,
simple, of dimension $3$). For open sets it is superseded by `green_78`.
-/
@[category research solved, AMS 20 22 28]
theorem green_78.variants.jing_tran [MeasurableSpace SO3] [BorelSpace SO3] (μ : Measure SO3)
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] :
    ∃ η : ℝ, 10 ^ (-12 : ℤ) ≤ η ∧ ∃ C : ℝ, 0 < C ∧ ∀ A : Set SO3, IsCompact A →
      0 < μ.real A → μ.real A < C → (2 + η) * μ.real A < μ.real (A * A) := by
  sorry

/--
**Strong Breuillard--Green conjecture** [JTZ23, Conjecture 1.3]: if $A \subset SO(3)$ is open
then $\mu(A^2) \ge \min\{1, 4\mu(A)(1 - \mu(A))\}$. The conjecture in [JTZ23] also describes the
sets for which equality holds; only the inequality is stated here.
-/
@[category research open, AMS 20 22 28]
theorem green_78.variants.strong_breuillard_green [MeasurableSpace SO3] [BorelSpace SO3]
    (μ : Measure SO3) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] :
    ∀ A : Set SO3, IsOpen A →
      min 1 (4 * μ.real A * (1 - μ.real A)) ≤ μ.real (A * A) := by
  sorry

end Green78
