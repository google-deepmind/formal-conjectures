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
public import FormalConjectures.ErdosProblems.«214»

/-!
# Erdős Problem 232

*References:*
- [erdosproblems.com/232](https://www.erdosproblems.com/232)
- [ACMVZ23] Ambrus, Gergely and Csiszárik, Adrián and Matolcsi, Máté and Varga, Dániel and
  Zsámboki, Pál, *The density of planar sets avoiding unit distances*. Math. Program. (2023),
  [arXiv:2207.14179](https://arxiv.org/abs/2207.14179).
- [Cr67] Croft, H. T., *Incidence incidents*. Eureka (1967), 22-26.
- [Er85] Erdős, Paul, *Problems and results in combinatorial geometry*. Discrete geometry and
  convexity (New York, 1982), Ann. New York Acad. Sci. 440 (1985), 1-11.
  [PDF](https://www.renyi.hu/~p_erdos/1985-23.pdf)
- [Mo66] Moser, L., *Poorly formulated unsolved problems of combinatorial geometry*.
  Mimeographed (1966).
-/

@[expose] public section

open Filter MeasureTheory
open scoped EuclideanGeometry

namespace Erdos232

/-- The proportion $\lambda(A \cap B_R) / \lambda(B_R)$ of the open ball $B_R$ of radius `R`
centred at the origin that is occupied by `A`. For `R ≤ 0` the ball is empty and the quotient is
`0`; this plays no role for the limit $R \to \infty$. -/
noncomputable def ballDensity (A : Set ℝ²) (R : ℝ) : ℝ :=
  (volume (A ∩ Metric.ball 0 R)).toReal / (volume (Metric.ball (0 : ℝ²) R)).toReal

/-- The upper density $\overline{\delta}(A) = \limsup_{R \to \infty} \lambda(A \cap B_R) /
\lambda(B_R)$, with balls centred at the origin (the upper density does not depend on the
centre). The quotients lie in $[0, 1]$, so this is the genuine limsup. -/
noncomputable def upperDensity (A : Set ℝ²) : ℝ :=
  limsup (ballDensity A) atTop

/-- $m_1 = \sup \overline{\delta}(A)$, where $A$ ranges over the Lebesgue measurable subsets of
$\mathbb{R}^2$ without two points at distance $1$. The set of densities is nonempty (take
$A = \emptyset$) and bounded above by $1$, so `sSup` is the genuine supremum. -/
noncomputable def m₁ : ℝ :=
  sSup {d : ℝ | ∃ A : Set ℝ², NullMeasurableSet A volume ∧
    Erdos214.UnitDistanceAvoiding A ∧ upperDensity A = d}

/--
For $A\subset \mathbb{R}^2$ we define the upper density as
$$\overline{\delta}(A)=\limsup_{R\to \infty}\frac{\lambda(A \cap B_R)}{\lambda(B_R)},$$
where $\lambda$ is the Lebesgue measure and $B_R$ is the ball of radius $R$.

Estimate
$$m_1=\sup \overline{\delta}(A),$$
where $A$ ranges over all measurable subsets of $\mathbb{R}^2$ without two points distance $1$
apart. In particular, is $m_1\leq 1/4$?

A question of Moser [Mo66]; Erdős [Er85] conjectured $m_1<1/4$. The answer is yes: Ambrus,
Csiszárik, Matolcsi, Varga, and Zsámboki [ACMVZ23] proved that $m_1\leq 0.247$.
-/
@[category research solved, question, AMS 28 52, formal_proof using lean4 at
    "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos232.lean#L125"]
theorem erdos_232 : m₁ ≤ 1 / 4 := by
  sorry

/--
Ambrus, Csiszárik, Matolcsi, Varga, and Zsámboki [ACMVZ23, Theorem 1]: any Lebesgue measurable,
$1$-avoiding planar set has upper density at most $0.2470$.
-/
@[category research solved, AMS 28 52, formal_proof using lean4 at
    "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos232.lean#L90"]
theorem erdos_232.variants.acmvz_set (A : Set ℝ²) (hA : NullMeasurableSet A volume)
    (hfree : Erdos214.UnitDistanceAvoiding A) : upperDensity A ≤ 247 / 1000 := by
  sorry

/--
Ambrus, Csiszárik, Matolcsi, Varga, and Zsámboki [ACMVZ23] proved that $m_1\leq 0.247$.
-/
@[category research solved, AMS 28 52, formal_proof using lean4 at
    "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos232.lean#L115"]
theorem erdos_232.variants.acmvz : m₁ ≤ 247 / 1000 := by
  sorry

/--
A lower bound of $m_1\geq \pi/(8\sqrt{3})\approx 0.2267$ is given by taking the union of open
circular discs of radius $1/2$ at a regular hexagonal lattice suitably spaced apart
(see [ACMVZ23, Section 1]).
-/
@[category research solved, AMS 28 52]
theorem erdos_232.variants.hexagonal_lower_bound :
    Real.pi / (8 * Real.sqrt 3) ≤ m₁ := by
  sorry

/--
Croft [Cr67] gives a small improvement of $m_1\geq 0.22936$ (see [ACMVZ23, Section 1]).
-/
@[category research solved, AMS 28 52]
theorem erdos_232.variants.croft_lower_bound : 0.22936 ≤ m₁ := by
  sorry

end Erdos232
