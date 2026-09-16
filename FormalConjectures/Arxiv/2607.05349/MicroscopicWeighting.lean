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
# The microscopic weighting on a metric space

*Reference:* [arxiv/2607.05349](https://arxiv.org/abs/2607.05349)
**The microscopic weighting on a metric space**
by *Emily Roff, Simon Willerton*
-/

open Filter Matrix

open scoped Topology

namespace Arxiv.«2607.05349»

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [MetricSpace X]

/-- The similarity matrix $Z(t)_{ij} = e^{-t \cdot d(x_i, x_j)}$ of a finite metric space. -/
noncomputable def similarityMatrix (X : Type*) [Fintype X] [MetricSpace X] (t : ℝ) :
    Matrix X X ℝ :=
  Matrix.of fun i j => Real.exp (-t * dist i j)

/-- The distance matrix $D_{ij} = d(x_i, x_j)$ of a finite metric space. -/
noncomputable def distanceMatrix (X : Type*) [Fintype X] [MetricSpace X] : Matrix X X ℝ :=
  Matrix.of fun i j => dist i j

/-- The weighting $\vec{w}(t) = Z(t)^{-1}\mathbf{1}$ at scale `t`.

`Matrix.inv` is `0` on singular matrices, so this is only the intended vector where `Z t` is
invertible. The analytic function `t ↦ det (Z t)` tends to `1` as `t → ∞`, so its zeros are
isolated. Hence `Z t` is invertible for all small enough `t > 0`, as required below. -/
noncomputable def weighting (X : Type*) [Fintype X] [DecidableEq X] [MetricSpace X] (t : ℝ) :
    X → ℝ :=
  (similarityMatrix X t)⁻¹ *ᵥ 1

/-- `X` admits a *microscopic weighting* when $\vec{w}(t)$ converges as $t \to 0^+$. -/
def HasMicroscopicWeighting (X : Type*) [Fintype X] [DecidableEq X] [MetricSpace X] : Prop :=
  ∃ w : X → ℝ, Tendsto (weighting X) (𝓝[>] 0) (𝓝 w)

/-- `g` is a *gauging* for `M` with concentration `c`: it sums to `1` and `M g` is the constant
vector `c`. This is Definition 2.3 of the source, which states it for symmetric `M`. -/
def IsGauging (M : Matrix X X ℝ) (g : X → ℝ) (c : ℝ) : Prop :=
  ∑ i, g i = 1 ∧ M *ᵥ g = Function.const X c

omit [DecidableEq X] [Nonempty X] [MetricSpace X] in
/-- All gaugings of a symmetric matrix share one concentration, so $\mathrm{con}$ is an
attribute of the matrix. The source records this after Definition 2.3, as the calculation
$c = c\mathbf{1}^T v' = (v^TA^T)v' = v^T(c'\mathbf{1}) = c'$, and Definition 2.4 rests on it. -/
@[category textbook, AMS 15]
theorem concentration_unique {M : Matrix X X ℝ} (hM : M.IsSymm) {g g' : X → ℝ} {c c' : ℝ}
    (h : IsGauging M g c) (h' : IsGauging M g' c') : c = c' := by
  obtain ⟨hs, hg⟩ := h
  obtain ⟨hs', hg'⟩ := h'
  have key : g' ⬝ᵥ (M *ᵥ g) = (M *ᵥ g') ⬝ᵥ g := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hM.eq]
  rw [hg, hg'] at key
  simpa [dotProduct, Function.const, ← Finset.sum_mul, ← Finset.mul_sum, hs, hs'] using key

/-- `M` has finite concentration, written $\mathrm{con}(M) \neq \infty$ in the source: some
gauging for `M` exists.

Definition 2.4 sets $\mathrm{con}(M)$ to the concentration of any gauging, and to $\infty$ when
there is none, so `con(M) ≠ ∞` is exactly this. Stating it as existence keeps the value of
$\mathrm{con}$ out of the statement; `concentration_unique` above is what makes that value
well defined in the first place. -/
def HasFiniteConcentration (M : Matrix X X ℝ) : Prop :=
  ∃ g c, IsGauging M g c

-- In the docstring below, matrix rows are separated by `\cr` rather than `\\`: the website's
-- markdown processing strips one backslash from `\\` before KaTeX runs, which destroys the
-- row breaks.
/--
**Conjecture 3.3 (Roff-Willerton, 2026).** A finite metric space admits a microscopic weighting
if and only if its distance matrix has finite concentration.

`Nonempty` is needed and not just tidiness. On the empty space every gauging condition fails,
since `∑ i, g i` is `0` rather than `1`, while `X → ℝ` is a subsingleton so the weighting
converges trivially. The equivalence would be false there for reasons that have nothing to do
with the question.

The answer is false as proved by Kenta Kitamura assisted by ChatGPT 5.6 sol.

The proof proceeds by constructing an explicit counterexample: a finite metric space
on 10 points that has finite concentration but does not admit a microscopic weighting.
The metric space is defined by the following $10 \times 10$ distance matrix $A$:
$$
\begin{pmatrix}
0 & 116 & 236 & 231 & 260 & 124 & 64 & 290 & 266 & 64 \cr
116 & 0 & 312 & 268 & 296 & 112 & 64 & 280 & 296 & 64 \cr
236 & 312 & 0 & 68 & 40 & 236 & 288 & 68 & 36 & 288 \cr
231 & 268 & 68 & 0 & 34 & 237 & 288 & 72 & 40 & 288 \cr
260 & 296 & 40 & 34 & 0 & 264 & 320 & 40 & 68 & 320 \cr
124 & 112 & 236 & 237 & 264 & 0 & 64 & 280 & 264 & 64 \cr
64 & 64 & 288 & 288 & 320 & 64 & 0 & 312 & 320 & 120 \cr
290 & 280 & 68 & 72 & 40 & 280 & 312 & 0 & 40 & 312 \cr
266 & 296 & 36 & 40 & 68 & 264 & 320 & 40 & 0 & 320 \cr
64 & 64 & 288 & 288 & 320 & 64 & 120 & 312 & 320 & 0
\end{pmatrix}
$$

The space has finite concentration, demonstrated by the explicit gauging $g$:
$$
g = \frac{1}{24842973905} \begin{pmatrix} 3672468740 \cr 6389133731 \cr 9124217512 \cr
5612262448 \cr -6875621136 \cr 2754831248 \cr 0 \cr 10758780188 \cr -6593098826 \cr 0
\end{pmatrix}
$$
which gives $A g = \frac{4111107017312}{24842973905} \mathbf{1}$.

To prove that it does not admit a microscopic weighting, we provide a vector $v \in \ker A$:
$$
v = \begin{pmatrix} -2 \cr -1 \cr 3 \cr 4 \cr -4 \cr -2 \cr 2 \cr 2 \cr -4 \cr 2 \end{pmatrix}
$$
along with a row-space certificate $q$ for the entrywise square matrix $B = A^{\circ 2}$ satisfying $q A = v^\top B$:
$$
q^\top = \frac{1}{128472094291} \begin{pmatrix} 43681853675722 \cr -53873248293642 \cr
-66890627544007 \cr -81187181670120 \cr 24308499983196 \cr 40819375894674 \cr 0 \cr
54690260644468 \cr 35226831040652 \cr 0
\end{pmatrix}
$$
This certificate shows that the obstruction $v^\top B$ annihilates $\ker A$, making it impossible to construct a convergent weighting.
-/
@[category research solved, AMS 15 51,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/microscopic-weighting-counterexample/blob/eff8979/lean/MicroscopicWeightingCounterexampleFC.lean#L886-L894"]
theorem microscopic_weighting_iff_finite_concentration :
    answer(False) ↔ ∀ (X : Type) [Fintype X] [DecidableEq X] [Nonempty X] [MetricSpace X],
      HasMicroscopicWeighting X ↔ HasFiniteConcentration (distanceMatrix X) := by
  sorry

/--
One direction is known: a microscopic weighting implies finite concentration (Theorem 3.1(3)).
Together with the conjecture above this leaves the converse, that finite concentration is enough.
-/
@[category research solved, AMS 15 51]
theorem hasFiniteConcentration_of_hasMicroscopicWeighting
    (h : HasMicroscopicWeighting X) : HasFiniteConcentration (distanceMatrix X) := by
  sorry

/--
Theorem 3.8: the conjecture is known when the distance matrix is invertible, and the microscopic
weighting is then the unique gauging.
-/
@[category research solved, AMS 15 51]
theorem hasMicroscopicWeighting_iff_of_isUnit (h : IsUnit (distanceMatrix X).det) :
    HasMicroscopicWeighting X ↔ HasFiniteConcentration (distanceMatrix X) := by
  sorry

end Arxiv.«2607.05349»
