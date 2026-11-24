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
# Hermite's Problem and Jacobi–Perron Periodicity

By Lagrange's 1770 theorem, a real irrational number has an eventually periodic simple continued
fraction expansion precisely when it is quadratic over $\mathbb{Q}$. In an 1848 letter to C. G. J.
Jacobi (published 1850), Charles Hermite asked for an integer sequence representation of real
numbers whose eventual periodicity characterizes cubic irrationals.

While Wikipedia describes Jacobi's multidimensional continued-fraction approach qualitatively, the
explicit normalized map $(x, y) \mapsto (\{y / x\}, \{1 / x\})$ on $[0, 1)^2$ with floor digits
$(\lfloor 1 / x \rfloor, \lfloor y / x \rfloor)$ follows Jacobi (1868) and Oskar Perron (1907).
Perron (1907, Satz IX and Satz X) proved that every non-terminating eventually periodic
two-dimensional Jacobi–Perron expansion comes from a $\mathbb{Q}$-linearly independent triple
$(1, x, y)$ spanning a real cubic number field $[K : \mathbb{Q}] = 3$. Whether the converse holds
for every such cubic basis—and in particular for $(\{\alpha\}, \{\alpha^2\})$ when $\alpha$ is a
real cubic irrational—remains open.

*References:*
- [Wikipedia: Hermite's problem](https://en.wikipedia.org/wiki/Hermite%27s_problem)
- C. Hermite, *Extraits de lettres de M. Ch. Hermite à M. Jacobi sur différents objets de la
  théorie des nombres*, J. Reine Angew. Math. **40** (1850), 261–315.
- C. G. J. Jacobi, *Allgemeine Theorie der kettenbruchähnlichen Algorithmen, in welchen jede Zahl
  aus drei vorhergehenden gebildet wird*, J. Reine Angew. Math. **69** (1868), 29–64.
- O. Perron, *Grundlagen für eine Theorie des Jacobischen Kettenbruchalgorithmus*, Math. Ann.
  **64** (1907), 1–76.
-/

@[expose] public section

namespace HermiteProblem

open scoped Classical in
/-- One step of the normalized two-dimensional Jacobi–Perron transformation
$(x, y) \mapsto (\{y / x\}, \{1 / x\})$ on $[0, 1)^2$, returning $(0, 0)$ when $x = 0$. -/
noncomputable def jacobiPerronStep (s : ℝ × ℝ) : ℝ × ℝ :=
  if s.1 = 0 then (0, 0) else (Int.fract (s.2 / s.1), Int.fract (1 / s.1))

open scoped Classical in
/-- Integer floor-digit pair $(\lfloor 1 / x \rfloor, \lfloor y / x \rfloor)$ produced by one
Jacobi–Perron step, returning $(0, 0)$ when $x = 0$. -/
noncomputable def jacobiPerronDigits (s : ℝ × ℝ) : ℤ × ℤ :=
  if s.1 = 0 then (0, 0) else (Int.floor (1 / s.1), Int.floor (s.2 / s.1))

/-- A real number $\alpha$ is a cubic irrational if it is algebraic over $\mathbb{Q}$ of degree
$[\mathbb{Q}(\alpha) : \mathbb{Q}] = 3$. -/
def IsRealCubicIrrational (α : ℝ) : Prop :=
  IsAlgebraic ℚ α ∧ (minpoly ℚ α).natDegree = 3

/-- The Jacobi–Perron expansion from $s_0 \in \mathbb{R}^2$ is non-terminating and eventually
periodic if $x_n \ne 0$ for all $n \ge 0$ and its digit stream repeats with some period $T \ge 1$
from some index $N_0$ onward. -/
def HasEventuallyPeriodicJacobiPerron (s₀ : ℝ × ℝ) : Prop :=
  (∀ n : ℕ, ((jacobiPerronStep^[n]) s₀).1 ≠ 0) ∧
    ∃ N₀ T : ℕ, 1 ≤ T ∧
      ∀ n : ℕ, N₀ ≤ n →
        jacobiPerronDigits ((jacobiPerronStep^[n + T]) s₀) =
          jacobiPerronDigits ((jacobiPerronStep^[n]) s₀)

/-- At $(1/2, 3/4)$, one Jacobi–Perron step emits the integer digit pair $(2, 1)$. -/
@[category test, AMS 11]
theorem jacobiPerronDigits_half_three_quarters :
    jacobiPerronDigits (1 / 2, 3 / 4) = (2, 1) := by
  unfold jacobiPerronDigits
  rw [if_neg (by norm_num)]
  ext <;> dsimp <;> norm_num

/-- At $(1/2, 3/4)$, one Jacobi–Perron step maps the state to $(1/2, 0)$. -/
@[category test, AMS 11]
theorem jacobiPerronStep_half_three_quarters :
    jacobiPerronStep (1 / 2, 3 / 4) = (1 / 2, 0) := by
  unfold jacobiPerronStep
  rw [if_neg (by norm_num)]
  ext <;> dsimp
  · rw [show (3 / 4 : ℝ) / (1 / 2) = (1 / 2 : ℝ) + (1 : ℤ) by norm_num,
      Int.fract_add_intCast (1 / 2 : ℝ) 1]
    exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  · rw [show (1 : ℝ) / (1 / 2) = (2 : ℤ) by norm_num]
    exact Int.fract_intCast 2

/-- No rational number $q \in \mathbb{Q}$ satisfies `IsRealCubicIrrational`. -/
@[category test, AMS 11]
theorem ratCast_not_isRealCubicIrrational (q : ℚ) : ¬ IsRealCubicIrrational (q : ℝ) := by
  rintro ⟨_, hdeg⟩
  have hmin : minpoly ℚ (q : ℝ) = Polynomial.X - Polynomial.C q := by
    simpa only [eq_ratCast] using minpoly.eq_X_sub_C ℝ q
  rw [hmin, Polynomial.natDegree_X_sub_C] at hdeg
  omega

/-- At $(0, 0)$, the Jacobi–Perron iteration terminates at step $0$ and fails
`HasEventuallyPeriodicJacobiPerron`. -/
@[category test, AMS 11]
theorem not_hasEventuallyPeriodicJacobiPerron_zero :
    ¬ HasEventuallyPeriodicJacobiPerron (0, 0) := by
  rintro ⟨hnez, _⟩
  exact hnez 0 rfl

/--
**Perron's Periodicity Theorem** (Perron 1907, Satz IX and Satz X, p. 41): if $x, y \in [0, 1)$
have a non-terminating eventually periodic two-dimensional Jacobi–Perron expansion, then $x$ and
$y$ lie in a real cubic subfield $K \subseteq \mathbb{R}$ ($[K : \mathbb{Q}] = 3$) with $(1, x, y)$
linearly independent over $\mathbb{Q}$.
-/
@[category research solved, AMS 11]
theorem perron_periodic_implies_cubic_basis (x y : ℝ)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (hy : y ∈ Set.Ico (0 : ℝ) 1)
    (hper : HasEventuallyPeriodicJacobiPerron (x, y)) :
    ∃ K : IntermediateField ℚ ℝ,
      Module.finrank ℚ K = 3 ∧ x ∈ K ∧ y ∈ K ∧ LinearIndependent ℚ ![1, x, y] := by
  sorry

/--
**Jacobi–Perron Cubic Field Periodicity Question** (Jacobi 1868; Perron 1907): for every real cubic
subfield $K \subseteq \mathbb{R}$ and every $x, y \in K$ with $(1, x, y)$ linearly independent over
$\mathbb{Q}$ (following Perron 1907 to exclude rational and quadratic degeneracies where the
expansion terminates), is the Jacobi–Perron expansion of $(\{x\}, \{y\})$ eventually periodic?
-/
@[category research open, question, AMS 11]
theorem jacobi_perron_cubic_basis_periodic :
    ∀ (K : IntermediateField ℚ ℝ), Module.finrank ℚ K = 3 →
      ∀ x y : ℝ, x ∈ K → y ∈ K → LinearIndependent ℚ ![1, x, y] →
        HasEventuallyPeriodicJacobiPerron (Int.fract x, Int.fract y) := by
  sorry

/--
**Jacobi–Perron Periodicity Question for $(\{\alpha\}, \{\alpha^2\})$** (Jacobi 1868; Perron 1907):
for every real cubic irrational $\alpha$, is the Jacobi–Perron expansion of
$(\{\alpha\}, \{\alpha^2\})$ non-terminating and eventually periodic? This is the specialization of
`jacobi_perron_cubic_basis_periodic` to the power basis $(1, \alpha, \alpha^2)$ of
$\mathbb{Q}(\alpha)$.
-/
@[category research open, question, AMS 11]
theorem jacobi_perron_cubic_basis_periodic.variants.power_basis :
    ∀ α : ℝ, IsRealCubicIrrational α →
      HasEventuallyPeriodicJacobiPerron (Int.fract α, Int.fract (α ^ 2)) := by
  sorry

end HermiteProblem
