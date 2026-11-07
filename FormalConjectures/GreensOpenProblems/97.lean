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
# Ben Green's Open Problem 97

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.97)
- [Si23] Simkin, M., *The number of $n$-queens configurations*. Adv. Math. 427 (2023),
  Paper No. 109127. [arXiv:2107.13460](https://arxiv.org/abs/2107.13460)
- [BoKe21] Bowtell, C. and Keevash, P., *The $n$-queens problem*.
  [arXiv:2109.08083](https://arxiv.org/abs/2109.08083) (2021).
- [NAB23] Nobel, P., Agrawal, A. and Boyd, S., *Computing tighter bounds on the $n$-queens
  constant via Newton's method*. Optim. Lett. 17 (2023), 1229--1240.
  [arXiv:2112.03336](https://arxiv.org/abs/2112.03336)
- [EMM19] Eberhard, S., Manners, F. and Mrazović, R., *Additive triples of bijections, or the
  toroidal semiqueens problem*. J. Eur. Math. Soc. 21 (2019), 441--463.
  [arXiv:1510.05987](https://arxiv.org/abs/1510.05987)
-/

@[expose] public section

open Filter Asymptotics
open scoped Nat Topology

namespace Green97

/--
The permutation `σ` of `Fin n` is a placement of $n$ non-attacking queens on the $n \times n$
board, with the queen of row `i` in column `σ i`.

A placement of $n$ queens on an $n \times n$ board has exactly one queen in each row and in each
column, so it is a permutation. Two queens on the same diagonal have the same value of
`σ i - i` or of `σ i + i`, computed in $\mathbb{Z}$.
-/
def IsQueens {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  (Function.Injective fun i : Fin n ↦ ((σ i).val : ℤ) - (i.val : ℤ)) ∧
    Function.Injective fun i : Fin n ↦ ((σ i).val : ℤ) + (i.val : ℤ)

instance {n : ℕ} : DecidablePred (IsQueens (n := n)) := fun σ ↦ by
  unfold IsQueens
  infer_instance

/--
`numQueens n` is $Q(n)$, the number of ways to place $n$ non-attacking queens on an $n \times n$
chessboard (`IsQueens`). For $n = 0$ there is one (empty) placement.
-/
def numQueens (n : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) ↦ IsQueens σ).card

/--
The permutation `σ` of `Fin n` is a placement of $n$ non-attacking queens on the toroidal
$n \times n$ board: as for `IsQueens`, but the diagonals wrap around, so `σ i - i` and `σ i + i`
are computed in $\mathbb{Z}/n\mathbb{Z}$.
-/
def IsToroidalQueens {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  (Function.Injective fun i : Fin n ↦ ((σ i).val : ZMod n) - (i.val : ZMod n)) ∧
    Function.Injective fun i : Fin n ↦ ((σ i).val : ZMod n) + (i.val : ZMod n)

instance {n : ℕ} : DecidablePred (IsToroidalQueens (n := n)) := fun σ ↦ by
  unfold IsToroidalQueens
  infer_instance

/--
`numToroidalQueens n` is $T(n)$, the number of ways to place $n$ non-attacking queens on the
toroidal $n \times n$ board (`IsToroidalQueens`).
-/
def numToroidalQueens (n : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) ↦ IsToroidalQueens σ).card

/--
The filter on `ℕ` for $n \to \infty$ through the integers with $n \equiv 1, 5 \pmod 6$. For
$n \ge 1$, these are exactly the $n$ for which $T(n) > 0$ (Pólya, see [BoKe21, Chapter 1]).
-/
noncomputable def toroidalDegrees : Filter ℕ :=
  atTop ⊓ Filter.principal {n : ℕ | n % 6 = 1 ∨ n % 6 = 5}

/-- The 4-queens problem has $2$ solutions. -/
@[category test, AMS 5]
theorem numQueens_four : numQueens 4 = 2 := by
  decide +kernel

/-- The 3-queens problem has no solution. -/
@[category test, AMS 5]
theorem numQueens_three : numQueens 3 = 0 := by
  decide +kernel

/-- On the toroidal $5 \times 5$ board there are $10$ placements of $5$ non-attacking queens. -/
@[category test, AMS 5]
theorem numToroidalQueens_five : numToroidalQueens 5 = 10 := by
  decide +kernel

def green_97.answer : ℕ → ℝ := sorry

/--
In how many ways (asymptotically) $Q(n)$ may $n$ non-attacking queens be placed on an
$n \times n$ chessboard?

This is the $n$-queens problem, see [Gr24, Problem 97]. We read "asymptotically" as: find an
explicit function `green_97.answer` with $Q(n) \sim$ `green_97.answer n`. The function
$n \mapsto Q(n)$ itself is not an explicit answer. [Gr24] notes that an asymptotic "rather than
an asymptotic for the log" is open. What is known is $Q(n) = ((1+o(1))\, n e^{-\alpha})^n$ for a
constant $1.94 < \alpha < 1.9449$ [Si23], see `green_97.variants.simkin`.
-/
@[category research open, question value, AMS 5]
theorem green_97 :
    (fun n : ℕ ↦ (numQueens n : ℝ)) ~[atTop] green_97.answer := by
  sorry

/--
**Simkin's theorem.** There is a constant $1.94 < \alpha < 1.9449$ such that
$$\lim_{n \to \infty} \frac{Q(n)^{1/n}}{n} = e^{-\alpha},$$
that is, $Q(n) = ((1+o(1))\, n e^{-\alpha})^n$ [Si23, Theorem 1.1]. The constant $\alpha$ is
defined in [Si23] as the solution of a convex optimisation problem over Borel probability measures
on the square $[-1/2, 1/2]^2$. The limit determines $\alpha$ uniquely. Nobel, Agrawal and Boyd
[NAB23] combined Simkin's formulation with a sharper bound of Knuth, solved the resulting convex
problems numerically, and report the tighter range
$\alpha \in [1.944000752, 1.944001082]$.
-/
@[category research solved, AMS 5]
theorem green_97.variants.simkin :
    ∃ α : ℝ, 1.94 < α ∧ α < 1.9449 ∧
      Tendsto (fun n : ℕ ↦ (numQueens n : ℝ) ^ ((1 : ℝ) / n) / n) atTop
        (𝓝 (Real.exp (-α))) := by
  sorry

def green_97.variants.alpha.answer : ℝ := sorry

/--
Find an explicit value for the constant $\alpha$ of `green_97.variants.simkin`, that is, the
number with $Q(n)^{1/n}/n \to e^{-\alpha}$.

[Gr24] writes that "an explicit solution remains an open problem". The value $\alpha$ is the
solution of an entropy optimisation problem [Si23]. As for `green_97`, an explicit closed form is
intended.
-/
@[category research open, question value, AMS 5]
theorem green_97.variants.alpha :
    Tendsto (fun n : ℕ ↦ (numQueens n : ℝ) ^ ((1 : ℝ) / n) / n) atTop
      (𝓝 (Real.exp (-green_97.variants.alpha.answer))) := by
  sorry

/--
**Bowtell and Keevash.** For $n \equiv 1, 5 \pmod 6$ the number of toroidal $n$-queens
configurations satisfies $T(n) = ((1+o(1))\, n e^{-3})^n$ [BoKe21, Theorem 1.2]. The filter
`toroidalDegrees` restricts to these $n$, because $T(n) = 0$ for all other $n \ge 1$.
-/
@[category research solved, AMS 5]
theorem green_97.variants.bowtell_keevash :
    Tendsto (fun n : ℕ ↦ (numToroidalQueens n : ℝ) ^ ((1 : ℝ) / n) / n) toroidalDegrees
      (𝓝 (Real.exp (-3))) := by
  sorry

def green_97.variants.toroidal.answer : ℕ → ℝ := sorry

/--
Find an asymptotic for the number $T(n)$ of toroidal $n$-queens configurations, for
$n \equiv 1, 5 \pmod 6$.

[Gr24] writes, after the result of [BoKe21], that the problem of "obtaining an asymptotic (rather
than an asymptotic for the log) remains open". [BoKe21] proved the asymptotic of the logarithm, see
`green_97.variants.bowtell_keevash`. We read "asymptotic" as for `green_97`: an explicit function
is intended.
-/
@[category research open, question value, AMS 5]
theorem green_97.variants.toroidal :
    (fun n : ℕ ↦ (numToroidalQueens n : ℝ)) ~[toroidalDegrees]
      green_97.variants.toroidal.answer := by
  sorry

/--
`numAdditiveTriples n` is the number of pairs $(\pi_1, \pi_2)$ of bijections
$\{1, \dots, n\} \to \mathbb{Z}/n\mathbb{Z}$ such that $\pi_1 + \pi_2$ is also a bijection
[EMM19, Section 1]. It is $n!$ times the number of arrangements of $n$ mutually non-attacking
semiqueens on the toroidal $n \times n$ board, where a semiqueen moves along rows, columns and
one diagonal direction.
-/
noncomputable def numAdditiveTriples (n : ℕ) : ℕ :=
  Nat.card {π : (Fin n ≃ ZMod n) × (Fin n ≃ ZMod n) //
    Function.Bijective fun i ↦ π.1 i + π.2 i}

/--
**Eberhard, Manners and Mrazović.** For odd $n$, the number $s_n$ of pairs $(\pi_1, \pi_2)$ of
bijections $\{1, \dots, n\} \to \mathbb{Z}/n\mathbb{Z}$ with $\pi_1 + \pi_2$ also a bijection is
$$s_n = (e^{-1/2} + o(1))\, \frac{(n!)^3}{n^{n-1}}$$
[EMM19, Theorem 1.2]. [Gr24] refers to this paper for the variant of the toroidal question where
only $\pi_1$, $\pi_2$ and $\pi_1 - \pi_2$ are required to be bijections. Replacing $\pi_2$ by
$-\pi_2$ shows that this variant has the same count $s_n$. For even $n$, $s_n = 0$
[EMM19, Section 1], so the theorem is stated for odd $n$.
-/
@[category research solved, AMS 5]
theorem green_97.variants.eberhard_manners_mrazovic :
    (fun n : ℕ ↦ (numAdditiveTriples n : ℝ)) ~[atTop ⊓ Filter.principal {n : ℕ | Odd n}]
      fun n : ℕ ↦ Real.exp (-(1 / 2)) * ((n ! : ℕ) : ℝ) ^ 3 / (n : ℝ) ^ (n - 1) := by
  sorry

end Green97
