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
# Erdős Problem 106

*References:*
- [erdosproblems.com/106](https://www.erdosproblems.com/106)
- [ErGr75b] Erdős, P. and Graham, R. L., *On packing squares with equal squares*. J. Combinatorial
  Theory Ser. A (1975), 119--123.
- [Er94b] Erdős, Paul, *Some problems in number theory, combinatorics and combinatorial geometry*.
  Math. Pannon. (1994), 261-269.
- [Er95] Erdős, Paul, *Some of my favourite problems in number theory, combinatorics, and
  geometry*. Resenhas (1995), 165-186.
- [Ha84] Halász, Sylvia, *Packing a convex domain with similar convex domains*. J. Combin. Theory
  Ser. A (1984), 85--90.
- [ErSo95] Erdős, Paul and Soifer, Alexander, *Squares in a square*. Geombinatorics (1995),
  110--114.
- [CaSt05] Campbell, Connie and Staton, William, *A square-packing problem of Erdős*. Amer. Math.
  Monthly (2005), 165--167.
- [Pr08] Praton, I., *Packing squares in a square*. Math. Mag. (2008), 358-361.
- [BKU24] Baek, J. and Koizumi, J. and Ueoro, T., *A note on the Erdős conjecture about square
  packing*. arXiv:2411.07274 (2024).
- [Ra26] A. Raj Singh, *On a square packing conjecture of Erdős*. arXiv:2601.22163 (2026).
-/

@[expose] public section

namespace Erdos106

/-- A square in the plane, given by its centre, a unit vector along one of its sides and its side
length. The other side direction is the counterclockwise quarter-turn of `direction`. -/
structure Square where
  center : ℝ × ℝ
  direction : ℝ × ℝ
  side : ℝ
  side_pos : 0 < side
  direction_unit : direction.1 ^ 2 + direction.2 ^ 2 = 1

/-- The (closed) set of points of a square. -/
def Square.carrier (S : Square) : Set (ℝ × ℝ) :=
  {p | ∃ x y : ℝ, |x| ≤ S.side / 2 ∧ |y| ≤ S.side / 2 ∧
    p = (S.center.1 + x * S.direction.1 - y * S.direction.2,
      S.center.2 + x * S.direction.2 + y * S.direction.1)}

/-- A family of squares is a packing of the unit square if each square lies inside the unit square
and no two of them have a common interior point. -/
def IsPacking {n : ℕ} (P : Fin n → Square) : Prop :=
  (∀ i, (P i).carrier ⊆ Set.Icc 0 1 ×ˢ Set.Icc 0 1) ∧
    Pairwise fun i j => Disjoint (interior (P i).carrier) (interior (P j).carrier)

/-- `f n` is the maximum possible sum of the side lengths of `n` squares drawn inside the unit
square with no common interior point. -/
noncomputable def f (n : ℕ) : ℝ :=
  sSup {t | ∃ P : Fin n → Square, IsPacking P ∧ t = ∑ i, (P i).side}

/-- `g n` is defined as `f n` with the additional assumption that all squares have sides parallel
to the sides of the unit square. -/
noncomputable def g (n : ℕ) : ℝ :=
  sSup {t | ∃ P : Fin n → Square, IsPacking P ∧ (∀ i, (P i).direction = (1, 0)) ∧
    t = ∑ i, (P i).side}

/--
Draw $n$ squares inside the unit square with no common interior point. Let $f(n)$ be the maximum
possible sum of the side-lengths of the squares. Is $f(k^2+1)=k$?

In [Er94b] Erdős dates this conjecture to 'more than 60 years ago'. Erdős proved that $f(2)=1$ in
an early mathematical paper for high school students in Hungary. Newman proved (in personal
communication to Erdős) that $f(5)=2$. It is trivial from the Cauchy-Schwarz inequality that
$f(k^2)=k$.

It is easy to see that $f(k^2+1)\geq k$, by first dividing the unit square into $k^2$ smaller
squares of side-length $1/k$, and then replacing one square by two smaller squares of side-length
$1/2k$. Halász [Ha84] gives a construction that shows $f(k^2+2)\geq k+\frac{1}{k+1}$, and in
general, for any $c\geq 1$, $f(k^2+2c+1)\geq k+\frac{c}{k}$ and $f(k^2+2c)\geq k+\frac{c}{k+1}$.

Erdős and Soifer [ErSo95] and Campbell and Staton [CaSt05] have conjectured that, in general, for
any integer $-k<c<k$, $f(k^2+2c+1)=k+\frac{c}{k}$, and proved the corresponding lower bound.
Praton [Pr08] has proved that this general conjecture is equivalent to $f(k^2+1)=k$.

A negative answer to the original question was provided by Claude Opus 5 (prompted by
Silverstein), which proved that $f(17)>4$. As a consequence there exists an absolute constant
$c>0$ such that $f(k^2+1)\geq k+\frac{c}{k}$ for all $k\geq 4$.

The case $k = 0$ is excluded, since trivially $f(1) = 1$.
-/
@[category research solved, AMS 52, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos106.lean#L618"]
theorem erdos_106 : answer(False) ↔ ∀ k : ℕ, 0 < k → f (k ^ 2 + 1) = k := by
  sorry

/-- The counterexample of Claude Opus 5 (prompted by Silverstein): $f(17) > 4$. -/
@[category research solved, AMS 52, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos106.lean#L610"]
theorem erdos_106.variants.seventeen : 4 < f 17 := by
  sorry

/-- It is known that $f(5)=2$ (Newman). It is not known whether $f(10)=3$. -/
@[category research open, AMS 52]
theorem erdos_106.variants.ten : answer(sorry) ↔ f 10 = 3 := by
  sorry

/--
Baek, Koizumi, and Ueoro [BKU24] have proved $g(k^2+1)=k$, where $g(\cdot)$ is defined identically
to $f(\cdot)$ with the additional assumption that all squares have sides parallel to the sides of
the unit square. More generally, they prove that $g(k^2+2c+1)=k+c/k$ for any $-k<c<k$, which
determines all values of $g(\cdot)$.
-/
@[category research solved, AMS 52]
theorem erdos_106.variants.axis_parallel (k : ℕ) (hk : 0 < k) (c : ℤ) (hc : -k < c ∧ c < k) :
    g (k ^ 2 + 2 * c + 1).toNat = (k : ℝ) + (c : ℝ) / k := by
  sorry

end Erdos106
