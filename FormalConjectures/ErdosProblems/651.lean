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
# Erdős Problem 651

*References:*
- [erdosproblems.com/651](https://www.erdosproblems.com/651)
- [Er97e] Erdős, P., *Some of my favourite unsolved problems*. Math. Japon. (1997), 527-537.
- [ErSz60] Erdős, P. and Szekeres, G., *On some extremum problems in elementary geometry*.
  Ann. Univ. Sci. Budapest. Eötvös Sect. Math. 3-4 (1960/61), 53-62.
- [PoZa22] Pohoata, C. and Zakharov, D., *Convex polytopes from fewer points*.
  [arXiv:2208.04878](https://arxiv.org/abs/2208.04878) (2022).
- [Va96] Valtr, P., *Several results related to the Erdős-Szekeres theorem*. Doctoral
  dissertation, Charles University, Prague (1996).
-/

@[expose] public section

open Filter
open scoped EuclideanGeometry

namespace Erdos651

/--
A finite set `X` of points of $\mathbb{R}^k$ is in general position if every subset of at most
$k + 1$ points is affinely independent.

For $|X| \geq k + 1$ this says that no $k + 1$ points of `X` lie on a common hyperplane, which is
the definition of [PoZa22, Section 1]. For smaller sets it also rules out degenerate
configurations, such as three collinear points in $\mathbb{R}^3$. This is not
`EuclideanGeometry.InGeneralPosition`, which is for the plane and means that no three points are
collinear and no four are concyclic.
-/
def IsInGeneralPosition {k : ℕ} (X : Finset (ℝ^k)) : Prop :=
  ∀ Y ⊆ X, Y.card ≤ k + 1 → AffineIndependent ℝ ((↑) : ↥(Y : Set (ℝ^k)) → ℝ^k)

/--
`X` contains `n` points in convex position: there is a subset of `n` points such that none of
them lies in the convex hull of the others. These are the vertices of a convex polytope.
-/
def HasConvexSubset {k : ℕ} (n : ℕ) (X : Finset (ℝ^k)) : Prop :=
  ∃ Y ⊆ X, Y.card = n ∧ ConvexIndependent ℝ ((↑) : ↥(Y : Set (ℝ^k)) → ℝ^k)

/--
The set of integers `N` such that every set of at least `N` points in general position in
$\mathbb{R}^k$ contains `n` points in convex position.

A subset of a set in general position is in general position. So `N` belongs to this set
exactly when every set of exactly `N` points in general position contains `n` points in convex
position, and the set is closed upwards (see `cardSet_mono`).
-/
def cardSet (k n : ℕ) : Set ℕ :=
  {N | ∀ X : Finset (ℝ^k), IsInGeneralPosition X → N ≤ X.card → HasConvexSubset n X}

/--
$f_k(n)$ is the smallest integer such that any $f_k(n)$ points in general position in
$\mathbb{R}^k$ contain $n$ points in convex position.

For $k \geq 2$ the set `cardSet k n` is non-empty (see `nonempty_cardSet`), so `sInf` is a
minimum. For $k \leq 1$ the value is not meaningful: for $k = 1$ and $n \geq 3$ the set is empty
and `f 1 n = 0` is a junk value. We only use `f k n` for $k \geq 2$.
-/
noncomputable def f (k n : ℕ) : ℕ := sInf (cardSet k n)

/-- If `N` belongs to `cardSet k n`, so does every larger integer. -/
@[category API, AMS 5 52]
theorem cardSet_mono {k n N M : ℕ} (hN : N ∈ cardSet k n) (hNM : N ≤ M) :
    M ∈ cardSet k n := by
  intro X hX hM
  exact hN X hX (hNM.trans hM)

/-- If `N` belongs to `cardSet k n`, then `f k n ≤ N`. -/
@[category API, AMS 5 52]
theorem f_le {k n N : ℕ} (h : N ∈ cardSet k n) : f k n ≤ N :=
  Nat.sInf_le h

/--
For $k \geq 2$ and every $n$ there is an integer $N$ such that any $N$ points in general
position in $\mathbb{R}^k$ contain $n$ points in convex position. So $f_k(n)$ is well defined.

This is the higher-dimensional Erdős-Szekeres theorem. For $n \leq k + 1$ one can take $N = n$.
For larger $n$ it follows from Ramsey's theorem, which gives $f_k(n) \leq R_{k+2}(k+3, n)$, see
[PoZa22, Section 1].
-/
@[category research solved, AMS 5 52]
theorem nonempty_cardSet {k : ℕ} (hk : 2 ≤ k) (n : ℕ) : (cardSet k n).Nonempty := by
  sorry

/--
Let $f_k(n)$ denote the smallest integer such that any $f_k(n)$ points in general position in
$\mathbb{R}^k$ contain $n$ which determine a convex polyhedron. Is it true that
$$
  f_k(n) > (1+c_k)^n
$$
for some constant $c_k>0$?

A problem of Erdős [Er97e]. We read "determine a convex polyhedron" as "are in convex position",
and the inequality as holding, with some $c_k > 0$, for all sufficiently large $n$. We ask the
question for every dimension $k \geq 3$. The planar case $k = 2$ is the Erdős-Klein-Szekeres
problem (see `erdos_651.variants.planar`).

The answer is no. Pohoata and Zakharov [PoZa22, Theorem 1.1] proved that $f_3(n) \leq 2^{o(n)}$,
and this implies $f_k(n) \leq 2^{o(n)}$ for every $k \geq 3$, see
`erdos_651.variants.pohoata_zakharov`.
-/
@[category research solved, question, AMS 5 52]
theorem erdos_651 :
    ¬ ∀ k : ℕ, 3 ≤ k → ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (1 + c) ^ n < (f k n : ℝ) := by
  sorry

/--
Pohoata and Zakharov [PoZa22, Theorem 1.1] proved that $ES_3(n) = 2^{o(n)}$, where $ES_k(n)$ is
the function $f_k(n)$ above: for every $\varepsilon > 0$ and all large $n$, any set of at least
$2^{\varepsilon n}$ points in general position in $\mathbb{R}^3$ contains $n$ points in convex
position. By the projection argument of Valtr [Va96] (see `erdos_651.variants.antitone`) the same
holds in every dimension $k \geq 3$ [PoZa22, abstract and Section 1].

The theorem gives $f_k(n) \leq \lceil 2^{\varepsilon n} \rceil$. The form below follows by
applying it with $\varepsilon / 2$.
-/
@[category research solved, AMS 5 52]
theorem erdos_651.variants.pohoata_zakharov {k : ℕ} (hk : 3 ≤ k) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (f k n : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ)) := by
  sorry

/--
For every dimension $k \geq 3$ and every $c > 0$ one has $f_k(n) \leq (1+c)^n$ for all large
$n$. This is `erdos_651.variants.pohoata_zakharov` with $\varepsilon = \log_2(1 + c)$. In
particular, for every $c > 0$ the lower bound $f_k(n) > (1+c)^n$ fails not only for infinitely
many $n$ but for all large $n$.
-/
@[category research solved, AMS 5 52]
theorem erdos_651.variants.subexponential {k : ℕ} (hk : 3 ≤ k) :
    ∀ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (f k n : ℝ) ≤ (1 + c) ^ n := by
  sorry

/--
For $k = 2$ the lower bound of the question holds: $f_2(n) > (1+c)^n$ for some $c > 0$ and all
large $n$. Erdős and Szekeres [ErSz60] proved that
$2^{n-2} + 1 \leq f_2(n)$, see [PoZa22, abstract and Section 1], and $(3/2)^n < 2^{n-2} + 1$ for
all $n \geq 5$. The Erdős-Klein-Szekeres conjecture (Erdős Problem 107) states that
$f_2(n) = 2^{n-2} + 1$ for $n \geq 3$.
-/
@[category research solved, AMS 5 52]
theorem erdos_651.variants.planar :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (1 + c) ^ n < (f 2 n : ℝ) := by
  sorry

/--
The function $f_k(n)$ does not increase with the dimension: $f_{k+1}(n) \leq f_k(n)$ for
$k \geq 2$. Given a set in general position in $\mathbb{R}^{k+1}$ with at least $f_k(n)$ points,
project it to a generic hyperplane, find $n$ points in convex position in the projection, and
lift them back. This projection argument is due to Valtr [Va96]; see [PoZa22, Section 1, (1)].

The site states that $f_2(n) > f_3(n) > \cdots$. [PoZa22] gives only the non-strict inequality, so
we state that. The strict inequalities fail for small $n$: for example $f_2(3) = f_3(3) = 3$.
-/
@[category research solved, AMS 5 52]
theorem erdos_651.variants.antitone {k : ℕ} (hk : 2 ≤ k) (n : ℕ) : f (k + 1) n ≤ f k n := by
  sorry

end Erdos651
