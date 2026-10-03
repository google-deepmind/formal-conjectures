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
# Erdős Problem 704

*References:*
- [erdosproblems.com/704](https://www.erdosproblems.com/704)
- [Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*.
  Combinatorica (1981), 25-42.
- [FrWi81] Frankl, P. and Wilson, R. M., *Intersection theorems with geometric consequences*.
  Combinatorica (1981), 357-368.
- [LaRo72] Larman, D. G. and Rogers, C. A., *The realization of distances within sets in
  Euclidean space*. Mathematika (1972), 1-24.
- [Pr20] Prosanov, R., *A new proof of the Larman-Rogers upper bound for the chromatic number of
  the Euclidean space*. Discrete Appl. Math. (2020), 115-120.
- [Ra00] Raigorodskii, A. M., *On the chromatic number of a space*. Uspekhi Mat. Nauk (2000),
  147-148.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Erdos704

/--
The unit distance graph $G_n$ on $\mathbb{R}^n$: two points are adjacent if and only if the
distance between them is $1$.
-/
def unitDistanceGraph (n : ℕ) : SimpleGraph (EuclideanSpace ℝ (Fin n)) where
  Adj x y := dist x y = 1
  symm.symm x y := by simp [dist_comm]

/--
Does $\chi(G_n)$ grow exponentially in $n$?

Yes: Frankl and Wilson [FrWi81] proved an exponential lower bound and Larman and Rogers
[LaRo72] proved an exponential upper bound. Here exponential growth means that there are
constants $1 < c \leq C$ such that $c^n \leq \chi(G_n) \leq C^n$ for all large $n$.
-/
@[category research solved, AMS 5 52]
theorem erdos_704.parts.i : answer(True) ↔
    (∃ c > (1 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ k : ℕ, (unitDistanceGraph n).Colorable k → c ^ n ≤ (k : ℝ)) ∧
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      ∃ k : ℕ, (unitDistanceGraph n).Colorable k ∧ (k : ℝ) ≤ C ^ n := by
  sorry

/--
Let $G_n$ be the unit distance graph in $\mathbb{R}^n$, with two vertices joined by an edge if
and only if the distance between them is $1$. Does
$$\lim_{n\to\infty}\chi(G_n)^{1/n}$$
exist?

This generalises the Hadwiger–Nelson problem (Erdős Problem 508), the case $n = 2$. The
chromatic number is finite (see `Erdos704.erdos_704.variants.cube_colouring`).
-/
@[category research open, AMS 5 52]
theorem erdos_704.parts.ii : answer(sorry) ↔
    ∃ L : ℝ, Tendsto
      (fun n : ℕ ↦ ((unitDistanceGraph n).chromaticNumber.toNat : ℝ) ^ (1 / (n : ℝ)))
      atTop (𝓝 L) := by
  sorry

/--
The trivial colouring (by tiling with cubes) gives
$$\chi(G_n) \leq (2 + \sqrt{n})^n.$$
In particular $\chi(G_n)$ is finite for every $n$.
-/
@[category textbook, AMS 5 52]
theorem erdos_704.variants.cube_colouring :
    ∀ n : ℕ, ∃ k : ℕ, (unitDistanceGraph n).Colorable k ∧
      (k : ℝ) ≤ (2 + Real.sqrt n) ^ n := by
  sorry

/--
Frankl and Wilson [FrWi81] proved
$$\chi(G_n) \geq (1 + o(1)) 1.2^n.$$
-/
@[category research solved, AMS 5 52]
theorem erdos_704.variants.frankl_wilson :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ k : ℕ, (unitDistanceGraph n).Colorable k → (1 - ε) * 1.2 ^ n ≤ (k : ℝ) := by
  sorry

/--
Raigorodskii [Ra00] proved
$$\chi(G_n) \geq (1.239\cdots + o(1))^n.$$
We state the weaker bound with the truncated constant $1.239$: for every $0 < c < 1.239$ we
have $\chi(G_n) \geq c^n$ for all large $n$.
-/
@[category research solved, AMS 5 52]
theorem erdos_704.variants.raigorodskii :
    ∀ c ∈ Set.Ioo (0 : ℝ) 1.239, ∀ᶠ n : ℕ in atTop,
      ∀ k : ℕ, (unitDistanceGraph n).Colorable k → c ^ n ≤ (k : ℝ) := by
  sorry

/--
Larman and Rogers [LaRo72] proved
$$\chi(G_n) \leq (3 + o(1))^n.$$
Prosanov [Pr20] has given an alternative proof of this bound.
-/
@[category research solved, AMS 5 52]
theorem erdos_704.variants.larman_rogers :
    ∀ C > (3 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∃ k : ℕ, (unitDistanceGraph n).Colorable k ∧ (k : ℝ) ≤ C ^ n := by
  sorry

/--
Larman and Rogers [LaRo72] conjecture that the truth may be
$$\chi(G_n) = (2^{3/2} + o(1))^n,$$
that is, $\chi(G_n)^{1/n} \to 2^{3/2}$.
-/
@[category research open, AMS 5 52]
theorem erdos_704.variants.larman_rogers_conjecture :
    Tendsto
      (fun n : ℕ ↦ ((unitDistanceGraph n).chromaticNumber.toNat : ℝ) ^ (1 / (n : ℝ)))
      atTop (𝓝 ((2 : ℝ) ^ ((3 : ℝ) / 2))) := by
  sorry

end Erdos704
