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
# Erdős Problem 657

*References:*
- [erdosproblems.com/657](https://www.erdosproblems.com/657)
- [Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971)
  (1973), 117-138.
- [Er75f] Erdős, Paul, *On some problems of elementary and combinatorial geometry*. Ann. Mat.
  Pura Appl. (4) (1975), 99-108.
- [ErPa90] Erdős, P. and Pach, J., *Variations on the theme of repeated distances*.
  Combinatorica (1990), 261-269.
- [Er97e] Erdős, Paul, *Some of my favourite unsolved problems*. Math. Japon. (1997), 527-537.
- [Du08] Dumitrescu, Adrian, *On distinct distances and λ-free point sets*. Discrete Math.
  (2008), 6533-6538.
-/

@[expose] public section

open Filter
open scoped EuclideanGeometry

namespace Erdos657

/--
Is it true that if $A\subset \mathbb{R}^2$ is a set of $n$ points such that every subset of $3$
points determines $3$ distinct distances (that is, $A$ has no isosceles triangles, degenerate
ones included) then $A$ determines at least $f(n)n$ distinct distances, for some function $f$
with $f(n)\to \infty$?
-/
@[category research open, AMS 52]
theorem erdos_657 : answer(sorry) ↔
    ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ n : ℕ, ∀ A : Finset ℝ², A.card = n → (A : Set ℝ²).IsIsoscelesFree →
        f n * (n : ℝ) ≤ (distinctDistances A : ℝ) := by
  sorry

/--
In [Er73] Erdős attributes the problem, more generally in $\mathbb{R}^k$, to himself and Davies:
for every fixed $k \geq 1$, is there a function $f$ with $f(n)\to \infty$ such that every set of
$n$ points in $\mathbb{R}^k$ with no isosceles triangles determines at least $f(n)n$ distinct
distances?

Here the dimension $k$ is fixed and $f$ may depend on $k$.
-/
@[category research open, AMS 52]
theorem erdos_657.variants.higher_dim : answer(sorry) ↔
    ∀ k : ℕ, 1 ≤ k → ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ n : ℕ, ∀ A : Finset (ℝ^k), A.card = n → (A : Set (ℝ^k)).IsIsoscelesFree →
        f n * (n : ℝ) ≤ (distinctDistances A : ℝ) := by
  sorry

/--
The question on the real line, which Erdős [Er73] said was open, has a positive answer: there is
a function $f$ with $f(n)\to \infty$ such that every set of $n$ real numbers with no three-term
arithmetic progression determines at least $f(n)n$ distinct distances. This follows from the
lower bound of Dumitrescu [Du08].

On the line, a set has no isosceles triangle exactly when it has no three-term arithmetic
progression.
-/
@[category research solved, AMS 11 52]
theorem erdos_657.variants.dim_one : answer(True) ↔
    ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ n : ℕ, ∀ A : Finset ℝ, A.card = n → (A : Set ℝ).IsIsoscelesFree →
        f n * (n : ℝ) ≤ (distinctDistances A : ℝ) := by
  sorry

/--
Dumitrescu [Du08] proved that there is a constant $c > 0$ such that, for all large $n$, every set
of $n$ real numbers with no three-term arithmetic progression determines at least
$n(\log n)^c$ distinct distances.
-/
@[category research solved, AMS 11 52]
theorem erdos_657.variants.dim_one_lower :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ A : Finset ℝ, A.card = n → (A : Set ℝ).IsIsoscelesFree →
        (n : ℝ) * (Real.log n) ^ c ≤ (distinctDistances A : ℝ) := by
  sorry

/--
As noted in [Du08], Behrend's construction of large sets without three-term arithmetic
progressions shows that there is a constant $C > 0$ such that, for all large $n$, some set
of $n$ real numbers with no three-term arithmetic progression determines at most
$n 2^{C\sqrt{\log n}}$ distinct distances.
-/
@[category research solved, AMS 11 52]
theorem erdos_657.variants.dim_one_upper :
    ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∃ A : Finset ℝ, A.card = n ∧ (A : Set ℝ).IsIsoscelesFree ∧
        (distinctDistances A : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ (C * √(Real.log n)) := by
  sorry

/--
Straus observed that for every $k$ there is a set of $2^k$ points in $\mathbb{R}^k$ with no
isosceles triangles which determines at most $2^k - 1$ distinct distances.
-/
@[category research solved, AMS 52]
theorem erdos_657.variants.straus (k : ℕ) :
    ∃ A : Finset (ℝ^k), A.card = 2 ^ k ∧ (A : Set (ℝ^k)).IsIsoscelesFree ∧
      distinctDistances A ≤ 2 ^ k - 1 := by
  sorry

end Erdos657
