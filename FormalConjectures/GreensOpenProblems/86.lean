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
# Ben Green's Open Problem 86

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.86)
- [KRS00] Konyagin, S. V., Ruzsa, I. Z. and Schlag, W., *On uniformly distributed dilates of
  finite integer sequences*. J. Number Theory 82 (2000), 165--187.
  [doi:10.1006/jnth.1999.2420](https://doi.org/10.1006/jnth.1999.2420)
- [Mo94] Montgomery, H. L., *Ten lectures on the interface between analytic number theory and
  harmonic analysis*. CBMS Regional Conference Series in Mathematics 84, American Mathematical
  Society (1994).
-/

@[expose] public section

open scoped Finset

namespace Green86

/--
`numInInterval A θ t` is the number of $a \in A$ such that $\theta a \pmod 1$ lies in the
interval $[t, t + 1/n)$ of $\mathbb{R}/\mathbb{Z}$, where $n = |A|$.
-/
noncomputable def numInInterval (A : Finset ℤ) (θ t : ℝ) : ℕ :=
  #{a ∈ A | Int.fract (θ * ((a : ℤ) : ℝ) - t) < 1 / (#A : ℝ)}

/--
An interval contains at most $|A|$ of the points, so `green_86` is trivially true for each
$c \ge 1$.
-/
@[category API, AMS 11]
theorem numInInterval_le_card (A : Finset ℤ) (θ t : ℝ) : numInInterval A θ t ≤ #A := by
  unfold numInInterval
  exact Finset.card_filter_le _ _

/--
Let $c > 0$. Let $A$ be a set of $n$ (distinct) integers. Does there exist $\theta$ such that
no interval of length $\frac{1}{n}$ in $\mathbb{R}/\mathbb{Z}$ contains more than $n^c$ of the
numbers $\theta a \pmod 1$, $a \in A$?

We read the question for every $c > 0$ and all $n \ge n_0(c)$. For small $n$ it can fail: for
$A = \{0, 1, 3\}$ and $3^c < 2$, three points with at most one in each interval of length
$1/3$ must be equally spaced, which is impossible. Intervals are half-open; for the question
over all $c > 0$ this does not matter, since a closed interval of length $1/n$ is covered by two
half-open ones. [Gr24] reports that the answer is yes for $c > 1/3$ [KRS00], and that
[Mo94, Problem 17 (4)] attributes the problem to Komlós and Ruzsa.
-/
@[category research open, question, AMS 11]
theorem green_86 :
    ∀ c : ℝ, 0 < c → ∃ n₀ : ℕ, ∀ A : Finset ℤ, n₀ ≤ #A →
      ∃ θ : ℝ, ∀ t : ℝ, (numInInterval A θ t : ℝ) ≤ (#A : ℝ) ^ c := by
  sorry

end Green86
