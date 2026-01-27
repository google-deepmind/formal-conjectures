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
import FormalConjectures.Util.ProblemImports

/-!
# Ben Green's Open Problem 62

More commonly known as the **no-three-in-line problem**.

Given $N \lt 2$ and a more than $2 * N$ points on an $N \times N$-grid,
are there $3$ of the points on a common line?

*References:*
- [Ben Green's Open Problem 62](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.62)
- [Wikipedia](https://en.wikipedia.org/wiki/No-three-in-line_problem)
- [GK2025] Grebennikov, A. Kwan, M. No $(k + 1)$-in-line problem for large constant $k$.
  https://arxiv.org/abs/2510.17743
-/

namespace Green72

/-- We say a subset of $[N]^2$ is allowed for some $k$ if it contains no $k$ points
which lie on a common line. -/
structure AllowedSet (k : ℕ) (N : ℕ) (s : Finset (ℕ × ℕ)) : Prop where
  is_bounded : ∀ i ∈ s, i.1 < N ∧ i.2 < N
  not_collinear : ∀ ⦃t : Finset (ℕ × ℕ)⦄, t ⊆ s → t.card = k →
    Collinear ℝ ({r | ∃ i ∈ s, r = ((↑i.1 : ℝ), (↑i.2 : ℝ))} : Set (ℝ × ℝ))

/-- The maximal size of an allowed set -/
noncomputable def AllowedSetSize (k : ℕ) (N : ℕ) : ℕ :=
  sSup {r | ∃ s, r = s.card ∧ AllowedSet N k s}

/-- By the pigeon hole principle, the size of a subset of an $N \times N$ grid such that no $k$
points lie on a line is bounded by $\leq (k - 1) * N$ for $N \geq k$. -/
@[category high_school, AMS 05 52]
theorem allowedSetSize_le {k : ℕ} {N : ℕ} (h : k ≤ N) :
    AllowedSetSize k N ≤ (k - 1) * N := by
  sorry

/-- $N, k$ when the AllowedSetSize of $N$ for $k$ is $k * N$. -/
def NoKInLineFor (k : ℕ) (N : ℕ) : Prop :=
  AllowedSetSize k N = (k - 1) * N

/-- The **no-k-in-line problem**:
For $N \geq k$ and $k > 1$, the AllowedSetSize in $(k - 1) * N$, i. e. on an $N \times N$ subset,
there is a set of $k * N$ points for which no $k$ lie on a line (and not such a set of bigger size).
-/
@[category research open, AMS 05 52]
theorem NoKInLine {k : ℕ} {N : ℕ} (hk : 1 < k) (h : k ≤ N) : NoKInLineFor k N := by
  sorry

/-- **Green's Open Problem 62 / No-three-in-line problem**:
The no-k-in-line conjecture holds for $k = 3$. -/
@[category research open, AMS 05 52]
theorem green_62 {N : ℕ} (hN : 3 ≤ N) : NoKInLineFor 3 N := by
  sorry

alias no_three_in_line := green_62

/-- Does the no-three-in-line problem hold when $N$ is big enough? -/
@[category research open, AMS 05 52]
theorem green_62.variants.eventually : ∀ᶠ N in Filter.atTop, NoKInLineFor 3 N := by
  sorry

/-- For $N \leq 60$, this has been verfied with computers. -/
@[category research solved, AMS 05 52]
theorem no_three_in_line_le {N : ℕ} (hN : 3 ≤ N) (hN' : N ≤ 60) :
    NoKInLineFor 3 N := by
  sorry

/-- In [GK2025] Grebennikov and Kwan prove the no-k-in-line conjecture for $k > 10 ^ 37$. -/
@[category research solved, AMS 05 52]
theorem no_k_in_line_big {k : ℕ} (N : ℕ) (h : 10 ^ 37 < k) :
    NoKInLineFor k N := by
  sorry

-- TODO: Add lower bound for no-three-in-line

end Green72
