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
public import FormalConjectures.ErdosProblems.«211»

/-!
# Erdős Problem 1069

*References:*
- [erdosproblems.com/1069](https://www.erdosproblems.com/1069)
- [Er87b] Erdős, P., *Some combinatorial and metric problems in geometry*. Intuitive geometry
  (Siófok, 1985) (1987), 167-177.
- [Sa87] Sah, C.-H., *The rich line problem of P. Erdős*. (1987), 123-125.
- [SzTr83] Szemerédi, E. and Trotter, Jr., W. T., *Extremal problems in discrete geometry*.
  Combinatorica (1983), 381-392.
-/

@[expose] public section

open EuclideanGeometry

namespace Erdos1069

/-- The $k$-rich lines of a finite set `s` of points in the plane: the lines of `ℝ²` which
contain at least $k$ points of `s`. -/
def richLines (s : Finset ℝ²) (k : ℕ) : Set (AffineSubspace ℝ ℝ²) :=
  {L | IsLine L ∧ k ≤ ((s : Set ℝ²) ∩ (L : Set ℝ²)).ncard}

/-- For $k \geq 2$ there are only finitely many $k$-rich lines, since each is spanned by two of
the points, so `Set.ncard` counts them. -/
@[category API, AMS 5 52]
theorem richLines_finite (s : Finset ℝ²) {k : ℕ} (hk : 2 ≤ k) : (richLines s k).Finite := by
  refine (Erdos211.determinedLines s).finite_toSet.subset ?_
  rintro L ⟨hL, hcard⟩
  exact Finset.mem_coe.2 (Erdos211.determinedLines_eq.2 ⟨hL, hk.trans hcard⟩)

/--
Given any $n$ points in $\mathbb{R}^2$, the number of $k$-rich lines (lines which contain
$\geq k$ of the points) is, provided $k\leq n^{1/2}$,
$$\ll \frac{n^2}{k^3}.$$

Erdős [Er87b] describes this as a conjecture of himself, Croft, and Purdy. It was proved by
Szemerédi and Trotter [SzTr83]. We take $k \geq 2$, since for $k \leq 1$ there are infinitely
many $k$-rich lines.
-/
@[category research solved, AMS 5 52]
theorem erdos_1069 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ) (s : Finset ℝ²), s.card = n → 2 ≤ k →
      (k : ℝ) ≤ Real.sqrt n →
        ((richLines s k).ncard : ℝ) ≤ C * (n : ℝ) ^ 2 / (k : ℝ) ^ 3 := by
  sorry

/--
When $k=n^{1/2}$ the lattice points show that there can be $\geq(2+o(1))n^{1/2}$ many
$n^{1/2}$-rich lines: for $n=m^2$ the $m\times m$ grid has $2m$ lines with $m$ points each.
Erdős thought that perhaps this is best possible, but Sah [Sa87] gave a construction achieving
$\geq (3+o(1))n^{1/2}$ many $n^{1/2}$-rich lines.
-/
@[category textbook, AMS 5 52]
theorem erdos_1069.variants.lattice (m : ℕ) (hm : 2 ≤ m) :
    ∃ s : Finset ℝ², s.card = m ^ 2 ∧ 2 * m ≤ (richLines s m).ncard := by
  sorry

end Erdos1069
