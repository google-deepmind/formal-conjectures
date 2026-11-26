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
# Erdős Problem 662: a global threshold variant

*References:*
- [erdosproblems.com/662](https://www.erdosproblems.com/662)
- [Er97e] Erdős, Paul, *Some of my favourite unsolved problems*.
  Math. Japon. (1997), 527–537.
- [Snyder / Star Fleet](https://github.com/AItoBit/erdos-662-proof),
  *A global threshold counterexample for Erdős Problem 662*.
-/

@[expose] public section

namespace Erdos662

/-- Euclidean distance in the real plane. -/
noncomputable def euclideanDistance (x y : ℝ × ℝ) : ℝ :=
  Real.sqrt ((x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2)

/-- The number of nonzero unit triangular-lattice vectors of length at most `t`.
The lattice basis is $(1,0)$ and $(1/2,\sqrt{3}/2)$, so the squared length of
the vector with integer coordinates $(a,b)$ is $a^2+ab+b^2$. -/
noncomputable def triangularNeighborCount (t : ℝ) : ℕ :=
  Nat.card {d : ℤ × ℤ // d ≠ (0, 0) ∧
    (d.1 : ℝ) ^ 2 + (d.1 : ℝ) * (d.2 : ℝ) + (d.2 : ℝ) ^ 2 ≤ t ^ 2}

/-- Every two distinct indexed points are at Euclidean distance at least one. -/
def OneSeparated {α : Type*} (p : α → ℝ × ℝ) : Prop :=
  ∀ i j, i ≠ j → 1 ≤ euclideanDistance (p i) (p j)

/-- Directed pairs of distinct indexed points at Euclidean distance at most `t`.
Each unordered pair contributes twice. -/
noncomputable def closeDirectedPairs {α : Type*} [Fintype α] [DecidableEq α]
    (t : ℝ) (p : α → ℝ × ℝ) : Finset (α × α) := by
  classical
  exact (Finset.univ.product Finset.univ).filter fun q =>
    q.1 ≠ q.2 ∧ euclideanDistance (p q.1) (p q.2) ≤ t

/-- For every radius $t\geq1$, there is a cutoff $N(t)$ such that every
one-separated indexed planar configuration with $n\geq N(t)$ points has at most
$n f(t)$ directed pairs at distance at most $t$, where $f(t)$ is the number of
nonzero unit triangular-lattice vectors of length at most $t$. -/
def GlobalThresholdConjecture : Prop :=
  ∀ t : ℝ, 1 ≤ t → ∃ N : ℕ, ∀ (α : Type) [Fintype α] [DecidableEq α],
    N ≤ Fintype.card α → ∀ p : α → ℝ × ℝ,
      OneSeparated p →
        (closeDirectedPairs t p).card ≤ triangularNeighborCount t * Fintype.card α

/-- A corrected global threshold variant of [Er97e, p. 532]. For the unit
triangular lattice, let $f(t)$ count the nonzero lattice vectors of length at most
$t$. Is it true that, for every $t\geq1$, all sufficiently large one-separated
planar configurations of $n$ points have at most $n f(t)$ directed pairs at
distance at most $t$?

This variant inserts the factor $n$ missing from the printed global comparison
and uses closed Euclidean thresholds. In this convention $f(3)=36$, rather than
the printed $18$; $f(2)=18$. This is an explicit reconstruction of the ambiguous
printed question. Colin Snyder / Star Fleet disproved this
variant using radius $6$ and arbitrarily large finite configurations. -/
@[category research solved, question, AMS 52, formal_proof using lean4 at
  "https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Solution.lean"]
theorem erdos_662.variants.global_threshold : ¬ GlobalThresholdConjecture := by
  sorry

end Erdos662
