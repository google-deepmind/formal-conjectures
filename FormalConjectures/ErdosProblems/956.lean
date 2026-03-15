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

open scoped Pointwise

/-!
# Erdős Problem 956

*Reference:* [erdosproblems.com/956](https://www.erdosproblems.com/956)

If $C, D \subseteq \mathbb{R}^2$ then the distance between $C$ and $D$ is defined by
$\delta(C, D) = \inf \{ \|c - d\| \mid c \in C, d \in D \}$.

Let $h(n)$ be the maximal number of unit distances between disjoint convex
translates. That is, the maximal $m$ such that there is a compact convex set
$C \subset \mathbb{R}^2$ and a set $X$ of size $n$ such that all $(C + x)_{x \in X}$ are disjoint
and there are $m$ pairs $x_1, x_2 \in X$ such that $\delta(C + x_1, C + x_2) = 1$.

[ErPa90] Erdős, P. and Pach, J., _Variations on the theme of repeated distances_,
Combinatorica **10** (1990), 261–269.
-/

namespace Erdos956

/-- The distance between two subsets of a metric space:
$\delta(C, D) = \inf \{ \operatorname{dist}(c, d) \mid c \in C, d \in D \}$. -/
noncomputable def setDist956 {α : Type*} [PseudoMetricSpace α]
    (C D : Set α) : ℝ :=
  sInf {r : ℝ | ∃ c ∈ C, ∃ d ∈ D, r = dist c d}

/--
**Erdős Problem 956** [ErPa90]:

There exists a constant $c > 0$ such that for all sufficiently large $n$,
one can find a compact convex set $C \subset \mathbb{R}^2$ and $n$ translation vectors whose
translates of $C$ are pairwise disjoint with more than $n^{1+c}$ pairs at
unit set-distance.
-/
@[category research open, AMS 5 52]
theorem erdos_956 :
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∃ (C : Set (EuclideanSpace ℝ (Fin 2))),
        IsCompact C ∧ Convex ℝ C ∧ C.Nonempty ∧
      ∃ (X : Finset (EuclideanSpace ℝ (Fin 2))),
        X.card = n ∧
        (∀ x₁ ∈ X, ∀ x₂ ∈ X, x₁ ≠ x₂ →
          Disjoint (C + {x₁}) (C + {x₂})) ∧
      ∃ (P : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))),
        (∀ p ∈ P, p.1 ∈ X ∧ p.2 ∈ X ∧ p.1 ≠ p.2 ∧
          setDist956 (C + {p.1}) (C + {p.2}) = 1) ∧
        (∀ p ∈ P, (p.2, p.1) ∉ P) ∧
        ((P.card : ℝ) > (n : ℝ) ^ ((1 : ℝ) + c)) := by
  sorry

/--
**Erdős Problem 956, upper bound** [ErPa90]:

$h(n) \ll n^{4/3}$. For any compact convex set $C$ and $n$ translations with
pairwise disjoint translates, the number of pairs at unit set-distance
is $O(n^{4/3})$.
-/
@[category research solved, AMS 5 52]
theorem erdos_956.variants.upper_bound :
    ∃ K : ℝ, K > 0 ∧
    ∀ (C : Set (EuclideanSpace ℝ (Fin 2))),
      IsCompact C → Convex ℝ C → C.Nonempty →
    ∀ (X : Finset (EuclideanSpace ℝ (Fin 2))),
      (∀ x₁ ∈ X, ∀ x₂ ∈ X, x₁ ≠ x₂ →
        Disjoint (C + {x₁}) (C + {x₂})) →
    ∀ (P : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))),
      (∀ p ∈ P, p.1 ∈ X ∧ p.2 ∈ X ∧ p.1 ≠ p.2 ∧
        setDist956 (C + {p.1}) (C + {p.2}) = 1) →
      (∀ p ∈ P, (p.2, p.1) ∉ P) →
      (P.card : ℝ) ≤ K * (X.card : ℝ) ^ ((4 : ℝ) / 3) := by
  sorry

end Erdos956
