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
# Erdős Problem 958

*Reference:* [erdosproblems.com/958](https://www.erdosproblems.com/958)

Let $A \subset \mathbb{R}^2$ be a finite set of size $n$, and let $\{d_1, \ldots, d_k\}$
be the set of distinct distances determined by $A$. Let $f(d)$ be the multiplicity of $d$,
the number of unordered pairs from $A$ at distance $d$ apart.

Is it true that $k = n - 1$ and $\{f(d_i)\} = \{1, \ldots, n-1\}$ if and only if $A$ is
a set of equidistant points on a line or a circle?

Erdős conjectured that the answer is no, and other such configurations exist [Er84c].

This was proved by Clemen, Dumitrescu, and Liu [CDL25], who observed that equidistant
points on a short circular arc on a circle of radius 1, together with the centre, provide
a counterexample.

[Er84c] Erdős, P., _Some old and new problems in combinatorial geometry_,
Convexity and graph theory (Jerusalem, 1981), 1984, pp. 129–136.

[CDL25] Clemen, F., Dumitrescu, A., and Liu, D., _On multiplicities of interpoint distances_.
arXiv:2505.04283 (2025).
-/

namespace Erdos958

/-- The set of distinct distances determined by a finite point set in $\mathbb{R}^2$. -/
noncomputable def distinctDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : Finset ℝ :=
  (A.offDiag).image (fun p => dist p.1 p.2)

/-- The number of unordered pairs in $A$ at distance $d$. -/
noncomputable def distMultiplicity (A : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) : ℕ :=
  (A.offDiag.filter (fun p => dist p.1 p.2 = d)).card / 2

/-- The distance multiplicity property: $A$ has exactly $n-1$ distinct distances and the
multiplicities are exactly $\{1, 2, \ldots, n-1\}$. -/
def HasDistanceMultiplicityProperty (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  A.card ≥ 2 ∧
  (distinctDistances A).card = A.card - 1 ∧
  ∀ m : ℕ, (1 ≤ m ∧ m ≤ A.card - 1) ↔
    (∃ d ∈ distinctDistances A, distMultiplicity A d = m)

/-- A finite point set is equidistant-collinear if the points are equally spaced along a
line: $A = \{p, p + v, p + 2v, \ldots, p + (n-1)v\}$ for some $p, v$ with $v \neq 0$. -/
def IsEquidistantCollinear (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ (p v : EuclideanSpace ℝ (Fin 2)), v ≠ 0 ∧
    ∀ a ∈ A, ∃ i : Fin A.card, a = p + (i.val : ℝ) • v

/-- A finite point set is equidistant-circular if the points are equally spaced on a
circle: all points lie on a circle and consecutive points in a cyclic ordering have
equal Euclidean distance. -/
def IsEquidistantCircular (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  A.card ≥ 3 ∧
  ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ), r > 0 ∧
    (∀ a ∈ A, dist a c = r) ∧
    ∃ (σ : ℕ → EuclideanSpace ℝ (Fin 2)),
      (∀ i, i < A.card → σ i ∈ A) ∧
      (∀ a ∈ A, ∃ i, i < A.card ∧ σ i = a) ∧
      (∀ i j, i < A.card → j < A.card → σ i = σ j → i = j) ∧
      ∀ i, i < A.card →
        dist (σ i) (σ ((i + 1) % A.card)) = dist (σ 0) (σ 1)

/--
**Erdős Problem 958** [Er84c]:

Is it true that if a finite set $A \subset \mathbb{R}^2$ satisfies the distance multiplicity
property (exactly $n-1$ distinct distances with multiplicities $\{1, \ldots, n-1\}$), then $A$
must be a set of equidistant points on a line or equidistant points on a circle?

The answer is no. This was proved by Clemen, Dumitrescu, and Liu [CDL25].
-/
@[category research solved, AMS 5 52]
theorem erdos_958 : answer(False) ↔
    (∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
      HasDistanceMultiplicityProperty A →
      (IsEquidistantCollinear A ∨ IsEquidistantCircular A)) := by
  sorry

end Erdos958
