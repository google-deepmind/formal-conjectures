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
# Erdős Problem 669

*Reference:* [erdosproblems.com/669](https://www.erdosproblems.com/669)

Let $F_k(n)$ be minimal such that for any $n$ points in $\mathbb{R}^2$ there
exist at most $F_k(n)$ many distinct lines passing through at least $k$ of the
points, and $f_k(n)$ similarly but with lines passing through exactly $k$ points.

Estimate $f_k(n)$ and $F_k(n)$ — in particular, determine $\lim F_k(n)/n^2$
and $\lim f_k(n)/n^2$.

Trivially $f_k(n) \leq F_k(n)$ and $f_2(n) = F_2(n) = \binom{n}{2}$.
The problem with $k = 3$ is the classical 'Orchard problem' of Sylvester.
Burr, Grünbaum, and Sloane [BGS74] proved that $f_3(n) = n^2/6 - O(n)$ and
$F_3(n) = n^2/6 - O(n)$.

There is a trivial upper bound $F_k(n) \leq \binom{n}{2}/\binom{k}{2}$,
hence $\lim F_k(n)/n^2 \leq 1/(k(k-1))$.

A problem of Erdős [Er97f]. See also problem \#101.

[Er97f] Erdős, P., _Some of my new and almost new problems and results in
combinatorial geometry_. (1997).

[BGS74] Burr, S. A., Grünbaum, B., and Sloane, N. J. A., _The orchard problem_.
Geometriae Dedicata (1974).
-/

open Classical

namespace Erdos669

/-- The number of affine lines in $\mathbb{R}^2$ passing through at least $k$ points
from a finite point set $P$. -/
noncomputable def atLeastKPointLineCount
    (P : Finset (EuclideanSpace ℝ (Fin 2))) (k : ℕ) : ℕ :=
  Set.ncard {L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) |
    Module.finrank ℝ L.direction = 1 ∧
    k ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L}}

/-- The number of affine lines in $\mathbb{R}^2$ passing through exactly $k$ points
from a finite point set $P$. -/
noncomputable def exactlyKPointLineCount
    (P : Finset (EuclideanSpace ℝ (Fin 2))) (k : ℕ) : ℕ :=
  Set.ncard {L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) |
    Module.finrank ℝ L.direction = 1 ∧
    Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L} = k}

/-- $F_k(n)$: the maximum over all $n$-point sets $P \subseteq \mathbb{R}^2$ of the number of
lines passing through at least $k$ points of $P$. -/
noncomputable def bigF (k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
    P.card = n ∧ atLeastKPointLineCount P k = m}

/-- $f_k(n)$: the maximum over all $n$-point sets $P \subseteq \mathbb{R}^2$ of the number of
lines passing through exactly $k$ points of $P$. -/
noncomputable def littleF (k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
    P.card = n ∧ exactlyKPointLineCount P k = m}

/--
**Erdős Problem 669, Part 1** [Er97f]:

The limit $\lim_{n \to \infty} F_k(n)/n^2$ exists for all $k \geq 2$.
-/
@[category research open, AMS 5 52]
theorem erdos_669 (k : ℕ) (hk : k ≥ 2) :
    ∃ L : ℝ, ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        |((bigF k n : ℝ) / (n : ℝ) ^ 2) - L| ≤ ε := by
  sorry

/--
**Erdős Problem 669, Part 2** [Er97f]:

The limit $\lim_{n \to \infty} f_k(n)/n^2$ exists for all $k \geq 2$.
-/
@[category research open, AMS 5 52]
theorem erdos_669.variants.littleF_limit_exists (k : ℕ) (hk : k ≥ 2) :
    ∃ L : ℝ, ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        |((littleF k n : ℝ) / (n : ℝ) ^ 2) - L| ≤ ε := by
  sorry

/--
**Erdős Problem 669, trivial upper bound**:

$F_k(n) \leq n(n-1)/(k(k-1))$ for all $n$ and $k \geq 2$.
This follows from $F_k(n) \leq \binom{n}{2}/\binom{k}{2}$ since each line
through at least $k$ points accounts for at least $\binom{k}{2}$ pairs.
-/
@[category undergraduate, AMS 5 52]
theorem erdos_669.variants.trivial_bound (k : ℕ) (hk : k ≥ 2) (n : ℕ) :
    (bigF k n : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) / ((k : ℝ) * ((k : ℝ) - 1)) := by
  sorry

end Erdos669
