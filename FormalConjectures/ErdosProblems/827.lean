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
# Erdős Problem 827

*Reference:* [erdosproblems.com/827](https://www.erdosproblems.com/827)

Let $n_k$ be minimal such that if $n_k$ points in $\mathbb{R}^2$ are in general
position then there exists a subset of $k$ points such that all $\binom{k}{3}$
triples determine circles of different radii.

Erdős [Er75h] asked whether $n_k$ exists. In [Er78c] he gave a simple argument
proving existence, but the argument was incorrect as noted by Martinez and
Roldán-Pensado [MaRo15]. A corrected argument gives $n_k \ll k^9$.
-/

open Finset

namespace Erdos827

/-- Points in $\mathbb{R}^2$ are in general position if no three are collinear. -/
def InGeneralPosition (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ P → S.card = 3 → ¬Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2)))

/-- The circumradius of three points in $\mathbb{R}^2$, defined via Heron's formula.
    For a non-degenerate triangle with side lengths $a$, $b$, $c$ and semiperimeter
    $s = (a+b+c)/2$, the circumradius is $R = \frac{abc}{4\sqrt{s(s-a)(s-b)(s-c)}}$.
    Returns $0$ for degenerate (collinear) configurations. -/
noncomputable def circumradius (p₁ p₂ p₃ : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  let a := dist p₁ p₂
  let b := dist p₂ p₃
  let c := dist p₁ p₃
  let s := (a + b + c) / 2
  let area_sq := s * (s - a) * (s - b) * (s - c)
  if area_sq > 0 then
    (a * b * c) / (4 * Real.sqrt area_sq)
  else 0

/-- All $\binom{k}{3}$ triples of distinct points in $S$ determine circles of pairwise
    distinct radii. -/
def AllDistinctCircumradii (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
  ∀ d ∈ S, ∀ e ∈ S, ∀ f ∈ S,
    a ≠ b → a ≠ c → b ≠ c →
    d ≠ e → d ≠ f → e ≠ f →
    ({a, b, c} : Finset _) ≠ ({d, e, f} : Finset _) →
    circumradius a b c ≠ circumradius d e f

/--
**Erdős Problem 827** [Er75h, Er78c, Er92e]:

For every $k \geq 3$, there exists $n$ such that any set of $n$ points in
$\mathbb{R}^2$ in general position contains a $k$-element subset whose
$\binom{k}{3}$ triples all determine circumscribed circles of pairwise
different radii.

Martinez and Roldán-Pensado [MaRo15] proved this with $n \leq C \cdot k^9$.
-/
@[category research solved, AMS 5 51]
theorem erdos_827 (k : ℕ) (hk : k ≥ 3) :
    ∃ n : ℕ, ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
      P.card ≥ n →
      InGeneralPosition P →
      ∃ S : Finset (EuclideanSpace ℝ (Fin 2)),
        S ⊆ P ∧ S.card = k ∧ AllDistinctCircumradii S := by
  sorry

end Erdos827
