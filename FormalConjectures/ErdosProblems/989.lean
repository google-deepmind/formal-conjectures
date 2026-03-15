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
# Erdős Problem 989

*Reference:* [erdosproblems.com/989](https://www.erdosproblems.com/989)

If $A = \{z_1, z_2, \ldots\} \subset \mathbb{R}^2$ is an infinite sequence then let
$$
  f(r) = \sup_C \left| |A \cap C| - \pi r^2 \right|,
$$
where the supremum is over all closed disks $C$ of radius $r$.

Is $f(r)$ unbounded for every $A$? How fast does $f(r)$ grow?

This was settled by Beck [Be87], who proved that $f(r) \gg r^{1/2}$ for all $A$,
and there exists $A$ such that $f(r) \ll (r \log r)^{1/2}$.

[Er64b] Erdős, P., _Problems and results on diophantine approximations_.
Compositio Math. (1964), 52–65.

[Be87] Beck, J., _Irregularities of distribution. I_, Acta Math. 159 (1987), 1–49.
-/

namespace Erdos989

/-- Euclidean distance in $\mathbb{R}^2$. -/
noncomputable def euclidDist (p q : ℝ × ℝ) : ℝ :=
  Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

/-- A sequence is locally finite if every closed disk contains only finitely
many terms of the sequence. -/
def IsLocallyFinite (A : ℕ → ℝ × ℝ) : Prop :=
  ∀ (c : ℝ × ℝ) (r : ℝ), Set.Finite {i : ℕ | euclidDist (A i) c ≤ r}

/-- Number of terms of $A$ in the closed disk centered at $c$ with radius $r$. -/
noncomputable def countInDisk (A : ℕ → ℝ × ℝ) (c : ℝ × ℝ) (r : ℝ) : ℕ :=
  Set.ncard {i : ℕ | euclidDist (A i) c ≤ r}

/-- The discrepancy $f(r) = \sup_c \left| |A \cap \mathrm{disk}(c,r)| - \pi r^2 \right|$. -/
noncomputable def discrepancy (A : ℕ → ℝ × ℝ) (r : ℝ) : ℝ :=
  ⨆ (c : ℝ × ℝ), |↑(countInDisk A c r) - Real.pi * r ^ 2|

/--
Erdős Problem 989, Beck's lower bound [Be87]:
For every locally finite sequence $A$ in $\mathbb{R}^2$, there exists $C > 0$ such that
for all sufficiently large $r$, there exists a center $c$ with
$\left| |A \cap \mathrm{disk}(c,r)| - \pi r^2 \right| \geq C \cdot \sqrt{r}$.
In particular, $f(r)$ is unbounded for every such $A$.

This is formulated existentially over the center $c$ rather than using `discrepancy`
(which takes a supremum via `⨆` on `ℝ`) to avoid the issue that `iSup` on a
`ConditionallyCompleteLattice` requires `BddAbove`, which may not hold.
-/
@[category research solved, AMS 11]
theorem erdos_989 (A : ℕ → ℝ × ℝ) (hA : IsLocallyFinite A) :
    ∃ C : ℝ, C > 0 ∧ ∃ R₀ : ℝ, ∀ r : ℝ, r ≥ R₀ →
      ∃ c : ℝ × ℝ, |↑(countInDisk A c r) - Real.pi * r ^ 2| ≥ C * Real.sqrt r := by
  sorry

/--
Erdős Problem 989, Beck's upper bound [Be87]:
There exists a locally finite sequence $A$ in $\mathbb{R}^2$ and $C > 0$ such that
for all sufficiently large $r$ and all centers $c$,
$\left| |A \cap \mathrm{disk}(c,r)| - \pi r^2 \right| \leq C \cdot \sqrt{r \cdot \log r}$.

This is formulated universally over the center $c$ rather than using `discrepancy`
(which takes a supremum via `⨆` on `ℝ`) to avoid the issue that `iSup` on a
`ConditionallyCompleteLattice` requires `BddAbove`.
-/
@[category research solved, AMS 11]
theorem erdos_989.variants.upper_bound :
    ∃ (A : ℕ → ℝ × ℝ), IsLocallyFinite A ∧
    ∃ C : ℝ, C > 0 ∧ ∃ R₀ : ℝ, ∀ r : ℝ, r ≥ R₀ →
      ∀ c : ℝ × ℝ,
        |↑(countInDisk A c r) - Real.pi * r ^ 2| ≤ C * Real.sqrt (r * Real.log r) := by
  sorry

end Erdos989
