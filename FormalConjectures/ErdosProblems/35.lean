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
# Erdős Problem 35

*Reference:* [erdosproblems.com/35](https://www.erdosproblems.com/35)

If $B$ is an additive basis of order $k$ and $A$ has Schnirelmann density $\alpha$, then
$d_s(A + B) \geq \alpha + \alpha(1-\alpha)/k$. Erdős [Er36c] proved the result with $2k$ in
the denominator. Plünnecke [Pl70] proved the stronger inequality
$d_s(A + B) \geq \alpha^{1-1/k}$, as observed by Ruzsa.

See also Problem 38.

[Er36c] Erdős, P., _On the arithmetical density of the sum of two sequences, one of which
forms a basis for the integers_. Acta Arith. (1936), 201-207.

[Er56] Erdős, P., _Problems and results in additive number theory_. Colloque sur la Théorie
des Nombres, Bruxelles, 1955 (1956), 127-137.

[Pl70] Plünnecke, H., _Eine zahlentheoretische Anwendung der Graphentheorie_. J. Reine Angew.
Math. 243 (1970), 171–183.
-/

open Classical Finset
open scoped Pointwise

namespace Erdos35

/-- Schnirelmann density of a set $A \subseteq \mathbb{N}$:
$$d_s(A) = \inf_{N \geq 1} \frac{|A \cap \{1, \ldots, N\}|}{N}$$ -/
noncomputable def schnirelmannDensity (A : Set ℕ) : ℝ :=
  sInf {x : ℝ | ∃ N : ℕ, N ≥ 1 ∧ x = ((Icc 1 N).filter (· ∈ A)).card / (N : ℝ)}

/--
Let $B \subseteq \mathbb{N}$ be an additive basis of order $k$ and let
$\alpha = d_s(A)$ be the Schnirelmann density of $A \subseteq \mathbb{N}$. Then
$$d_s(A + B) \geq \alpha + \frac{\alpha(1 - \alpha)}{k}.$$

This was proved by Plünnecke [Pl70], who showed the stronger inequality
$d_s(A + B) \geq \alpha^{1-1/k}$, as observed by Ruzsa.
-/
@[category research solved, AMS 11]
theorem erdos_35
    (A B : Set ℕ) (k : ℕ) (hk : k ≥ 1)
    (hB : B.IsAddBasisOfOrder k) :
    let α := schnirelmannDensity A
    schnirelmannDensity (A + B) ≥ α + α * (1 - α) / (k : ℝ) := by
  sorry

/--
Plünnecke's strengthening of Erdős Problem 35: if $B$ is an additive basis of order $k$
and $\alpha = d_s(A)$, then $d_s(A + B) \geq \alpha^{1-1/k}$. This implies the bound
$\alpha + \alpha(1-\alpha)/k$ from the main problem.
-/
@[category research solved, AMS 11]
theorem erdos_35_plunnecke
    (A B : Set ℕ) (k : ℕ) (hk : k ≥ 1)
    (hB : B.IsAddBasisOfOrder k) :
    let α := schnirelmannDensity A
    schnirelmannDensity (A + B) ≥ α ^ (1 - 1 / (k : ℝ)) := by
  sorry

end Erdos35
