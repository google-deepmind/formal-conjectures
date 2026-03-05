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
$d_s(A + B) \geq \alpha + \alpha(1-\alpha)/k$. Proved by Plünnecke [Pl70].

[Pl70] Plünnecke, H., _Eine zahlentheoretische Anwendung der Graphentheorie_. J. Reine Angew.
Math. 243 (1970), 171–183.
-/

open Classical Finset BigOperators

namespace Erdos35

/-- The sumset $A + B$: the set of all $a + b$ with $a \in A$, $b \in B$. -/
def sumset (A B : Set ℕ) : Set ℕ := {n : ℕ | ∃ a ∈ A, ∃ b ∈ B, n = a + b}

/-- Schnirelmann density of a set $A \subseteq \mathbb{N}$:
$$d_s(A) = \inf_{N \geq 1} \frac{|A \cap \{1, \ldots, N\}|}{N}$$ -/
noncomputable def schnirelmannDensity (A : Set ℕ) : ℝ :=
  sInf {x : ℝ | ∃ N : ℕ, N ≥ 1 ∧ x = ((Icc 1 N).filter (· ∈ A)).card / (N : ℝ)}

/-- A set $B \subseteq \mathbb{N}$ is an additive basis of order $k$ if every natural number
can be written as a sum of exactly $k$ elements from $B$ (with repetition).
Since $0 \in B$ is assumed separately, "exactly $k$" is equivalent to "at most $k$". -/
def IsAdditiveBasis (B : Set ℕ) (k : ℕ) : Prop :=
  ∀ n : ℕ, ∃ f : Fin k → ℕ, (∀ i, f i ∈ B) ∧ ∑ i, f i = n

/--
Let $B \subseteq \mathbb{N}$ be an additive basis of order $k$ with $0 \in B$, and let
$\alpha = d_s(A)$ be the Schnirelmann density of $A \subseteq \mathbb{N}$. Then
$$d_s(A + B) \geq \alpha + \frac{\alpha(1 - \alpha)}{k}.$$

This was proved by Plünnecke [Pl70], who showed the stronger inequality
$d_s(A + B) \geq \alpha^{1-1/k}$, as observed by Ruzsa.
-/
@[category research solved, AMS 11]
theorem erdos_35
    (A B : Set ℕ) (k : ℕ) (hk : k ≥ 1)
    (hB : IsAdditiveBasis B k) (h0 : (0 : ℕ) ∈ B) :
    let α := schnirelmannDensity A
    schnirelmannDensity (sumset A B) ≥ α + α * (1 - α) / (k : ℝ) := by
  sorry

end Erdos35
