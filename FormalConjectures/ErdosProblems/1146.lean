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
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Erdős Problem 1146

Erdős asked whether the set of 3-smooth numbers {2^m · 3^n : m, n ≥ 0} is an essential component
with respect to Schnirelmann density. 3-smooth numbers are not lacunary, so Ruzsa's result
that lacunary sets cannot be essential components (see Problem 37) does not rule them out;
this makes them "the simplest set with a chance" to be an essential component.

*Reference:* [erdosproblems.com/1146](https://www.erdosproblems.com/1146)

*See also:* Problem 37.

[Va99] Ruzsa, I. Z., *Sumsets and structure*, Combinatorial Number Theory and Additive
Group Theory (1999).

[Ru99] Ruzsa, I., *Erdős and the Integers*. Journal of Number Theory (1999), 115-163.
-/

open Classical
open scoped Pointwise

namespace Erdos1146

/--
The Schnirelmann density of a set $A \subseteq \mathbb{N}$, defined as
$$d_s(A) = \inf_{n \geq 1} \frac{|A \cap \{1,\ldots,n\}|}{n}.$$
-/
noncomputable def schnirelmannDensity (A : Set ℕ) : ℝ :=
  ⨅ n : ℕ+, (((Finset.Icc 1 (n : ℕ)).filter (· ∈ A)).card : ℝ) / ((n : ℕ) : ℝ)

/--
A set $A \subseteq \mathbb{N}$ is an essential component if $d_s(A + B) > d_s(B)$ for every
$B \subseteq \mathbb{N}$ with $0 < d_s(B) < 1$, where $d_s$ is the Schnirelmann density.
-/
def IsEssentialComponent (A : Set ℕ) : Prop :=
  ∀ (B : Set ℕ), 0 < schnirelmannDensity B → schnirelmannDensity B < 1 →
    schnirelmannDensity (A + B) > schnirelmannDensity B

/--
The set of 3-smooth numbers: $\{2^m \cdot 3^n \mid m, n \geq 0\}$.
-/
def smoothNumbers23 : Set ℕ :=
  {k | ∃ m n : ℕ, k = 2 ^ m * 3 ^ n}

/--
Erdős Problem 1146 [Va99, 1.19]:
Is the set $B = \{2^m \cdot 3^n : m, n \geq 0\}$ an essential component?

A set $A \subseteq \mathbb{N}$ is an essential component if $d_s(A + B) > d_s(B)$ for every
$B \subseteq \mathbb{N}$ with $0 < d_s(B) < 1$, where $d_s$ is the Schnirelmann density.

Ruzsa states: "The simplest set with a chance to be an essential component is
the collection of numbers in the form $2^m \cdot 3^n$ and Erdős often asked whether
it is an essential component or not."
-/
@[category research open, AMS 11]
theorem erdos_1146 : answer(sorry) ↔ IsEssentialComponent smoothNumbers23 := by
  sorry

end Erdos1146
