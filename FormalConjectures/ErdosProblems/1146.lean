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
# Erdős Problem 1146

*References:*
- [erdosproblems.com/1146](https://www.erdosproblems.com/1146)
- [Ru99] Ruzsa, I., Erdős and the Integers. Journal of Number Theory (1999), 115-163.
-/

open Classical
open scoped Pointwise

namespace Erdos1146

/--
We say that $A\subset \mathbb{N}$ is an essential component if $d_s(A \oplus B)>d_s(B)$ for every
$B\subset \mathbb{N}$ with $0<d_s(B)<1$ where $d_s$ is the Schnirelmann density.
Here, the sumset is the appropriate one for Schnirelmann density, $A \oplus B = \{a+b \mid a \in A \cup \{0\}, b \in B \cup \{0\}\}$ (i.e. $(A \cup \{0\}) + (B \cup \{0\})$).
This avoids the trivial case where the sumset misses $1$ simply because neither $A$ nor $B$ contains $0$.
-/
def IsEssentialComponent (A : Set ℕ) : Prop :=
  ∀ B : Set ℕ,
    let b := schnirelmannDensity B;
    0 < b → b < 1 → schnirelmannDensity ((A ∪ {0}) + (B ∪ {0})) > b

/--
Is $B=\{2^m3^n : m,n\geq 0\}$ an essential component?

In [Ru99] Ruzsa states "The simplest set with a chance to be an essential component is the
collection of numbers in the form $2^m3^n$ and Erdős often asked whether it is an essential
component or not; I do not even have a plausible guess."
-/
@[category research open, AMS 11]
theorem erdos_1146 :
    answer(sorry) ↔ IsEssentialComponent { k | ∃ m n : ℕ, k = 2 ^ m * 3 ^ n } := by
  sorry

end Erdos1146
