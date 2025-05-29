/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 477

*Reference:* [erdosproblems.com/477](https://www.erdosproblems.com/477)
-/
/--
Let $f: \mathbb{Z} \rightarrow \mathbb{Z}$ be a polynomial of degree at least $2$.

Is there a set $A$ such that every $z \in \mathbb{Z}$ has exactly one representation as $z = a + f(n)$ for some $a \in A$ and $n \in \mathbb{Z}$?
-/
@[category research open, AMS 12]
theorem erdos_477 (f : Polynomial ℤ) (hf₀ : 2 ≤ f.degree) : ∃ (A : Set ℤ),
    ∀ z, ∃! a ∈ A ×ˢ Set.range f.eval, z = a.1 + a.2 := sorry

/--
Probably there is no such $A$ for any polynomial $f$.
-/
@[category research open, AMS 12]
theorem erdos_477.variants.strong_negation (f : Polynomial ℤ) (hf₀ : 2 ≤ f.degree) : ¬ ∃ (A : Set ℤ),
    ∀ z, ∃! a ∈ A ×ˢ Set.range f.eval, z = a.1 + a.2 := sorry
