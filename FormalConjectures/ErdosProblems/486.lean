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
# Erdős Problem 486: Logarithmic density for sets avoiding modular subsets

For each $n \in \mathbb{N}$ choose some $X_n \subseteq \mathbb{Z}/n\mathbb{Z}$.
Let $B = \{m \in \mathbb{N} : \forall n, m \not\equiv x \pmod{n} \text{ for all } x \in X_n\}$.
Must $B$ have a logarithmic density?

*Reference:* [erdosproblems.com/486](https://www.erdosproblems.com/486)
-/

namespace Erdos486

/--
**Erdős Problem 486**

For each $n \in \mathbb{N}$ choose some $X_n \subseteq \mathbb{Z}/n\mathbb{Z}$.
Let $B = \{m \in \mathbb{N} : \forall n, m \not\equiv x \pmod{n} \text{ for all } x \in X_n\}$.
Must $B$ have a logarithmic density?
-/
@[category research open, AMS 11]
theorem erdos_486 : answer(sorry) ↔
    ∀ X : (n : ℕ) → Set (ZMod n), ∃ d, {m : ℕ | ∀ n, (m : ZMod n) ∉ X n}.HasLogDensity d := by
  sorry

end Erdos486
