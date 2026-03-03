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
# Erdős Problem 3

*Reference:* [erdosproblems.com/3](https://www.erdosproblems.com/3)
-/

namespace Erdos3

/--
If $A \subset \mathbb{N} has $\sum_{n \in A}\frac 1 n = \infty$, then must $A$ contain arbitrarily
long arithmetic progressions?
-/
@[category research open, AMS 11]
theorem erdos_3 : answer(sorry) ↔ ∀ A : Set ℕ,
    (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
    ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k := by
  sorry

/--
Green and Tao [GT08] proved that the set of primes contains arbitrarily long arithmetic
progressions. Bloom and Sisask [BS20] proved that any set of positive integers with divergent
reciprocal sum contains a 3-term arithmetic progression, resolving the k=3 case.

[GT08] Green, B. and Tao, T., _The primes contain arbitrarily long arithmetic progressions_.
Annals of Mathematics (2008), 481-547.
[BS20] Bloom, T. F. and Sisask, O., _Breaking the logarithmic barrier in Roth's theorem on
arithmetic progressions_. arXiv:2007.03528 (2020).
-/
@[category research formally solved using formal_conjectures at "https://www.erdosproblems.com/3", AMS 11]
theorem erdos_3.variants.bloom_sisask :
    ∀ A : Set ℕ, (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
    ∃ S ⊆ A, S.IsAPOfLength 3 := by
  sorry

end Erdos3
