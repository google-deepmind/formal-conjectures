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
# Erdős Problem 590

*References:*
 - [erdosproblems.com/591](https://www.erdosproblems.com/590)
 - [Ch72] Chang, C. C., A partition theorem for the complete graph on {$\omega\sp{\omega }$}. J. Combinatorial Theory Ser. A (1972), 396-452.
 - [Sp57] Specker, Ernst, Teilmengen von Mengen mit Relationen. Comment. Math. Helv. (1957), 302-314.
 - [La73] Larson, Jean A., A short proof of a partition theorem for the ordinal {$\omega \sp{\omega }$}. Ann. Math. Logic (1973/74), 129-145.
-/

open Cardinal Ordinal

universe u

/--
Let $α$ be the infinite ordinal $\omega^{\omega}$. It was proved by Chang [Ch72] that any red/blue
colouring of the edges of $K_α$ there is either a red $K_α$ or a blue $K_3$.
-/
@[category research solved, AMS 3]
theorem erdos_590 : OmegaPowerRamsey ω 3 := by
  sorry

/--
Specker [Sp57] proved that when $α=ω^2$ any red/blue
colouring of the edges of $K_α$ there is either a red $K_α$ or a blue $K_3$.
-/
@[category research solved, AMS 3]
theorem erdos_590.variants.two : OmegaPowerRamsey 2 3 := by
  sorry

/--
Specker [Sp57] proved that when $α=ω^n$ for $3≤ n < \omega$ then it is not the case that any
red/blue colouring of the edges of $K_α$ there is either a red $K_α$ or a blue $K_3$.
-/
@[category research solved, AMS 3]
theorem erdos_590.variants.ge_three_false (n : ℕ) (h : 3 ≤ n) : ¬ OmegaPowerRamsey n 3 := by
  sorry

/--
Let m be a finite cardinal $< \omega$. Let $α$ be the infinite ordinal $\omega^{\omega}$.
It was proved by Milnor that any red/blue colouring of the edges of $K_α$ there is either a
red $K_α$ or a blue $K_3$. A shorter proof was found by Larson [La73]
-/
@[category research solved, AMS 3]
theorem erdos_590.variants.finite_cardinal (m : ℕ): OmegaPowerRamsey ω m := by
  sorry
