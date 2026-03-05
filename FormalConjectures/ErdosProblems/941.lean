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
# Erdős Problem 941

Heath-Brown proved that every sufficiently large integer is the sum of at most three powerful
numbers (numbers whose prime factors all appear with exponent ≥ 2).

*Reference:* [erdosproblems.com/941](https://www.erdosproblems.com/941)

[He88] Heath-Brown, D.R., _Ternary quadratic forms and sums of three square-full numbers_.
Séminaire de Théorie des Nombres, Paris 1986–87 (1988), 137–163.
-/

namespace Erdos941

/-- A natural number $n$ is powerful if for every prime $p$ dividing $n$, $p^2$ also
    divides $n$. -/
def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/--
Erdős Problem 941 (proved by Heath-Brown [He88]):

Are all large integers the sum of at most three powerful numbers (i.e. if $p \mid n$
then $p^2 \mid n$)? That is, does there exist $N_0$ such that for all $n \geq N_0$, there
exist powerful numbers $a, b, c$ (possibly zero) with $n = a + b + c$?
-/
@[category research solved, AMS 11]
theorem erdos_941 : answer(True) ↔ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∃ a b c : ℕ, n = a + b + c ∧
      IsPowerful a ∧ IsPowerful b ∧ IsPowerful c := by
  sorry

end Erdos941
