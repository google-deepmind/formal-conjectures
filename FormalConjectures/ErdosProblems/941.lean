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

A joint problem of Erdős and Ivić, posed in the Oberwolfach problem book (1986) [Ob1].
Heath-Brown proved that every sufficiently large integer is the sum of at most three powerful
numbers (numbers whose prime factors all appear with exponent ≥ 2).

See also Problem 1107, which generalizes this to $r$-powerful numbers for $r \geq 3$,
and Problem 940.

*Reference:* [erdosproblems.com/941](https://www.erdosproblems.com/941)

[Er76d] Erdős, P., _Problems and results on number theoretic properties of consecutive
integers and related questions_. Proceedings of the Fifth Manitoba Conference on Numerical
Mathematics (Univ. Manitoba, Winnipeg, Man., 1975) (1976), 25-44.

[He88] Heath-Brown, D.R., _Ternary quadratic forms and sums of three square-full numbers_.
Séminaire de Théorie des Nombres, Paris 1986–87 (1988), 137–163.

[Ob1] Oberwolfach problem session (1986).

OEIS: [A056828](https://oeis.org/A056828)
-/

namespace Erdos941

/--
Erdős Problem 941 (proved by Heath-Brown [He88]):

Are all large integers the sum of at most three powerful numbers (i.e. if $p \mid n$
then $p^2 \mid n$)? That is, does there exist $N_0$ such that for all $n \geq N_0$, there
exist powerful numbers $a, b, c$ (possibly zero) with $n = a + b + c$?
-/
@[category research solved, AMS 11]
theorem erdos_941 : answer(True) ↔ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∃ a b c : ℕ, n = a + b + c ∧
      a.Powerful ∧ b.Powerful ∧ c.Powerful := by
  sorry

end Erdos941
