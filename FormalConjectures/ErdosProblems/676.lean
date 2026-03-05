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
# Erdős Problem 676

*Reference:* [erdosproblems.com/676](https://www.erdosproblems.com/676)

Is every sufficiently large integer of the form $ap^2 + b$ for some prime $p$
and integer $a \geq 1$ and $0 \leq b < p$?

The sieve of Eratosthenes implies that almost all integers are of this form,
and the Brun–Selberg sieve implies the number of exceptions in $[1,x]$ is
$\ll x/(\log x)^c$ for some constant $c > 0$. Erdős believed it is "rather unlikely"
that all large integers are of this form.

[Er79] Erdős, P., _Some unconventional problems in number theory_. Acta Math. Acad. Sci.
Hungar. 33 (1979), 71–80.
-/

namespace Erdos676

/--
Erdős Problem 676 [Er79]:

Is every sufficiently large integer of the form $ap^2 + b$ for some prime $p$
and integer $a \geq 1$ and $0 \leq b < p$?

Formalized as: there exists $N_0$ such that for all $n \geq N_0$, there exist a prime $p$,
a positive integer $a$, and a non-negative integer $b < p$ with $n = a \cdot p^2 + b$.
-/
@[category research open, AMS 11]
theorem erdos_676 :
    answer(sorry) ↔
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        ∃ p a b : ℕ, Nat.Prime p ∧ a ≥ 1 ∧ b < p ∧ n = a * p ^ 2 + b := by
  sorry

end Erdos676
