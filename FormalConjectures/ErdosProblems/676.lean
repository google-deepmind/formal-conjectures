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

[Er79] Erdős, P., _Some unconventional problems in number theory_. Math. Mag. 52 (1979), 67–70.

[Er79d] Erdős, P., _Some unconventional problems in number theory_. Acta Math. Acad. Sci.
Hungar. 33 (1979), 71–80.
-/

namespace Erdos676

/--
Erdős Problem 676 [Er79][Er79d]:

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

/--
Variant of Erdős Problem 676 (Selfridge–Wagstaff): If the primality requirement on $p$ is
dropped, a preliminary computer search by Selfridge and Wagstaff suggested that there are
infinitely many integers not of the form $am^2 + b$ with $m \geq 2$, $a \geq 1$,
$0 \leq b < m$. -/
@[category research open, AMS 11]
theorem erdos_676_non_prime :
    ∀ N₀ : ℕ, ∃ n : ℕ, n ≥ N₀ ∧
      ∀ m a b : ℕ, m ≥ 2 → a ≥ 1 → b < m → n ≠ a * m ^ 2 + b := by
  sorry

/--
Variant of Erdős Problem 676 [Er79d]: Erdős conjectured that $\limsup c_n = \infty$,
where $c_n$ is the minimal coefficient such that $n = ap^2 + b$ with $0 \leq b < c_n p$
for some prime $p$ with $p^2 \leq n$. Equivalently, for every $C$, there are infinitely
many $n$ such that $n \bmod p^2 \geq C \cdot p$ for every prime $p$ with $p^2 \leq n$. -/
@[category research open, AMS 11]
theorem erdos_676_limsup_minimal_coefficient :
    ∀ C : ℕ, ∀ N₀ : ℕ, ∃ n : ℕ, n ≥ N₀ ∧
      ∀ p : ℕ, Nat.Prime p → p ^ 2 ≤ n → n % (p ^ 2) ≥ C * p := by
  sorry

end Erdos676
