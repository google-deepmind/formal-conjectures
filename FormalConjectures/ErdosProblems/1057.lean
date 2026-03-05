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
# Erdős Problem 1057

*Reference:* [erdosproblems.com/1057](https://www.erdosproblems.com/1057)

Let $C(x)$ count the number of Carmichael numbers in $[1, x]$. Is it true that
$C(x) = x^{1-o(1)}$?

A Carmichael number is a composite $n > 1$ such that $a^n \equiv a \pmod{n}$ for all $a$.
By Korselt's criterion, this is equivalent to $n$ being squarefree, composite,
and $p - 1 \mid n - 1$ for all primes $p \mid n$.

Alford, Granville, and Pomerance [AGP94] proved $C(x) \to \infty$ and $C(x) > x^{2/7}$.
Harman [Ha08] improved the lower bound to $C(x) > x^{0.33336704}$.

[AGP94] Alford, W. R., Granville, A., and Pomerance, C., _There are infinitely many Carmichael
numbers_. Annals of Mathematics (1994).

[Ha08] Harman, G., _Watt's mean value theorem and Carmichael numbers_. International Journal of
Number Theory (2008).

[Er56c] Erdős, P., _On pseudoprimes and Carmichael numbers_. Publ. Math. Debrecen (1956).
-/

open Finset Filter Real Classical

namespace Erdos1057

/-- A natural number $n$ is a Carmichael number if $n > 1$, $n$ is not prime,
$n$ is squarefree, and $p - 1 \mid n - 1$ for every prime $p$ dividing $n$.
(This is Korselt's criterion.) -/
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ Squarefree n ∧ ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)

/-- $C(x)$ counts the number of Carmichael numbers in $\{1, \ldots, x\}$. -/
noncomputable def carmichaelCount (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun n => IsCarmichael n)).card

/--
Erdős Problem 1057 [Er56c]:

Is it true that $C(x) = x^{1-o(1)}$? That is, does $\log C(x) / \log x \to 1$
as $x \to \infty$?

This asks whether the Carmichael counting function grows almost as fast
as $x$ itself, in the sense that the exponent approaches 1.
-/
@[category research open, AMS 11]
theorem erdos_1057 : answer(sorry) ↔
    Tendsto
      (fun x : ℕ => Real.log (carmichaelCount x : ℝ) / Real.log (x : ℝ))
      atTop (nhds 1) := by
  sorry

end Erdos1057
