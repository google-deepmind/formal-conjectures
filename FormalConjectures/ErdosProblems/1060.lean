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
open Asymptotics

/-!
# Erdős Problem 1060

*Reference:* [erdosproblems.com/1060](https://www.erdosproblems.com/1060)
-/


namespace Erdos1060

/--
`σ(n)` is the classical **sum-of-divisors function**.

More precisely:
\[
\sigma(n) = \sum_{d \mid n} d,
\]
the sum of all positive divisors of `n`.
-/

def sigma (n : ℕ) : ℕ := ∑ x ∈ n.divisors, x


/--
`CountSolutions n` is the number of natural numbers `k ≤ n`
such that `k * σ(k) = n`.

Formally, we count:
\[
f(n) = \#\{\,k : \mathbb{N} \mid k \le n \ \text{and}\ k \sigma(k) = n\,\}.
\]
-/

def CountSolutions (n : ℕ) : ℕ :=
  Fintype.card {k : Fin (n + 1) // (k:ℕ) * sigma (k:ℕ) = n}


noncomputable def LogLog (n : ℕ) : ℝ := Real.log (Real.log (n : ℝ))


/--
`LittleO h` expresses the asymptotic condition

\[
h(n) = o\!\Big(\frac{1}{\log\log n}\Big) \quad (n \to \infty).
\]

-/

def LittleO (h : ℕ → ℝ)  : Prop :=
  IsLittleO Filter.atTop (fun n => h n) (fun n => (1 : ℝ) / LogLog n)


/-- The conjecture is about the function $f(n)$ count the number of solutions to $k\sigma(k)=n$,
where $\sigma(k)$ is the sum of divisors of $k$. Is it true that
$f(n)\leq n^{o(\frac{1}{\log\log n})}$? Perhaps even $\leq (\log n)^{O(1)}$?
-/

@[category research open, AMS 11]
theorem erdos_1060.bound_one (n : ℕ) :
  ∃ h : ℕ → ℝ, LittleO h ∧ CountSolutions n ≤ (n:ℝ) ^ h n :=
  by sorry



@[category research open, AMS 11]
theorem erdos_1060.bound_two (n : ℕ ) :
 ∃ (C : ℝ), IsBigO Filter.atTop (fun n =>
  (CountSolutions n : ℝ )) (fun n => (Real.log (n : ℝ)) ^ C) :=
  by sorry

end Erdos1060
