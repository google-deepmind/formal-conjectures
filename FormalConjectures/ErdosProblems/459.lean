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
# Erdős Problem 459

*Reference:* [erdosproblems.com/459](https://www.erdosproblems.com/459)

Let $f(u)$ be the largest $v$ such that no $m \in (u,v)$ is composed entirely
of primes dividing $uv$. Equivalently, $f(u)$ is the smallest integer $v > u$
such that every prime factor of $v$ divides $u$.

Trivially $u + 2 \leq f(u) \leq u^2$.

Cambie showed:
- $f(p) = p^2$ for every prime $p$
- $f(u) = u + 2$ whenever $u = 2^k - 2$ for $k \geq 2$
- $f(n) = (1 + o(1))n$ for almost all $n$

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
number theory*. Monographies de L'Enseignement Mathematique (1980).
-/

open Filter

open scoped Topology

namespace Erdos459

/-- The smallest $v > u$ such that every prime factor of $v$ divides $u$. -/
noncomputable def f (u : ℕ) : ℕ :=
  sInf {v : ℕ | u < v ∧ ∀ p : ℕ, Nat.Prime p → p ∣ v → p ∣ u}

/--
Erdős Problem 459 (almost all, Cambie):

$f(n) = (1 + o(1))n$ for almost all $n$, i.e., for every $\varepsilon > 0$, the density
of $\{n : f(n) > (1 + \varepsilon)n\}$ tends to $0$.
-/
@[category research solved, AMS 11]
theorem erdos_459 (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun x : ℕ =>
      (((Finset.Icc 1 x).filter (fun n =>
        (f n : ℝ) > (1 + ε) * (n : ℝ))).card : ℝ) / (x : ℝ))
      atTop (nhds 0) := by
  sorry

/--
Erdős Problem 459 (lower bound) [ErGr80, p.91]:

For all $u \geq 2$, $f(u) \geq u + 2$.
-/
@[category undergraduate, AMS 11]
theorem erdos_459.variants.lower_bound (u : ℕ) (hu : 2 ≤ u) :
    u + 2 ≤ f u := by
  sorry

/--
Erdős Problem 459 (upper bound) [ErGr80, p.91]:

For all $u \geq 2$, $f(u) \leq u^2$.
-/
@[category undergraduate, AMS 11]
theorem erdos_459.variants.upper_bound (u : ℕ) (hu : 2 ≤ u) :
    f u ≤ u ^ 2 := by
  sorry

/--
Erdős Problem 459 (prime case, Cambie):

For every prime $p$, $f(p) = p^2$.
-/
@[category research solved, AMS 11]
theorem erdos_459.variants.prime (p : ℕ) (hp : Nat.Prime p) :
    f p = p ^ 2 := by
  sorry

end Erdos459
