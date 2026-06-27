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

*References:*
- [erdosproblems.com/459](https://www.erdosproblems.com/459)
- [ErGr80] P. Erdős and R. L. Graham, *Old and new problems and results in combinatorial number
  theory*, Monographies de L'Enseignement Mathématique 28 (1980), p.91.
- [OEIS A289280](https://oeis.org/A289280)
-/

namespace Erdos459

/--
The function from the problem, in its equivalent form: `f u` is the smallest `v > u` all of whose
prime factors divide `u`. (Equivalently, `f u` is the largest `v` such that no `m ∈ (u, v)` is
composed entirely of primes dividing `u * v`.)
-/
noncomputable def f (u : ℕ) : ℕ := sInf {v | u < v ∧ v.primeFactors ⊆ u.primeFactors}

/--
Let $f(u)$ be the largest $v$ such that no $m\in (u,v)$ is composed entirely of primes dividing
$uv$. Estimate $f(u)$.

The estimate $u + 2 \le f(u) \le u^2$ holds for every $u \ge 2$. The upper bound is attained
when $u$ is prime, and the lower bound when $u = 2^k - 2$ with $k \ge 2$; Cambie further showed
that $f(n) = (1 + o(1))n$ for almost all $n$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/Woett/Lean-files/blob/main/ErdosProblem459.lean"]
theorem erdos_459 {u : ℕ} (hu : 2 ≤ u) : u + 2 ≤ f u ∧ f u ≤ u ^ 2 := by
  sorry

/--
The upper bound $f u ≤ u ^ 2$ is attained exactly when `u` is prime: $f p = p ^ 2$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/Woett/Lean-files/blob/main/ErdosProblem459.lean"]
theorem erdos_459.variants.upper_tight {p : ℕ} (hp : p.Prime) : f p = p ^ 2 := by
  sorry

end Erdos459
