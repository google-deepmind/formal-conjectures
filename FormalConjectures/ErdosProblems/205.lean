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
# Erdős Problem 205

*Reference:* [erdosproblems.com/205](https://www.erdosproblems.com/205)

Erdős and Graham asked whether all sufficiently large $n$ can be written as $n = 2^k + m$ for some
$k \geq 0$, where $m$ has fewer than $\log(\log(m))$ prime factors counted with multiplicity. This
was disproved.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).
-/

open Real

namespace Erdos205

/--
Erdős Problem 205 (Disproved) [ErGr80, p.28]:

Erdős and Graham asked whether all sufficiently large $n$ can be written as
$2^k + m$ for some $k \geq 0$, where $\Omega(m) < \log(\log(m))$. Here $\Omega(m)$ is the number
of prime divisors of $m$ counted with multiplicity.

The answer is no (`answer(False)`): there are infinitely many counterexamples.
-/
@[category research solved, AMS 11]
theorem erdos_205 : answer(False) ↔
    (∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ k : ℕ, 2 ^ k ≤ n ∧
        ((n - 2 ^ k).primeFactorsList.length : ℝ) <
          Real.log (Real.log ((n - 2 ^ k : ℕ) : ℝ))) := by
  sorry

end Erdos205
