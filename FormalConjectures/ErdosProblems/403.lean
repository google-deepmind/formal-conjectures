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
# Erdős Problem 403

*Reference:* [erdosproblems.com/403](https://www.erdosproblems.com/403)

Asked by Burr and Erdős. Frankl and Lin independently showed that the answer
is yes, and the largest solution is $2^7 = 2! + 3! + 5!$.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in
combinatorial number theory*. Monographies de L'Enseignement Mathematique (1980).
-/

open Finset BigOperators

namespace Erdos403

/--
Erdős Problem 403 [ErGr80, p.79]:

The equation $2^m = a_1! + \cdots + a_k!$ with $a_1 < a_2 < \cdots < a_k$ has only finitely
many solutions. Here a solution is a pair $(m, S)$ where $m$ is a natural number
and $S$ is a nonempty finite set of natural numbers whose factorials sum to $2^m$.
-/
@[category research solved, AMS 11]
theorem erdos_403 :
    Set.Finite {p : ℕ × Finset ℕ | p.2.Nonempty ∧
      ∑ a ∈ p.2, Nat.factorial a = 2 ^ p.1} := by
  sorry

end Erdos403
