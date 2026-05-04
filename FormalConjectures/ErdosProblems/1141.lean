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
# Erdős Problem 1141

*References:*
- [erdosproblems.com/1141](https://www.erdosproblems.com/1141)
- [A214583](https://oeis.org/A214583)
- [APSSV26b] B. Alexeev, M. Putterman, M. Sawhney, M. Sellke, and G. Valiant,
  [Short proofs in combinatorics, probability and number theory II](https://arxiv.org/abs/2604.06609).
  arXiv:2604.06609 (2026).
- [Or26] Y. Oriike, [Lean formalisation of Erdős problem 1141](https://github.com/yuta0x89/ErdosProblems/blob/a1319f732cdee5140faf47d984e2c451c1184803/Erdos1141.lean) (2026)
- [Po17] P. Pollack, Bounds for the first several prime character nonresidues. Proc. Amer. Math. Soc.
  (2017), 2815--2826.
- [Va99] Various, Some of Paul's favorite problems. Booklet produced for the conference "Paul Erdős
  and his mathematics", Budapest, July 1999 (1999).
-/

open Nat Set

namespace Erdos1141

/--
The property that $n-k^2$ is prime for all $k$ with $(n,k)=1$ and $k^2 < n$.
-/
def Erdos1141Prop (n : ℕ) : Prop :=
  ∀ k, k ^ 2 < n → Coprime n k → (n - k ^ 2).Prime

instance (n : ℕ) : Decidable (Erdos1141Prop n) :=
  decidable_of_iff (∀ k ≤ .sqrt (n - 1), Coprime n k → (n - k ^ 2).Prime) <| by
    cases n with
    | zero => simp [Erdos1141Prop]
    | succ n' =>
      simp [Erdos1141Prop, le_sqrt, pow_two]

/--
Are there infinitely many $n$ such that $n-k^2$ is prime for all $k$ with $(n,k)=1$ and $k^2 < n$?

In [Va99] it is asked whether $968$ is the largest integer with this property, but this is an
error, since for example $968-9=7\cdot 137$.

The list of $n$ satisfying the given property is [A214583] in the OEIS. The largest known such $n$
is $1722$.

The answer is negative: [APSSV26b] proves a stronger finiteness theorem, deducing it from
Pollack [Po17]. Oriike [Or26] formalised the deduction in Lean.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/yuta0x89/ErdosProblems/blob/a1319f732cdee5140faf47d984e2c451c1184803/Erdos1141.lean"]
theorem erdos_1141 :
    answer(False) ↔ Infinite { n | Erdos1141Prop n } := by
  sorry

@[category test, AMS 11]
example : ¬ Erdos1141Prop 968 := by
  decide +native

@[category test, AMS 11]
example : Erdos1141Prop 1722 := by
  decide +native

end Erdos1141
