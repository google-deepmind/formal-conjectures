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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 407

*References:*
- [erdosproblems.com/407](https://www.erdosproblems.com/407)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [EGST88] Evertse, J.-H. and Győry, K. and Stewart, C. L. and Tijdeman, R., *$S$-unit equations
  and their applications*. New advances in transcendence theory (Durham, 1986) (1988), 110-174.
- [TiWa88] Tijdeman, R. and Wang, Lian Xiang, *Sums of products of powers of given prime
  numbers*. Pacific J. Math. (1988), 177-193.
- [BaBe24] Bajpai, Prajeet and Bennett, Michael A., *Effective $S$-unit equations beyond three
  terms: Newman's conjecture*. Acta Arith. (2024), 421-458.
-/

@[expose] public section

namespace Erdos407

/-- `w n` counts the ordered quadruples $(a,b,c,d)$ of nonnegative integers with
$n=2^a+3^b+2^c3^d$. -/
noncomputable def w (n : ℕ) : ℕ :=
  {x : ℕ × ℕ × ℕ × ℕ | 2 ^ x.1 + 3 ^ x.2.1 + 2 ^ x.2.2.1 * 3 ^ x.2.2.2 = n}.ncard

/--
Let $w(n)$ count the number of solutions to
$$n=2^a+3^b+2^c3^d$$
with $a,b,c,d\geq 0$ integers. Is it true that $w(n)$ is bounded by some absolute constant?

A conjecture originally due to Newman.

This is true, and was proved by Evertse, Győry, Stewart, and Tijdeman [EGST88].

Quantitative bounds were provided by Tijdeman and Wang [TiWa88], who proved that (if $w(n)$ only
counts distinct solutions, where we call two solutions distinct if the sets
$\{2^a,3^b,2^{c}3^d\}$ are distinct) then $w(n) \leq 4$ for all large $n$.

This was made effective by Bajpai and Bennett [BaBe24], who proved that $w(n)\leq 4$ if
$n\geq 131082$ and $w(n)\leq 9$ for all $n$. (The largest $n$ for which $w(n)=9$ is $299$.)
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos407.lean#L257"]
theorem erdos_407 : answer(True) ↔ ∃ C : ℕ, ∀ n : ℕ, w n ≤ C := by
  sorry

end Erdos407
