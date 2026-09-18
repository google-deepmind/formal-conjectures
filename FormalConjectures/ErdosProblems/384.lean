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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 384

*References:*
- [erdosproblems.com/384](https://www.erdosproblems.com/384)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Ec69] Ecklund, Jr., E. F., *On prime divisors of the binomial coefficient*. Pacific J. Math.
  (1969), 267-270.
- [Gu04] Guy, Richard K., *Unsolved problems in number theory*. (2004), xviii+437.
-/

@[expose] public section

namespace Erdos384

/--
If $1<k<n-1$ then $\binom{n}{k}$ is divisible by a prime $p\leq n/2$ (except
$\binom{7}{3}=\binom{7}{4}=5\cdot 7$).

A conjecture of Erdős and Selfridge [ErGr80]. Proved by Ecklund [Ec69], who made the stronger
conjecture that whenever $n>k^2$ the binomial coefficient $\binom{n}{k}$ is divisible by a prime
$p<n/k$. Discussed in problem B31 and B33 of Guy's collection [Gu04]. Stronger forms of this
conjecture are [1094](https://www.erdosproblems.com/1094) and
[1095](https://www.erdosproblems.com/1095).

Ecklund's theorem is stated for $n \geq 2k$ with the single exception $\binom{7}{3}$; by the
symmetry $\binom{n}{k} = \binom{n}{n-k}$ this is the form above, where $\binom{7}{4}$ is the
second exception. The prime bound is $p \leq n/2$ (that is, $2p \leq n$); see
`erdos_384.variants.strict` for the strict inequality.
-/
@[category research solved, AMS 11]
theorem erdos_384 (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3))
    (h₄ : (n, k) ≠ (7, 4)) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  sorry

/--
With the strict inequality $p < n/2$ the statement is false: $\binom{4}{2} = 6$ has no prime
divisor $p < 2$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos384.lean#L71"]
theorem erdos_384.variants.strict : answer(False) ↔
    ∀ n k : ℕ, 1 < k → k < n - 1 → (n, k) ≠ (7, 3) → (n, k) ≠ (7, 4) →
      ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n := by
  sorry

end Erdos384
