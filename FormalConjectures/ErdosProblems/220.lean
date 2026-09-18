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

import FormalConjecturesUtil

/-!
# Erdős Problem 220

*References:*
- [erdosproblems.com/220](https://www.erdosproblems.com/220)
- [Er40] Erdős, P., *The difference of consecutive primes*. Duke Math. J. (1940), 438--441.
- [Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971)
  (1973), 117-138.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [MoVa86] Montgomery, H. L. and Vaughan, R. C., *On the distribution of reduced residues*. Ann. of
  Math. (2) (1986), 311-333.
- [Gu04] Guy, Richard K., *Unsolved problems in number theory*. (2004), xviii+437.
-/

namespace Erdos220

/-- The sum of the squared differences of adjacent entries of a list of natural numbers. -/
def sumSquaredGaps : List ℕ → ℕ
  | a :: b :: rest => (b - a) ^ 2 + sumSquaredGaps (b :: rest)
  | _ => 0

/-- The reduced residues `1 ≤ m < n` with `(m, n) = 1`, in increasing order. -/
def sortedTotatives (n : ℕ) : List ℕ :=
  ((Finset.Ico 1 n).filter fun m => m.Coprime n).sort (· ≤ ·)

/--
Let $n \geq 1$ and
$$A = \{a_1 < \cdots < a_{\phi(n)}\} = \{1 \leq m < n : (m, n) = 1\}.$$
Is it true that
$$\sum_{1 \leq k < \phi(n)} (a_{k+1} - a_k)^2 \ll \frac{n^2}{\phi(n)}?$$

A problem of Erdős [Er40, Er73, ErGr80], which is discussed in problem B40 of Guy's collection
[Gu04]. The answer is yes, as proved by Montgomery and Vaughan [MoVa86], who in fact proved that
$\sum_{1 \leq k < \phi(n)} (a_{k+1} - a_k)^\gamma \ll n^\gamma / \phi(n)^{\gamma - 1}$ for every
$\gamma \geq 1$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos220.lean#L39"]
theorem erdos_220 : answer(True) ↔
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (sumSquaredGaps (sortedTotatives n) : ℝ) ≤ C * (n : ℝ) ^ 2 / (n.totient : ℝ) := by
  sorry

end Erdos220
