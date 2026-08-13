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
# Number of parts in the symmetric representation of $\sigma(n)$

Number of parts in the symmetric representation of $\sigma(n)$. $a(n)$ is $1$ plus the number of pairs $(d_k, d_{k+1})$ of consecutive divisors of $n$
such that $d_{k+1}$ is odd and $d_{k+1} \ge 2 d_k$.

The formula used is
$1 + |\{(d_k, d_{k+1}) \in \text{consecutive pairs of divisors of } n \mid
d_{k+1} \text{ is odd and } d_{k+1} \ge 2 d_k\}|$,
which is a known characterization of the sequence.

*References:*
- [A237271](https://oeis.org/A237271)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA237271


open Nat Finset List

/--
Number of parts in the symmetric representation of $\sigma(n)$. $a(n)$ is $1$ plus the number of pairs $(d_k, d_{k+1})$ of consecutive divisors of $n$
such that $d_{k+1}$ is odd and $d_{k+1} \ge 2 d_k$.

The formula used is
$1 + |\{(d_k, d_{k+1}) \in \text{consecutive pairs of divisors of } n \mid
d_{k+1} \text{ is odd and } d_{k+1} \ge 2 d_k\}|$,
which is a known characterization of the sequence.
-/
def a (n : ℕ) : ℕ :=
  -- Get the list of divisors of n, sorted ascendingly.
  let divs_list : List ℕ := (n.divisors.sort (· ≤ ·))

  -- Get the list of consecutive pairs of divisors: [(d₁, d₂), (d₂, d₃), ...]
  let consecutive_pairs : List (ℕ × ℕ) := List.zip divs_list divs_list.tail

  -- Count the pairs satisfying the condition
  let count : ℕ := consecutive_pairs.countP fun pair =>
    let d_k := pair.fst
    let d_k_succ := pair.snd
    -- The second divisor d_{k+1} must be odd and at least twice the first divisor d_k.
    Odd d_k_succ ∧ d_k_succ ≥ 2 * d_k

  -- The sequence value is 1 + the count
  1 + count

def sortedDivisorsList (n : ℕ) : List ℕ := (n.divisors.sort (· ≤ ·))

/--
Number of maximal contiguous sublists of divisors of n where each adjacent pair (d_k, d_{k+1})
satisfies d_{k+1} <= 2 * d_k.
This is 1 + the number of "jumps" where d_{k+1} > 2 * d_k.
-/
def num2DenseSublists (n : ℕ) : ℕ :=
  let divs_list := sortedDivisorsList n
  let consecutive_pairs : List (ℕ × ℕ) := List.zip divs_list divs_list.tail

  -- A jump/break occurs when d_{k+1} > 2 * d_k
  let num_jumps : ℕ := consecutive_pairs.countP fun pair =>
    let d_k := pair.fst
    let d_k_succ := pair.snd
    d_k_succ > 2 * d_k

  1 + num_jumps


@[category test, AMS 11]
lemma a_1 : a 1 = 1 := by native_decide

@[category test, AMS 11]
lemma a_2 : a 2 = 1 := by native_decide

@[category test, AMS 11]
lemma a_3 : a 3 = 2 := by native_decide

@[category test, AMS 11]
lemma a_4 : a 4 = 1 := by native_decide

@[category test, AMS 11]
lemma a_5 : a 5 = 2 := by native_decide


/--
Conjecture 2: "a(n) is the number of 2-dense sublists of divisors of n.
We call '2-dense sublists of divisors of n' to the maximal sublists of divisors of n whose terms
increase by a factor of at most 2." - _Omar E. Pol_, Jul 31 2025

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/237271.wip.lean#L102"]
theorem conjecture_2 (n : ℕ) : a n = num2DenseSublists n := by
    sorry

/-- Number of odd divisors of n (A001227). -/
def A001227 (n : ℕ) : ℕ := (n.divisors.filter Odd).card

/-- Number of odd divisors m of n such that there is a divisor d of n with d < m < 2*d (A239657). -/
def A239657 (n : ℕ) : ℕ :=
  (n.divisors.filter fun m => Odd m ∧ ∃ d ∈ n.divisors, d < m ∧ m < 2 * d).card

/--
Conjecture 1 / Theorem: "a(n) is the number of odd divisors of n except the 'e' odd
divisors described in A005279." - _Omar E. Pol_, Dec 21 2024.
"The conjecture 1 is true. For a proof see A379288." - _Hartmut F. W. Hoft_, Jan 21 2025.
Equivalently, $a(n) = \text{A001227}(n) - \text{A239657}(n)$. - _Omar E. Pol_, Mar 23 2014
-/
@[category research solved, AMS 11]
theorem conjecture_1 (n : ℕ) (hn : 0 < n) :
    a n = A001227 n - A239657 n := by
  sorry

/--
Theorem: "a(p^k) = k + 1, where p is an odd prime and k >= 0."
- _Hartmut F. W. Hoft_, Dec 26 2016
-/
@[category research solved, AMS 11]
theorem a_odd_prime_pow (p k : ℕ) (hp : p.Prime) (ho : Odd p) :
    a (p ^ k) = k + 1 := by
  sorry

/--
Conjecture 3: "a(n) is the number of divisors p of n such that p is greater than
twice the adjacent previous divisor of n. The divisors p give the n-th row of A379288."
- _Omar E. Pol_, Aug 02 2025

Note: this is equivalent to `a_eq_num2DenseSublists` (Conjecture 2), since the divisors that
start a new 2-dense sublist are exactly those greater than twice their predecessor (plus the
smallest divisor).
-/
@[category research solved, AMS 11]
theorem conjecture_3 (n : ℕ) :
    a n = 1 + ((sortedDivisorsList n).zip (sortedDivisorsList n).tail).countP
      fun pair => pair.snd > 2 * pair.fst :=
  conjecture_2 n

/--
Conjecture 4: "a(A000290(n)) is odd." - _Omar E. Pol_, Oct 21 2025

That is, the number of parts in the symmetric representation of $\sigma(n^2)$ is always odd.
-/
@[category research open, AMS 11]
theorem conjecture_4 (n : ℕ) (hn : 0 < n) : Odd (a (n ^ 2)) := by
  sorry

/--
Conjecture 5: "a(A000384(n)) is odd." - _Omar E. Pol_, Oct 21 2025

That is, the number of parts in the symmetric representation of $\sigma(n(2n-1))$ is always odd,
where $n(2n-1)$ is the $n$-th hexagonal number.
-/
@[category research open, AMS 11]
theorem conjecture_5 (n : ℕ) (hn : 0 < n) : Odd (a (n * (2 * n - 1))) := by
  sorry

/--
Observation: "a(A002997(n)) >= 3, at least for 1 <= n <= 10000."
- _Omar E. Pol_, Oct 21 2025

That is, $a(k) \ge 3$ for every Carmichael number $k$.
A002997 is the sequence of Carmichael numbers.
-/
@[category research open, AMS 11]
theorem observation_carmichael (k : ℕ)
    (hk : ¬ k.Prime ∧ 1 < k ∧ ∀ a : ZMod k, a ≠ 0 → a ^ (k - 1) = 1) :
    3 ≤ a k := by
  sorry

end OeisA237271
