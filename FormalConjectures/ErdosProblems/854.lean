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
public import FormalConjectures.ErdosProblems.«235»

/-!
# Erdős Problem 854

*References:*
- [erdosproblems.com/854](https://www.erdosproblems.com/854)
- [Er85c] Erdős, P., *On some of my problems in number theory I would most like to see solved*.
  Number theory (Ootacamund, 1984), Lecture Notes in Math. 1122 (1985), 74-84.
  [PDF](https://www.renyi.hu/~p_erdos/1985-17.pdf)
- [Ob1] Erdős, P., *Oberwolfach Mathematical Problems*, Volume 1. Mathematisches
  Forschungsinstitut Oberwolfach.
- [OEIS A389839](https://oeis.org/A389839): smallest even number which cannot be written as the
  difference of two consecutive numbers which are relatively prime to the $n$th primorial. It
  agrees with `minEvenNonGap k` for $k\geq 3$.
- [OEIS A048670](https://oeis.org/A048670): Jacobsthal's function of the product of the first $n$
  primes, which is the largest gap.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos854

/-- The $k$th primorial $n_k = p_1 \cdots p_k$, the product of the first $k$ primes
(`Nat.nth Nat.Prime i` is the $(i+1)$st prime, counting from $i = 0$). In particular $n_0 = 1$. -/
noncomputable def kthPrimorial (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-- `gapSet m` is the set of values of $a_{i+1} - a_i$, where $a_1 < a_2 < \cdots$ are the
integers in $[1, m)$ coprime to $m$ (for $m > 1$). It is the set of entries of `Erdos235.gaps m`,
the differences of consecutive entries of the sorted list of integers below `m` coprime to `m`. -/
def gapSet (m : ℕ) : Finset ℕ :=
  (Erdos235.gaps m).toFinset

/-- `maxGap m` is $\max_i (a_{i+1} - a_i)$ for the integers in $[1, m)$ coprime to `m`, and `0`
if there are no gaps. For $m = n_k$ with $k\geq 2$ this is the Jacobsthal function of $m$. -/
def maxGap (m : ℕ) : ℕ :=
  (gapSet m).sup id

/-- $f(k)$: the smallest positive even integer that is not of the form $a_{i+1} - a_i$ for the
integers $a_1 < a_2 < \cdots$ in $[1, n_k)$ coprime to $n_k$. The condition `0 < t` is needed
since $0$ is not a gap. For $k \geq 1$ the set contains $n_k$ itself (even, and larger than every
gap), so `sInf` is a true minimum. -/
noncomputable def minEvenNonGap (k : ℕ) : ℕ :=
  sInf {t : ℕ | 0 < t ∧ Even t ∧ t ∉ gapSet (kthPrimorial k)}

/-- The third primorial is $2 \cdot 3 \cdot 5 = 30$. -/
@[category test, AMS 11]
theorem kthPrimorial_three : kthPrimorial 3 = 30 := by
  simp [kthPrimorial, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two,
    Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]

def erdos_854.parts.i.answer : ℕ → ℝ := sorry

/--
Let $n_k$ denote the $k$th primorial, i.e. the product of the first $k$ primes.

If $1=a_1<a_2<\cdots <a_{\phi(n_k)}=n_k-1$ is the sequence of integers coprime to $n_k$, then
estimate the smallest even integer not of the form $a_{i+1}-a_i$. Are there
$$\gg \max_i (a_{i+1}-a_i)$$
many even integers of the form $a_{j+1}-a_j$?

This is the first part. A problem of Erdős [Er85c, p. 80], who writes "integer" instead of "even
integer"; all differences $a_{i+1}-a_i$ are even, so only even integers are meaningful. Here
"estimate" is read as $\Theta$. Erdős first thought that for large $k$ every even $t \leq
\max_i(a_{i+1}-a_i)$ is a gap, but [Ob1] reports computations of Lacampagne and Selfridge showing
this fails for $n_6 = 30030$ (OEIS A389839 and A048670 give $20$ and $22$).
-/
@[category research open, question value, AMS 11]
theorem erdos_854.parts.i :
    (fun k ↦ (minEvenNonGap k : ℝ)) =Θ[atTop] erdos_854.parts.i.answer := by
  sorry

/--
Let $n_k$ denote the $k$th primorial, i.e. the product of the first $k$ primes.

If $1=a_1<a_2<\cdots <a_{\phi(n_k)}=n_k-1$ is the sequence of integers coprime to $n_k$, then
estimate the smallest even integer not of the form $a_{i+1}-a_i$. Are there
$$\gg \max_i (a_{i+1}-a_i)$$
many even integers of the form $a_{j+1}-a_j$?

This is the second part. We read it as: there is an absolute constant $c > 0$ such that, for all
large $k$, the number of distinct gap values is at least $c$ times the largest gap.
-/
@[category research open, question, AMS 11]
theorem erdos_854.parts.ii :
    ∃ c > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      c * (maxGap (kthPrimorial k) : ℝ) ≤ ((gapSet (kthPrimorial k)).card : ℝ) := by
  sorry

end Erdos854
