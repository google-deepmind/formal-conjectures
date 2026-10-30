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
# Erdős Problem 983

*References:*
- [erdosproblems.com/983](https://www.erdosproblems.com/983)
- [Er70b] Erdős, P., *Some applications of graph theory to number theory*. Proc. Second Chapel
  Hill Conf. on Combinatorial Mathematics and its Applications (Univ. North Carolina, Chapel
  Hill, N.C., 1970) (1970), 136-145. [PDF](https://www.renyi.hu/~p_erdos/1970-20.pdf)
- [Po79] Pomerance, C., *The prime number graph*. Math. Comp. 33 (1979), 399-408.
  [PDF](https://math.dartmouth.edu/~carlp/PDF/paper19.pdf)
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos983

/-- `numSmooth A S` is the number of elements of `A` all of whose prime factors lie in `S`.
The element `1` has no prime factors, so it is counted for every `S`. -/
def numSmooth (A S : Finset ℕ) : ℕ :=
  (A.filter fun a => ∀ p ∈ a.primeFactors, p ∈ S).card

/-- $f(k,n)$ is the least $r$ such that every $A\subseteq\{1,\ldots,n\}$ with $|A|=k$ has a set
$S$ of $r$ primes with more than $r$ elements of $A$ divisible only by primes from $S$.

For $\pi(n)<k\leq n$ the value $r=\pi(n)$ is admissible (take all primes $\leq n$), so `sInf` is
a minimum. Outside this range `f k n = 0` is a junk value: for $k\leq\pi(n)$ no $r$ is
admissible, and for $k>n$ every $r$ is. -/
noncomputable def f (k n : ℕ) : ℕ :=
  sInf {r : ℕ | ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → A.card = k →
    ∃ S : Finset ℕ, S.card = r ∧ (∀ p ∈ S, p.Prime) ∧ r < numSmooth A S}

/-- If every `A ⊆ {1, …, n}` of size `k` has a set `S` of `r` primes with more than `r`
elements of `A` divisible only by primes from `S`, then `f k n ≤ r`. -/
@[category API, AMS 11]
theorem f_le {k n r : ℕ}
    (h : ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → A.card = k →
      ∃ S : Finset ℕ, S.card = r ∧ (∀ p ∈ S, p.Prime) ∧ r < numSmooth A S) :
    f k n ≤ r :=
  Nat.sInf_le h

/--
Let $n\geq 2$ and $\pi(n)<k\leq n$. Let $f(k,n)$ be the smallest integer $r$ such that in any
$A\subseteq \{1,\ldots,n\}$ of size $\lvert A\rvert=k$ there exist primes $p_1,\ldots,p_r$ such
that $>r$ many $a\in A$ are only divisible by primes from $\{p_1,\ldots,p_r\}$.

Is it true that
$$2\pi(n^{1/2})-f(\pi(n)+1,n)\to \infty$$
as $n\to \infty$?

This is the first part. The primes may depend on $A$. Erdős and Straus conjectured this
[Er70b, p. 138 and p. 140].

The answer is no: Liam Price and GPT-5.5 Pro showed on the
[forum](https://www.erdosproblems.com/forum/thread/983#post-6104) that
$f(\pi(n)+1,n)=2\pi(n^{1/2})+1$ for infinitely many $n$; see the
[explanation](https://www.erdosproblems.com/forum/thread/983#post-6525) by Nat Sothanaphan.
Write $p_k$ for the $k$-th prime. By [Po79, Corollary after Theorem 2.2] there are infinitely
many $N$ with $p_{N-i}p_{N+i}<p_N^2$ for $1\leq i<N$. Take $n=p_N^2-1$, so
$\pi(n^{1/2})=N-1$. Let $A$ consist of the products of adjacent primes on the path
$p_{2N-1},p_1,p_{2N-2},p_2,\ldots,p_{N+1},p_{N-1},p_N$, its two endpoint primes, and the
other primes up to $n$. Then $\lvert A\rvert=\pi(n)+1$, and for any $r\leq 2N-2$ primes at
most $r$ elements of $A$ are divisible only by those primes, so $f(\pi(n)+1,n)\geq 2N-1$.
-/
@[category research solved, question, AMS 11]
theorem erdos_983.parts.i :
    ¬ Tendsto (fun n : ℕ ↦
      2 * (Nat.primeCounting (Nat.sqrt n) : ℤ) - (f (Nat.primeCounting n + 1) n : ℤ))
      atTop atTop := by
  sorry

def erdos_983.parts.ii.answer : ℕ → ℕ → ℝ := sorry

/--
Let $n\geq 2$ and $\pi(n)<k\leq n$. Let $f(k,n)$ be the smallest integer $r$ such that in any
$A\subseteq \{1,\ldots,n\}$ of size $\lvert A\rvert=k$ there exist primes $p_1,\ldots,p_r$ such
that $>r$ many $a\in A$ are only divisible by primes from $\{p_1,\ldots,p_r\}$.

In general, estimate $f(k,n)$, particularly when $\pi(n)+1<k=o(n)$.

This is the second part. We read "estimate" as an asymptotic formula `answer k n`, valid for
every function $k=k(n)$ with $\pi(n)+1<k(n)=o(n)$.
-/
@[category research open, question value, AMS 11]
theorem erdos_983.parts.ii :
    ∀ k : ℕ → ℕ, (∀ᶠ n : ℕ in atTop, Nat.primeCounting n + 1 < k n) →
      ((fun n : ℕ ↦ (k n : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ))) →
      (fun n : ℕ ↦ (f (k n) n : ℝ)) ~[atTop]
        (fun n : ℕ ↦ erdos_983.parts.ii.answer (k n) n) := by
  sorry

/--
It is trivial that $f(k,n)\leq \pi(n)$ [Er70b, p. 138]. Here $\pi(n)<k$.
-/
@[category textbook, AMS 11]
theorem erdos_983.variants.le_primeCounting {k n : ℕ} (hk : Nat.primeCounting n < k) :
    f k n ≤ Nat.primeCounting n := by
  sorry

/--
Erdős and Straus [Er70b, p. 139, (14)] proved
$$f(\pi(n)+1,n)\leq 2\pi(n^{1/2})+1.$$
-/
@[category research solved, AMS 11]
theorem erdos_983.variants.upper_bound (n : ℕ) :
    f (Nat.primeCounting n + 1) n ≤ 2 * Nat.primeCounting (Nat.sqrt n) + 1 := by
  sorry

/--
Erdős and Straus proved [Er70b, pp. 138-140] that
$$f(\pi(n)+1,n)=2\pi(n^{1/2})+o_A\left(\frac{n^{1/2}}{(\log n)^A}\right)$$
for any $A>0$.
-/
@[category research solved, AMS 11]
theorem erdos_983.variants.erdos_straus :
    ∀ A : ℝ, 0 < A →
      (fun n : ℕ ↦ (f (Nat.primeCounting n + 1) n : ℝ) -
          2 * (Nat.primeCounting (Nat.sqrt n) : ℝ)) =o[atTop]
        (fun n : ℕ ↦ Real.sqrt n / Real.log n ^ A) := by
  sorry

end Erdos983
