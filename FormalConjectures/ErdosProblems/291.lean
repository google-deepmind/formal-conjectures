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
# Erdős Problem 291

*References:*
- [erdosproblems.com/291](https://www.erdosproblems.com/291)
- [ErGr80, p.34] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number
  theory. Monographies de L'Enseignement Mathematique (1980).
- [Sh16] P. Shiu, The denominators of harmonic numbers. arXiv:1607.02863 (2016).
- [WuYa22] Wu, Bing-Ling and Yan, Xiao-Hui, On the denominators of harmonic numbers. {IV}. C. R.
  Math. Acad. Sci. Paris (2022), 53--57.
-/

open Nat Finset Set Filter

namespace Erdos291

/--
$L_n$ is the least common multiple of $\{1,\ldots,n\}$.
-/
def L (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm (fun x ↦ x)

@[category test, AMS 11]
theorem L_eval : L 1 = 1 ∧ L 2 = 2 ∧ L 3 = 6 ∧ L 4 = 12 := by decide

/--
$a_n$ is defined by $\sum_{1\leq k\leq n}\frac{1}{k}=\frac{a_n}{L_n}$.
-/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, L n / k

@[category test, AMS 11]
theorem a_eval : a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 11 ∧ a 4 = 25 := by decide

/--
Let $n\geq 1$ and define $L_n$ to be the least common multiple of $\{1,\ldots,n\}$ and $a_n$ by
$\sum_{1\leq k\leq n}\frac{1}{k}=\frac{a_n}{L_n}$.

Is it true that $(a_n,L_n)=1$ occurs for infinitely many $n$?
-/
@[category research open, AMS 11]
theorem erdos_291.parts.i :
    answer(sorry) ↔
      { n : ℕ | Nat.gcd (a n) (L n) = 1 }.Infinite := by
  sorry

/--
Is it true that $(a_n,L_n)>1$ occurs for infinitely many $n$?

Steinerberger has observed that the answer to the second question is trivially yes: for example, any
$n$ which begins with a $2$ in base $3$ has $3\mid (a_n,L_n)$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/Mnehmos/llm-driven-proof-search/blob/745090ac8644c90a4b9dd40171984af6b381af4e/lean-checker/LeanChecker/Erdos/Erdos291.lean"]
theorem erdos_291.parts.ii :
    answer(True) ↔
      { n : ℕ | Nat.gcd (a n) (L n) > 1 }.Infinite := by
  sorry

/--
More generally, if the leading digit of $n$ in base $p$ is $p-1$ then $p\mid (a_n,L_n)$. There is
in fact a necessary and sufficient condition: a prime $p\leq n$ divides $(a_n,L_n)$ if and only if
$p$ divides the numerator of $1+\cdots+\frac{1}{k}$, where $k$ is the leading digit of $n$ in base
$p$. This can be seen by writing $a_n = \frac{L_n}{1}+\cdots+\frac{L_n}{n}$ and observing that the
right-hand side is congruent to $1+\cdots+1/k$ modulo $p$. (The previous claim about $p-1$ follows
immediately from Wolstenholme's theorem.)
-/
@[category research solved, AMS 11]
theorem erdos_291.variants.steinerberger_generalization (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n) :
    let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num := by
  sorry

/--
This leads to a heuristic prediction (see for example a preprint of Shiu [Sh16]) of
$\asymp\frac{x}{\log x}$ for the number of $n\in [1,x]$ such that $(a_n,L_n)=1$.
-/
@[category research open, AMS 11]
theorem erdos_291.variants.shiu_heuristic_asymptotic :
    Asymptotics.IsTheta atTop
      (fun x : ℕ ↦ ((((Finset.Icc 1 x).filter (fun n ↦ Nat.gcd (a n) (L n) = 1)).card : ℝ)))
      (fun x : ℕ ↦ (x : ℝ) / Real.log x) := by
  sorry

/--
In particular, there should be infinitely many $n$, but the set of such $n$ should have
density zero. Unfortunately this heuristic is difficult to turn into a proof.
-/
@[category research open, AMS 11]
theorem erdos_291.variants.shiu_heuristic_density_zero :
    Filter.Tendsto (fun N : ℕ ↦
      ((((Finset.Icc 1 N).filter (fun n ↦ Nat.gcd (a n) (L n) = 1)).card : ℝ) / (N : ℝ)))
      atTop (nhds 0) := by
  sorry

/--
Wu and Yan [WuYa22] have proved, conditional on $\frac{1}{\log p}$ being linearly independent
over $\mathbb{Q}$ for any finite collection of primes $p$ (itself a consequence of Schanuel's
conjecture), that the set of $n$ for which $(a_n,L_n)>1$ has upper density $1$.
-/
@[category research solved, AMS 11]
theorem erdos_291.variants.wu_yan
    (h_indep : LinearIndependent ℚ (fun p : {p : ℕ // p.Prime} ↦ 1 / Real.log (p : ℝ))) :
    atTop.limsup (fun N : ℕ ↦
      ((((Finset.Icc 1 N).filter (fun n ↦ Nat.gcd (a n) (L n) > 1)).card : ℝ) /
        (N : ℝ) : EReal)) = 1 := by
  sorry

end Erdos291
