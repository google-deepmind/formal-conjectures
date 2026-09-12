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
# Erdős Problem 784

*References:*
- [erdosproblems.com/784](https://www.erdosproblems.com/784)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
- [ErRu80] Erdős, P. and Ruzsa, I. Z., *On the small sieve. I. Sifting by primes*. J. Number Theory
  (1980), 385--394.
- [Ru82] Ruzsa, Imre Z., *On the small sieve. {II}. Sifting by composite numbers*. J. Number Theory
  (1982), 260--268.
- [Sa98] Saias, Eric, *Applications des entiers \`a{} diviseurs denses*. Acta Arith. (1998), 225--240.
- [ScSz59] Schinzel, A. and Szekeres, G., *Sur un probl\`{e}me de M. Paul Erdős*. Acta Sci. Math.
  (Szeged) (1959), 221-229.
- [We25] Weingartner, Andreas, *The Schinzel-Szekeres function*. Res. Number Theory (2025), Paper
  No. 63, 32.
-/

open Filter Asymptotics Real

namespace Erdos784

/-- The integers in $\{1,\ldots,x\}$ not divisible by any element of $A$. -/
def avoidsDivisors (A : Finset ℕ) (x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (fun m => ∀ a ∈ A, ¬ a ∣ m)

/--
$H_C(x)$ is the minimum of $\#\{ m\leq x : a\nmid m\textrm{ for all }a\in A\}$ as $A$ ranges over
all subsets of $\{2,\ldots,\lfloor x\rfloor\}$ with $\sum_{n\in A}\frac{1}{n}\leq C$.

For $C\geq 0$ the empty set is admissible, so this is the minimum of a nonempty set of natural
numbers. (If $C<0$ there are no admissible sets and `sInf` returns $0$.)
-/
noncomputable def H (C : ℝ) (x : ℕ) : ℕ :=
  sInf {(avoidsDivisors A x).card | (A : Finset ℕ) (_ : A ⊆ Finset.Icc 2 x)
    (_ : A.reciprocalSum ≤ C)}

/--
The bound asked in the boxed problem: some $c=c(C)>0$ such that
$H_C(x)\gg x/(\log x)^c$ for all sufficiently large $x$.
-/
def BoundHolds (C : ℝ) : Prop :=
  ∃ c > (0 : ℝ), ∃ K > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
    K * (x : ℝ) / (log x) ^ c ≤ H C x

/--
Let $C>0$. Does there exist a $c>0$ (depending on $C$) such that, for all sufficiently large $x$,
if $A\subseteq [1,x]$ has $\sum_{n\in A}\frac{1}{n}\leq C$ then
$$\#\{ m\leq x : a\nmid m\textrm{ for all }a\in A\}\gg\frac{x}{(\log x)^c}?$$

In the comments jif has noted that the answer is trivially no for every $C\geq 1$ with $A=\{1\}$.
Presumably (as is usual in these kind of questions) the assumption that $1\not\in A$ is intended.

Together these answer the given question (positively for $0<C\leq 1$ and negatively for $C>1$).
-/
@[category research solved, AMS 11]
theorem erdos_784 (C : ℝ) (hC : 0 < C) : BoundHolds C ↔ C ≤ 1 := by
  sorry

/--
For $C=1$ it is known that
$$H_1(x)\asymp \frac{x}{\log x}.$$
The lower bound is due to Ruzsa [Ru82], and the upper bound is due to Saias [Sa98].
-/
@[category research solved, AMS 11]
theorem erdos_784.variants.C_eq_one :
    (fun x : ℕ ↦ (H 1 x : ℝ)) =Θ[atTop] (fun x : ℕ ↦ (x : ℝ) / log x) := by
  sorry

/--
For fixed $C>1$ Ruzsa answered this question in the negative. (In [Er80] Erdős states that Ruzsa's
construction shows his 'intuition completely misled' him.) In fact
$$H_C(x)=x^{e^{1-C}+o(1)}.$$
This was improved by Weingartner [We25] who proved (for any fixed $C>1$)
$$H_C(x)\asymp \frac{x^{e^{1-C}}}{\log x}.$$
-/
@[category research solved, AMS 11]
theorem erdos_784.variants.weingartner (C : ℝ) (hC : 1 < C) :
    (fun x : ℕ ↦ (H C x : ℝ)) =Θ[atTop]
      (fun x : ℕ ↦ (x : ℝ) ^ exp (1 - C) / log x) := by
  sorry

/--
On the other hand, if $A$ is restricted to sets of primes then Erdős and Ruzsa [ErRu80] proved that
there are always $\gg_C x$ many $n\leq x$ not divisible by any $p\in A$.
-/
@[category research solved, AMS 11]
theorem erdos_784.variants.primes (C : ℝ) (hC : 0 < C) :
    ∃ K > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 x → (∀ p ∈ A, p.Prime) → A.reciprocalSum ≤ C →
        K * (x : ℝ) ≤ (avoidsDivisors A x).card := by
  sorry

end Erdos784
