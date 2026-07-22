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
# Erdős Problem 785

*References:*
- [erdosproblems.com/785](https://www.erdosproblems.com/785)
- [ChFa10] Fang, Jin-Hui and Chen, Yong-Gao, *On additive complements*. Proc. Amer. Math. Soc.
  (2010), 1923-1927.
- [ChFa11] Chen, Yong-Gao and Fang, Jin-Hui, *On additive complements. II*. Proc. Amer. Math. Soc.
  (2011), 881-883.
- [ChFa14] Fang, Jin-Hui and Chen, Yong-Gao, *On additive complements. III*. J. Number Theory
  (2014), 83-91.
- [ChFa15] Chen, Yong-Gao and Fang, Jin-Hui, *On a conjecture of Sárközy and Szemerédi*.
  Acta Arith. (2015), 47-58.
- [Da64] Danzer, L., *Über eine Frage von G. Hanani aus der additiven Zahlentheorie*.
  J. Reine Angew. Math. (1964), 392-394.
- [Er57] Erdős, Paul, *Some unsolved problems*. Michigan Math. J. (1957), 291-300.
- [Er61] Erdős, Paul, *Some unsolved problems*. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221-254.
- [Na59] Narkiewicz, Władysław, *Remarks on a conjecture of Hanani in additive number theory*.
  Colloq. Math. (1959/60), 161-165.
- [Ru17] Ruzsa, Imre Z., *Exact additive complements*. Q. J. Math. (2017), 227-235.
- [SaSz94] Sárközy, A. and Szemerédi, E., *On a problem in additive number theory*.
  Acta Math. Hungar. (1994), 237-245.
-/

open Filter Pointwise
open Classical
open scoped Topology

namespace Erdos785

/-- The counting function $A(x)=\lvert A\cap [1,x]\rvert$. -/
noncomputable def counting (A : Set ℕ) (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (· ∈ A)).card

/-- The largest element of $A$ in $[1,x]$, that is $a^*(x)=\max A\cap [1,x]$
(equal to $0$ when there is no such element). -/
noncomputable def aStar (A : Set ℕ) (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (· ∈ A)).sup id

/-- Two sets $A, B\subseteq \mathbb{N}$ are *additive complements* if $A+B$ contains all
large integers. -/
def IsAdditiveComplement (A B : Set ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop, n ∈ A + B

/-- Two sets $A, B\subseteq \mathbb{N}$ are *exact additive complements* if $A+B$ contains all
large integers and $A(x)B(x)\sim x$. -/
def IsExactAdditiveComplement (A B : Set ℕ) : Prop :=
  IsAdditiveComplement A B ∧
    Tendsto (fun x : ℕ => (counting A x * counting B x : ℝ) / (x : ℝ)) atTop (𝓝 1)

/--
Let $A,B\subseteq \mathbb{N}$ be infinite sets such that $A+B$ contains all large integers.
Let $A(x)=\lvert A\cap [1,x]\rvert$ and similarly for $B(x)$. Is it true that if
$A(x)B(x)\sim x$ then
\[A(x)B(x)-x\to \infty\]
as $x\to \infty$?

A conjecture of Erdős and Danzer. The answer is yes, proved by Sárközy and Szemerédi [SaSz94],
who actually proved that it is impossible for
\[A(x)B(x)-x=o(A(x)).\]
-/
@[category research solved, AMS 11]
theorem erdos_785 : answer(True) ↔
    ∀ A B : Set ℕ, A.Infinite → B.Infinite → IsExactAdditiveComplement A B →
      Tendsto (fun x : ℕ => (counting A x * counting B x : ℝ) - (x : ℝ)) atTop atTop := by
  sorry

/--
Danzer [Da64] proved that exact additive complements exist (Hanani had earlier conjectured they
do not exist, as reported in [Er57] and [Er61]).
-/
@[category research solved, AMS 11]
theorem erdos_785.variants.danzer :
    ∃ A B : Set ℕ, A.Infinite ∧ B.Infinite ∧ IsExactAdditiveComplement A B := by
  sorry

/--
Sárközy and Szemerédi [SaSz94] proved that it is impossible for
\[A(x)B(x)-x=o(A(x)).\]
-/
@[category research solved, AMS 11]
theorem erdos_785.variants.sarkozy_szemeredi (A B : Set ℕ) (hA : A.Infinite) (hB : B.Infinite)
    (h : IsExactAdditiveComplement A B) :
    ¬ (fun x : ℕ => (counting A x * counting B x : ℝ) - (x : ℝ)) =o[atTop]
      (fun x : ℕ => (counting A x : ℝ)) := by
  sorry

/--
Chen and Fang [ChFa15] proved $A(x)B(x)-x\ll A(x)^c$ cannot hold for any constant $c>0$.
-/
@[category research solved, AMS 11]
theorem erdos_785.variants.chen_fang (A B : Set ℕ) (hA : A.Infinite) (hB : B.Infinite)
    (h : IsExactAdditiveComplement A B) (c : ℝ) (hc : 0 < c) :
    ¬ (fun x : ℕ => (counting A x * counting B x : ℝ) - (x : ℝ)) =O[atTop]
      (fun x : ℕ => (counting A x : ℝ) ^ c) := by
  sorry

/--
Narkiewicz [Na59] proved that, under the given assumptions (and perhaps swapping $A$ and $B$)
we must have $A(2x)/A(x)\to 1$ and $B(2x)/B(x)\to 2$.
-/
@[category research solved, AMS 11]
theorem erdos_785.variants.narkiewicz (A B : Set ℕ) (hA : A.Infinite) (hB : B.Infinite)
    (h : IsExactAdditiveComplement A B) :
    (Tendsto (fun x : ℕ => (counting A (2 * x) : ℝ) / (counting A x : ℝ)) atTop (𝓝 1) ∧
      Tendsto (fun x : ℕ => (counting B (2 * x) : ℝ) / (counting B x : ℝ)) atTop (𝓝 2)) ∨
    (Tendsto (fun x : ℕ => (counting B (2 * x) : ℝ) / (counting B x : ℝ)) atTop (𝓝 1) ∧
      Tendsto (fun x : ℕ => (counting A (2 * x) : ℝ) / (counting A x : ℝ))
        atTop (𝓝 2)) := by
  sorry

/--
Ruzsa [Ru17] has constructed, for any function $w(x)\to \infty$, such a pair of sets with
\[A(x)B(x)-x<w(x)\]
for infinitely many $x$.
-/
@[category research solved, AMS 11]
theorem erdos_785.variants.ruzsa_upper_bound (w : ℕ → ℝ) (hw : Tendsto w atTop atTop) :
    ∃ A B : Set ℕ, A.Infinite ∧ B.Infinite ∧ IsExactAdditiveComplement A B ∧
      ∃ᶠ x : ℕ in atTop, (counting A x * counting B x : ℝ) - (x : ℝ) < w x := by
  sorry

/--
Ruzsa [Ru17] proves that, if $a^*(x)=\max A \cap [1,x]$ and $A$ and $B$ satisfy the conditions
in the problem then (after possibly changing the roles of $A$ and $B$)
\[A(x)B(x)-x > (1-o(1))\frac{a^*(x)}{A(x)}.\]
-/
@[category research solved, AMS 11]
theorem erdos_785.variants.ruzsa_lower_bound (A B : Set ℕ) (hA : A.Infinite) (hB : B.Infinite)
    (h : IsExactAdditiveComplement A B) :
    (∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
        (1 - ε) * (aStar A x : ℝ) / (counting A x : ℝ)
          < (counting A x * counting B x : ℝ) - (x : ℝ)) ∨
    (∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
        (1 - ε) * (aStar B x : ℝ) / (counting B x : ℝ)
          < (counting A x * counting B x : ℝ) - (x : ℝ)) := by
  sorry

/--
Chen and Fang [ChFa10] proved the stronger statement that $A(x)B(x)-x\to \infty$ if $A$ and $B$
are infinite sets such that $A+B$ contains all large integers and
\[\limsup_{x\to \infty}\frac{A(x)B(x)}{x}<\frac{5}{4}.\]
They later [ChFa14] improved $5/4$ to $3-\sqrt{3}\approx 1.268$.
-/
@[category research solved, AMS 11]
theorem erdos_785.variants.chen_fang_limsup (A B : Set ℕ) (hA : A.Infinite) (hB : B.Infinite)
    (h : IsAdditiveComplement A B)
    (hlim : limsup (fun x : ℕ => ((counting A x * counting B x : ℝ) / (x : ℝ) : EReal)) atTop
      < ((3 - Real.sqrt 3 : ℝ) : EReal)) :
    Tendsto (fun x : ℕ => (counting A x * counting B x : ℝ) - (x : ℝ)) atTop atTop := by
  sorry

/--
Chen conjectures that this should be true with $3/2$.
-/
@[category research open, AMS 11]
theorem erdos_785.variants.chen_conjecture : answer(sorry) ↔
    ∀ A B : Set ℕ, A.Infinite → B.Infinite → IsAdditiveComplement A B →
      limsup (fun x : ℕ => ((counting A x * counting B x : ℝ) / (x : ℝ) : EReal)) atTop
          < ((3 / 2 : ℝ) : EReal) →
        Tendsto (fun x : ℕ => (counting A x * counting B x : ℝ) - (x : ℝ)) atTop atTop := by
  sorry

/--
This is sharp, as Chen and Fang [ChFa11] also proved that there exist such $A$ and $B$ with
\[\limsup_{x\to \infty}\frac{A(x)B(x)}{x}=\frac{3}{2}\]
for which $A(x)B(x)-x=1$ for infinitely many $x$.
-/
@[category research solved, AMS 11]
theorem erdos_785.variants.chen_fang_sharp :
    ∃ A B : Set ℕ, A.Infinite ∧ B.Infinite ∧ IsAdditiveComplement A B ∧
      limsup (fun x : ℕ => ((counting A x * counting B x : ℝ) / (x : ℝ) : EReal)) atTop
          = ((3 / 2 : ℝ) : EReal) ∧
      ∃ᶠ x : ℕ in atTop, (counting A x * counting B x : ℝ) - (x : ℝ) = 1 := by
  sorry

end Erdos785
