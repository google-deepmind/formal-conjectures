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
# Erdős Problem 302

*References:*
- [erdosproblems.com/302](https://www.erdosproblems.com/302)
- [BrRo91] Brown, Tom C. and Rödl, Voijtech, Monochromatic solutions to equations with unit
  fractions. Bull. Austral. Math. Soc. (1991), 387-392.
- [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number
  theory. Monographies de L'Enseignement Mathematique (1980).
- [va25](https://github.com/Woett/Mathematical-shorts/blob/main/Two-colouring%20and%20density%20lead%20to%20solutions%20to%20an%20equation%20in%20unit%20fractions.pdf)
-/

open Filter Finset
open scoped Topology

namespace Erdos302

/--
A finite set $A$ of positive integers admits no solution to
$\frac{1}{a} = \frac{1}{b} + \frac{1}{c}$ with $a, b, c$ distinct elements of $A$.
-/
def NoUnitFractionTriple (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c →
    (1 : ℚ) / a ≠ (1 : ℚ) / b + (1 : ℚ) / c

/--
$f N$ is the size of the largest $A ⊆ \{1, …, N\}$ containing no solution to
$\frac{1}{a} = \frac{1}{b} + \frac{1}{c}$ with distinct $a, b, c ∈ A$.
-/
def IsMaxNoTripleCard (N m : ℕ) : Prop :=
  IsGreatest {k | ∃ A ⊆ Finset.Icc 1 N, NoUnitFractionTriple A ∧ A.card = k} m

/--
Let $f(N)$ be the size of the largest $A\subseteq \{1,\ldots,N\}$ such that there are no
solutions to
$$\frac{1}{a}= \frac{1}{b}+\frac{1}{c}$$
with distinct $a,b,c\in A$? Estimate $f(N)$.

The colouring version of this is [303], which was solved by Brown and Rödl [BrRo91].
-/
@[category research open, AMS 11]
theorem erdos_302.parts.i (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N)) :
    Tendsto (fun N : ℕ => (f N : ℝ) / N) atTop (𝓝 answer(sorry)) := by
  sorry

/--
In particular, is $f(N)=(\tfrac{1}{2}+o(1))N$?

This is false: it is contradicted by Cambie's lower bound of $(5/8+o(1))N$ recorded below,
since $5/8 > 1/2$.
-/
@[category research solved, AMS 11]
theorem erdos_302.parts.ii (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N)) :
    ¬ Tendsto (fun N : ℕ => (f N : ℝ) / N) atTop (𝓝 ((1 : ℝ) / 2)) := by
  sorry

/--
One can take either $A$ to be all odd integers in $[1,N]$ or all integers in $[N/2,N]$ to show
$f(N)\geq (1/2+o(1))N$.
-/
@[category research solved, AMS 11]
theorem erdos_302.variants.lower_half (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((1 : ℝ) / 2 - ε) * N ≤ f N := by
  sorry

/--
Stijn Cambie has observed that
$$f(N)\geq (5/8+o(1))N,$$
taking $A$ to be all odd integers $\leq N/4$ and all integers in $[N/2,N]$.
-/
@[category research solved, AMS 11]
theorem erdos_302.variants.lower_five_eighths (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((5 : ℝ) / 8 - ε) * N ≤ f N := by
  sorry

/--
Wouter van Doorn has proved [va25] that
$$f(N) \leq (9/10+o(1))N.$$
-/
@[category research solved, AMS 11]
theorem erdos_302.variants.upper_nine_tenths (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (f N : ℝ) ≤ ((9 : ℝ) / 10 + ε) * N := by
  sorry

end Erdos302
