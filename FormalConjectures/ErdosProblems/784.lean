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
# Erdős Problem 784

*Reference:* [erdosproblems.com/784](https://www.erdosproblems.com/784)
-/

@[expose] public section

namespace Erdos784

/-- The integers `m ≤ n` that are not divisible by any element of `A`. -/
def nonmultiples (A : Finset ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun m => ∀ a ∈ A, ¬ a ∣ m

/--
An admissible set for the problem at `n` with constant `C`:
$A \subseteq \{2, \ldots, n\}$ with harmonic sum at most $C$.

The problem page records the intended reading of the original statement over
$A \subseteq \{2, \ldots, \lfloor x \rfloor\}$ (defining $H_C(x)$ with this restriction):
taken literally over $A \subseteq \{1, \ldots, n\}$, the case $C \geq 1$ would be
trivially false via $A = \{1\}$.
-/
def Admissible (C : ℝ) (n : ℕ) (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, 2 ≤ a ∧ a ≤ n) ∧ ∑ a ∈ A, (1 : ℝ) / a ≤ C

/--
Erdős Problem 784, positive part. Let $0 < C \leq 1$. Then there is $c > 0$ (depending on $C$)
such that for all sufficiently large $n$, every admissible $A$ (i.e.
$A \subseteq \{2, \ldots, n\}$ with $\sum_{a \in A} \frac{1}{a} \leq C$) satisfies
$$\#\{m \leq n : a \nmid m \text{ for all } a \in A\} \geq \frac{n}{(\log n)^c}.$$

For $C = 1$ this is due to Ruzsa [Ru82] (lower bound $H_1(x) \gg x / \log x$; the matching
upper bound is due to Saias [Sa98]). For $0 < C < 1$ a union bound gives the stronger lower
bound $(1 - C)x$.
-/
@[category research solved, question, AMS 11]
theorem erdos_784.positive (C : ℝ) (hC : 0 < C) (hC' : C ≤ 1) :
    ∃ c > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset ℕ, Admissible C n A →
      ((nonmultiples A n).card : ℝ) ≥ (n : ℝ) / (Real.log (n : ℝ)) ^ c := by
  sorry

/--
Erdős Problem 784, negative part. Let $C > 1$. Then the answer to the question is *no*: for
every $c > 0$ there are arbitrarily large $n$ and admissible sets $A$ with
$$\#\{m \leq n : a \nmid m \text{ for all } a \in A\} < \frac{n}{(\log n)^c}.$$

This follows from Ruzsa's construction [Ru82] $H_C(x) = x^{e^{1-C}+o(1)}$, sharpened by
Weingartner [We25] to $H_C(x) \asymp x^{e^{1-C}} / \log x$ for fixed $C > 1$.
-/
@[category research solved, question, AMS 11]
theorem erdos_784.negative (C : ℝ) (hC : 1 < C) :
    ¬ ∃ c > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset ℕ, Admissible C n A →
      ((nonmultiples A n).card : ℝ) ≥ (n : ℝ) / (Real.log (n : ℝ)) ^ c := by
  sorry

/-- The empty set is admissible for every `n` and leaves every integer `m ≤ n` a nonmultiple. -/
@[category test, AMS 11]
theorem nonmultiples_empty (n : ℕ) : nonmultiples ∅ n = Finset.Icc 1 n := by
  ext m
  simp [nonmultiples]

end Erdos784
