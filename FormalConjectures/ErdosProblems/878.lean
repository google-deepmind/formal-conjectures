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
# Erdős Problem 878

*Reference:* [erdosproblems.com/878](https://www.erdosproblems.com/878)
-/

open Asymptotics Filter Finset

namespace Erdos878

/--
If $n=\prod p_i^{k_i}$ then $f(n)=\sum p_i^{\ell_i}$, where $\ell_i$ is chosen so that
$n\in [p_i^{\ell_i}, p_i^{\ell_i+1})$.
-/
noncomputable def f (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, p ^ Nat.log p n

/-- Pairwise coprime `a_i ≤ n` whose prime factors all divide `n`. -/
def Admissible (n : ℕ) (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, a ≤ n) ∧
    (∀ a ∈ A, a.primeFactors ⊆ n.primeFactors) ∧
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.Coprime a b)

/--
$F(n)=\max \sum a_i$ over pairwise coprime $a_i\leq n$ whose prime factors all divide $n$.
-/
noncomputable def F (n : ℕ) : ℕ :=
  sSup ((fun A => ∑ a ∈ A, a) '' {A : Finset ℕ | Admissible n A})

/-- $H(x)=\sum_{n<x} f(n)/n$. -/
noncomputable def H (x : ℕ) : ℝ :=
  ∑ n ∈ range x, (f n : ℝ) / n

/--
Is it true that, for almost all $n$,
$$f(n)=o(n\log\log n)$$
-/
@[category research open, AMS 11]
theorem erdos_878.parts.i : answer(sorry) ↔
    ∀ ε > (0 : ℝ), {n : ℕ | (f n : ℝ) ≤ ε * n * Real.log (Real.log n)}.HasDensity 1 := by
  sorry

/--
and
$$F(n) \gg n\log\log n?$$
-/
@[category research open, AMS 11]
theorem erdos_878.parts.ii : answer(sorry) ↔
    ∃ c > (0 : ℝ), {n : ℕ | c * n * Real.log (Real.log n) ≤ (F n : ℝ)}.HasDensity 1 := by
  sorry

/--
Is it true that
$$\max_{n\leq x}f(n)\sim \frac{x\log x}{\log\log x}?$$
-/
@[category research open, AMS 11]
theorem erdos_878.parts.iii : answer(sorry) ↔
    (fun x : ℕ => (sSup (f '' {n | n ≤ x}) : ℝ)) ~[atTop]
      fun x => x * Real.log x / Real.log (Real.log x) := by
  sorry

/--
Is it true that (for all $x$, or perhaps just for all large $x$)
$$\max_{n\leq x}f(n)=\max_{n\leq x}F(n)?$$
-/
@[category research open, AMS 11]
theorem erdos_878.parts.iv : answer(sorry) ↔
    ∀ᶠ x : ℕ in atTop, sSup (f '' {n | n ≤ x}) = sSup (F '' {n | n ≤ x}) := by
  sorry

/--
Find an asymptotic formula for the number of $n<x$ such that $f(n)=F(n)$.
-/
@[category research open, AMS 11]
theorem erdos_878.parts.v :
    let g : ℕ → ℝ := answer(sorry)
    (fun x : ℕ => ((range x).filter fun n => f n = F n).card : ℝ) ~[atTop] g := by
  sorry

/--
Find an asymptotic formula for
$$H(x)=\sum_{n<x}\frac{f(n)}{n}.$$
-/
@[category research open, AMS 11]
theorem erdos_878.parts.vi :
    let g : ℕ → ℝ := answer(sorry)
    H ~[atTop] g := by
  sorry

/--
Is it true that
$$H(x) \ll x\log\log\log\log x?$$
-/
@[category research open, AMS 11]
theorem erdos_878.parts.vii : answer(sorry) ↔
    H ≪ fun x : ℕ =>
      (x : ℝ) * Real.log (Real.log (Real.log (Real.log x))) := by
  sorry

end Erdos878
