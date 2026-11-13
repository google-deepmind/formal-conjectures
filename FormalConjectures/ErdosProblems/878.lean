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
# Erdős Problem 878

*References:*
- [erdosproblems.com/878](https://www.erdosproblems.com/878)
- [Er84e] Erdős, P., _On two unconventional number theoretic functions and on some
  related problems_. (1984), 113--121.
- [Ki26] Kitamura, K., _Erdős Problem #878 in Lean_,
  [GitHub repository](https://github.com/KitaKen1/erdos-878-lean/tree/d4a8eecf0606b3eee7342c2040a31c8c30eb5d76) (2026).
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology Real

namespace Erdos878

/-- The function $f(n)=\sum_{p\mid n}p^{\lfloor\log_p n\rfloor}$. -/
noncomputable def f (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, p ^ Nat.log p n

open scoped Classical in
/-- The function $F(n)$ from Erdős Problem 878, with nontrivial terms $a_i \ge 2$. -/
noncomputable def F (n : ℕ) : ℕ :=
  ((Finset.Icc 2 n).powerset.filter fun A ↦
    A ⊆ Finset.Icc 2 n ∧
      (A : Set ℕ).Pairwise (fun a b ↦ Nat.Coprime a b) ∧
      ∀ a ∈ A, ∀ p, p.Prime → p ∣ a → p ∣ n).sup fun A ↦ ∑ a ∈ A, a

/-- The maximum of an arithmetic function on $\{0,\ldots,x\}$. -/
noncomputable def maxUpTo (g : ℕ → ℕ) (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).sup g

/-- The function $H(x)=\sum_{1\le n<x}f(n)/n$. -/
noncomputable def H (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 x, (f n : ℝ) / n

set_option linter.style.formal_proof_palomar false in
/-- Is it true that, for almost all $n$, $f(n)=o(n\log\log n)$ and
$F(n)\gg n\log\log n$?

The answer is yes; a Lean proof is given in [Ki26]. -/
@[category research solved, question, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/erdos-878-lean/blob/d4a8eecf0606b3eee7342c2040a31c8c30eb5d76/lean/Erdos878/FixedLoss.lean#L120"]
theorem erdos_878.parts.i :
    ∃ A : Set ℕ, A.HasDensity 1 ∧
      (fun n : A ↦ (f n : ℝ)) =o[atTop]
        (fun n : A ↦ (n : ℝ) * Real.log (Real.log (n : ℝ))) ∧
      (fun n : A ↦ (n : ℝ) * Real.log (Real.log (n : ℝ))) =O[atTop]
        (fun n : A ↦ (F n : ℝ)) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- Is it true that $\max_{n\le x}f(n)\sim x\log x/\log\log x$?

The answer is yes; a Lean proof is given in [Ki26]. -/
@[category research solved, question, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/erdos-878-lean/blob/d4a8eecf0606b3eee7342c2040a31c8c30eb5d76/lean/Erdos878/TrackBEndpointParameters.lean#L630"]
theorem erdos_878.parts.ii :
    Tendsto (fun x : ℕ ↦
        (maxUpTo f x : ℝ) / ((x : ℝ) * Real.log x / Real.log (Real.log x)))
        atTop (𝓝 1) := by
  sorry

/-- Is it true that, for all $x$, $\max_{n\le x}f(n)=\max_{n\le x}F(n)$?
Barreto noted that this is false at $x=210$. -/
@[category research solved, question, AMS 11]
theorem erdos_878.parts.iii_all :
    ¬ ∀ x : ℕ, maxUpTo f x = maxUpTo F x := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- Is it true that, for all large $x$, $\max_{n\le x}f(n)=\max_{n\le x}F(n)$?

This is false, as formalized in Lean 4 by Ilia Pauzner using Gemini 4 Argon. -/
@[category research solved, question, AMS 11, formal_proof using formal_conjectures at "https://github.com/ilpauzner/formal-conjectures/blob/b7742e7d900ca30503c0dd4c940625a6d9cf0a0c/FormalConjectures/ErdosProblems/878.lean#L435"]
theorem erdos_878.parts.iii_eventually :
    ¬ ∀ᶠ x : ℕ in atTop, maxUpTo f x = maxUpTo F x := by
  sorry

def erdos_878.parts.iv.answer : ℕ → ℝ := by sorry

/-- Find an asymptotic formula for the number of $n<x$ such that $f(n)=F(n)$. -/
@[category research open, question value, AMS 11]
theorem erdos_878.parts.iv :
    (fun x : ℕ ↦
      (((Finset.Ico 1 x).filter fun n ↦ f n = F n).card : ℝ))
      ~[atTop] erdos_878.parts.iv.answer := by
  sorry

def erdos_878.parts.v.answer : ℕ → ℝ := by sorry

/-- Find an asymptotic formula for $H(x)=\sum_{n<x}f(n)/n$. -/
@[category research open, question value, AMS 11]
theorem erdos_878.parts.v :
    H ~[atTop] erdos_878.parts.v.answer := by
  sorry

/-- Is it true that $H(x)\ll x\log\log\log\log x$? -/
@[category research open, question, AMS 11]
theorem erdos_878.parts.vi :
    H =O[atTop] fun x : ℕ ↦
        (x : ℝ) * Real.log (Real.log (Real.log (Real.log (x : ℝ)))) := by
  sorry

/-- Erdős [Er84e] proved that $\max_{n\le x}f(n)\sim x\log x/\log\log x$
for a sequence of $x\to\infty$. -/
@[category research solved, AMS 11]
theorem erdos_878.variants.second_question_subsequence :
    ∃ X : ℕ → ℕ, Tendsto X atTop atTop ∧
      Tendsto (fun k : ℕ ↦
        (maxUpTo f (X k) : ℝ) /
          ((X k : ℝ) * Real.log (X k) / Real.log (Real.log (X k))))
        atTop (𝓝 1) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- For almost all $n$, $F(n)\sim \frac12 n\log\log n$.
A Lean proof is given in [Ki26]. -/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/erdos-878-lean/blob/d4a8eecf0606b3eee7342c2040a31c8c30eb5d76/lean/Erdos878/SharpFirstAsymptotic.lean#L168"]
theorem erdos_878.variants.proposed_first_question_sharp :
    ∃ A : Set ℕ, A.HasDensity 1 ∧
      Tendsto (fun n : A ↦
        (F n : ℝ) / ((n : ℝ) * Real.log (Real.log (n : ℝ))))
        atTop (𝓝 (1 / 2 : ℝ)) := by
  sorry

/-- Erdős [Er84e] showed that $\limsup_{x\to\infty}H(x)/x=\infty$. -/
@[category research solved, AMS 11]
theorem erdos_878.variants.H_div_self_limsup_infinite :
    ∀ C : ℝ, ∃ᶠ x : ℕ in atTop, C ≤ H x / (x : ℝ) := by
  sorry

/-- Erdős [Er84e] showed that $\liminf_{x\to\infty}H(x)/x<\infty$. -/
@[category research solved, AMS 11]
theorem erdos_878.variants.H_div_self_liminf_finite :
    ∃ C : ℝ, ∃ᶠ x : ℕ in atTop, H x / (x : ℝ) ≤ C := by
  sorry

/-- Erdős [Er84e] proved that $H(x)\ll x\log\log\log x$. -/
@[category research solved, AMS 11]
theorem erdos_878.variants.H_upper_triple_log :
    H =O[atTop] fun x : ℕ ↦
      (x : ℝ) * Real.log (Real.log (Real.log (x : ℝ))) := by
  sorry

/-- Erdős [Er84e] proved that $x\log\log\log\log x\ll H(x)$;
this entry records the infinitely-often consequence. -/
@[category research solved, AMS 11]
theorem erdos_878.variants.H_lower_quadruple_log_infinitely_often :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ x : ℕ in atTop,
      c * ((x : ℝ) * Real.log (Real.log (Real.log (Real.log (x : ℝ))))) ≤ H x := by
  sorry

/-- The function $h(x)=\max_{n\le x}\omega(n)$ from [Er84e]. -/
noncomputable def h (x : ℕ) : ℕ :=
  maxUpTo (fun n ↦ n.primeFactors.card) x

/-- The function $m(x)=\max_{n\le x}f(n)$ from [Er84e]. -/
noncomputable def m (x : ℕ) : ℕ := maxUpTo f x

set_option linter.style.formal_proof_palomar false in
/-- Formula (17) of [Er84e]: does $(x h(x)-m(x))/x\to\infty$?

The answer is yes; a Lean proof is given in [Ki26]. -/
@[category research solved, question, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/erdos-878-lean/blob/d4a8eecf0606b3eee7342c2040a31c8c30eb5d76/lean/Erdos878/Formula17.lean#L192"]
theorem erdos_878.variants.original_formula_17 :
    Tendsto (fun x : ℕ ↦
        ((x * h x - m x : ℕ) : ℝ) / (x : ℝ)) atTop atTop := by
  sorry

end Erdos878
