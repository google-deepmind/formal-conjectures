/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 999

*References:*
- [erdosproblems.com/999](https://www.erdosproblems.com/999)
- [Er64b] Erdős, P., _Problems and results on diophantine approximations_. Compositio Math.
  (1964), 52-65.
- [KoMa20] Koukoulopoulos, Dimitris and Maynard, James, _On the Duffin-Schaeffer conjecture_.
  Ann. of Math. (2) (2020), 251--307.
-/

@[expose] public section

open MeasureTheory

namespace Erdos999

/-- `x` is *approximable* with respect to `f` if
$$\left\lvert x-\frac{p}{q}\right\rvert < \frac{f(q)}{q}$$
has infinitely many solutions with $(p,q)=1$. -/
def IsApproximable (f : ℕ → ℝ) (x : ℝ) : Prop :=
  {q : ℕ | 0 < q ∧ ∃ p : ℤ, Int.gcd p q = 1 ∧ |x - p / q| < f q / q}.Infinite

/--
For any function $f:\mathbb{N}\to \mathbb{R}_{\geq 0}$ the property that, for almost all
$\alpha$
$$\left\lvert \alpha-\frac{p}{q}\right\rvert < \frac{f(q)}{q}$$
has infinitely many solutions with $(p,q)=1$, is equivalent to
$$\sum_{q\geq 1}\phi(q)\frac{f(q)}{q}=\infty.$$

The Duffin–Schaeffer conjecture. It is easy to prove that the latter follows from the former.
Erdős proved this in the special case when $f(q)q$ is bounded. The full conjecture was proved by
Koukoulopoulos and Maynard [KoMa20].
-/
@[category research solved, AMS 11]
theorem erdos_999 : answer(True) ↔ ∀ f : ℕ → ℝ, (∀ q, 0 ≤ f q) →
    ((∀ᵐ x : ℝ, IsApproximable f x) ↔
      ¬ Summable fun q : ℕ ↦ (Nat.totient q : ℝ) * f q / q) := by
  sorry

/-- It is easy to prove that divergence of the series follows from approximability almost
everywhere (the Borel–Cantelli lemma). -/
@[category textbook, AMS 11]
theorem erdos_999.variants.easy_direction (f : ℕ → ℝ) (hf : ∀ q, 0 ≤ f q)
    (h : ∀ᵐ x : ℝ, IsApproximable f x) :
    ¬ Summable fun q : ℕ ↦ (Nat.totient q : ℝ) * f q / q := by
  sorry

/-- Erdős [Er64b] proved the conjecture in the special case when $f(q)q$ is bounded. -/
@[category research solved, AMS 11]
theorem erdos_999.variants.erdos (f : ℕ → ℝ) (hf : ∀ q, 0 ≤ f q)
    (hb : ∃ C : ℝ, ∀ q, f q * q ≤ C) :
    (∀ᵐ x : ℝ, IsApproximable f x) ↔
      ¬ Summable fun q : ℕ ↦ (Nat.totient q : ℝ) * f q / q := by
  sorry

end Erdos999
