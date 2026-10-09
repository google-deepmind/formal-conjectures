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
# Erdős Problem 460

*References:*
- [erdosproblems.com/460](https://www.erdosproblems.com/460)
- [Er77c] Erdős, Paul, *Problems and results on combinatorial number theory. III*.
  Number theory day (1977), 43–72, p. 64.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
  number theory*. Monographies de L'Enseignement Mathematique (1980), p. 91.
-/

@[expose] public section

namespace Erdos460

/-- Selected values through candidate t, including zero when `includeZero` is true. -/
def greedyPrefix (includeZero : Bool) (n : ℕ) : ℕ → Finset ℕ
  | 0 => if includeZero then {0} else ∅
  | t + 1 =>
      let s := greedyPrefix includeZero n t
      if t + 1 = 1 ∨ ∀ b ∈ s, Nat.Coprime (n - (t + 1)) (n - b)
      then insert (t + 1) s else s

/-- Exactly the positive selected values strictly below n. -/
def selected (includeZero : Bool) (n : ℕ) : Finset ℕ :=
  (greedyPrefix includeZero n (n - 1)).filter (fun a => 0 < a ∧ a < n)

/-- The original subsum condition, including primes equal to a. -/
def Proper (n a : ℕ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ p ≤ a ∧ p ∣ n - a

/-- No prime at most a divides n-a; this handles n-a=1 correctly. -/
def Rough (n a : ℕ) : Prop := ¬ Proper n a

noncomputable def totalSum (includeZero : Bool) (n : ℕ) : ℝ :=
  ∑ a ∈ selected includeZero n, (1 : ℝ) / (a : ℝ)

noncomputable def properSum (includeZero : Bool) (n : ℕ) : ℝ := by
  classical
  exact ∑ a ∈ (selected includeZero n).filter (Proper n), (1 : ℝ) / (a : ℝ)

noncomputable def roughSum (includeZero : Bool) (n : ℕ) : ℝ := by
  classical
  exact ∑ a ∈ (selected includeZero n).filter (Rough n), (1 : ℝ) / (a : ℝ)

/--
Let $a_0=0$ and $a_1=1$, and in general define $a_k$ to be the least integer
$>a_{k-1}$ for which $(n-a_k,n-a_i)=1$ for all $0\leq i<k$. Does
$$\sum_{0<a_i<n}\frac{1}{a_i}\to \infty$$
as $n\to \infty$?

The finite scan records the positive selected values below $n$. The prescribed
$a_1=1$ is inserted unconditionally; subsequent candidates must pass the gcd tests.
-/
@[category research open, AMS 11]
theorem erdos_460.parts.i : answer(sorry) ↔
    Filter.Tendsto (totalSum true) Filter.atTop Filter.atTop := by sorry

/-- Does the sum restricted to those $a_i$ for which $n-a_i$ is divisible by some
prime $\leq a_i$ tend to infinity as $n\to\infty$? -/
@[category research open, AMS 11]
theorem erdos_460.parts.ii : answer(sorry) ↔
    Filter.Tendsto (properSum true) Filter.atTop Filter.atTop := by sorry

/-- Does the complementary reciprocal subsum tend to infinity as $n\to\infty$? -/
@[category research open, AMS 11]
theorem erdos_460.parts.iii : answer(sorry) ↔
    Filter.Tendsto (roughSum true) Filter.atTop Filter.atTop := by sorry

/-- The formulation in [ErGr80] omits the gcd test against $a_0$. Does its truncated
reciprocal sum tend to infinity as $n\to\infty$? -/
@[category research open, AMS 11]
theorem erdos_460.variants.erdos_graham : answer(sorry) ↔
    Filter.Tendsto (totalSum false) Filter.atTop Filter.atTop := by sorry

/-- At $n=6$, testing against zero selects only $1$ and $5$. -/
@[category test, AMS 11]
theorem selected_six : selected true 6 = {1, 5} := by decide

/-- Omitting the zero test also selects $2$ and $3$ at $n=6$. -/
@[category test, AMS 11]
theorem selected_six_variant : selected false 6 = {1, 2, 3, 5} := by decide

end Erdos460
