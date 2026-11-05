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
# Erdős Problem 122

*References:*
- [erdosproblems.com/122](https://www.erdosproblems.com/122)
- [Er97] Erdős, Paul, *Problems in number theory*. New Zealand J. Math. (1997), 155-160.
- [Er97e] Erdős, Paul, *Some of my favourite unsolved problems*. Math. Japon. (1997), 527-537.
- [EPS97] Erdős, P. and Pomerance, C. and Sárközy, A., *On locally repeated values of certain
  arithmetic functions. IV*. Ramanujan J. (1997), 227-241.
-/

@[expose] public section

open Filter Topology

namespace Erdos122

/-- $F(n)/f(n) \to 0$ for almost all $n$: the limit holds along a set of natural density $1$. -/
def RatioTendsToZeroAlmostAll (F : ℕ → ℝ) (f : ℕ → ℕ) : Prop :=
  ∃ S : Set ℕ, S.HasDensity 1 ∧ Tendsto (fun n ↦ F n / f n) (atTop ⊓ 𝓟 S) (𝓝 0)

/-- The number of $n \in \mathbb{N}$ with $n + f(n) \in (x, x + F(x))$. This set is finite
since $n \le n + f(n) < x + F(x)$. -/
noncomputable def count (f : ℕ → ℕ) (F : ℕ → ℝ) (x : ℕ) : ℕ :=
  {n : ℕ | (x : ℝ) < (n + f n : ℕ) ∧ ((n + f n : ℕ) : ℝ) < x + F x}.ncard

/-- The property of $f$ in Erdős Problem 122: for every $F$ with $F(x) \to \infty$ and
$F(n)/f(n) \to 0$ for almost all $n$, there are infinitely many $x$ with
$\operatorname{count}(x) > C F(x)$, for every $C$.

We read "there are infinitely many $x$ such that $\operatorname{count}(x)/F(x) \to \infty$" as
$\limsup_{x} \operatorname{count}(x)/F(x) = \infty$. We require $F(x) \to \infty$ to exclude a
degenerate case: if $F(x) < 1$ for all $x$, the interval $(x, x + F(x))$ contains no integer, so
no $f$ has the property. -/
def Erdos122Property (f : ℕ → ℕ) : Prop :=
  ∀ F : ℕ → ℝ, Tendsto F atTop atTop → RatioTendsToZeroAlmostAll F f →
    ∀ C : ℝ, ∃ᶠ x in atTop, C * F x < count f F x

/--
For which number theoretic functions $f$ is it true that, for any $F(n)$ such that
$F(n)/f(n)\to 0$ for almost all $n$, there are infinitely many $x$ such that
$$\frac{\#\{ n\in \mathbb{N} : n+f(n)\in (x,x+F(x))\}}{F(x)}\to \infty?$$
-/
@[category research open, AMS 11]
theorem erdos_122 : {f : ℕ → ℕ | Erdos122Property f} = answer(sorry) := by
  sorry

/-- Erdős, Pomerance and Sárközy [EPS97] proved the property for the divisor function
$\tau(n)$. -/
@[category research solved, AMS 11]
theorem erdos_122.variants.divisor_count : Erdos122Property fun n ↦ n.divisors.card := by
  sorry

/-- Erdős, Pomerance and Sárközy [EPS97] proved the property for $\omega(n)$, the number of
distinct prime divisors of $n$. -/
@[category research solved, AMS 11]
theorem erdos_122.variants.omega : Erdos122Property fun n ↦ n.primeFactors.card := by
  sorry

/-- Erdős conjectured that the property fails for Euler's totient function $\phi(n)$. -/
@[category research open, AMS 11]
theorem erdos_122.variants.totient : ¬ Erdos122Property Nat.totient := by
  sorry

/-- Erdős conjectured that the property fails for the sum of divisors function $\sigma(n)$. -/
@[category research open, AMS 11]
theorem erdos_122.variants.sigma : ¬ Erdos122Property fun n ↦ ∑ d ∈ n.divisors, d := by
  sorry

/-- The zero function does not have the property. Take $F(x) = x$. Then
$\operatorname{count}(x) \le x = F(x)$. Note that $F(n)/0 = 0$ in Lean. -/
@[category test, AMS 11]
theorem not_erdos122Property_zero : ¬ Erdos122Property fun _ ↦ 0 := by
  intro h
  refine h (fun x ↦ (x : ℝ)) tendsto_natCast_atTop_atTop ⟨Set.univ, by simp, by simp⟩ 1 ?_
  filter_upwards with x
  rw [one_mul, not_lt]
  have hsub : {n : ℕ | (x : ℝ) < ((n + 0 : ℕ) : ℝ) ∧ ((n + 0 : ℕ) : ℝ) < x + x} ⊆
      ↑(Finset.Ioo x (x + x)) := by
    intro n hn
    simp only [Set.mem_ofPred_eq, add_zero] at hn
    simp only [Finset.coe_Ioo, Set.mem_Ioo]
    exact ⟨by exact_mod_cast hn.1, by exact_mod_cast hn.2⟩
  have h2 : count (fun _ ↦ 0) (fun x ↦ (x : ℝ)) x ≤ x :=
    (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans
      (by rw [Set.ncard_coe_finset, Nat.card_Ioo]; omega)
  exact_mod_cast h2

end Erdos122
