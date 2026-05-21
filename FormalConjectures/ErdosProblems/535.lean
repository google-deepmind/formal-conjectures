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
# Erdős Problem 535

*References:*
- [erdosproblems.com/535](https://www.erdosproblems.com/535)
- [Er64] P. Erdős, _On a problem in elementary number theory and a combinatorial problem_. Math.
  Comp. (1964), 644–646.
- [AbHa70] H. L. Abbott and D. Hanson, _An extremal problem in number theory_. Bull. London Math.
  Soc. (1970), 324–326.
- [Er73] P. Erdős, _Problems and results on combinatorial number theory_, in
  *A Survey of Combinatorial Theory*, North-Holland, 1973.
-/

open ArithmeticFunction
open Filter Real
open scoped omega Omega

namespace Erdos535

/-- No `r`-subset has constant pairwise GCD with coprime quotients. -/
def NoConstantPairwiseGcdCoprimeSubsets (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ S ⊆ A, S.card = r →
    ¬ (∃ d, 0 < d ∧ (S : Set ℕ).Pairwise (fun a b => Nat.gcd a b = d) ∧
      ∀ a ∈ S, ∃ b, a = d * b ∧ Nat.gcd b d = 1)

/--
All elements of `A` are positive and have exactly `k` prime factors,
counted with multiplicity.

Erdős [Er73] explains that Abbott pointed out the ordinary sunflower conjecture
does not seem to suffice for Problem 535; the corrected stronger auxiliary
statement uses $Ω$, not $ω$.
-/
def AllBigOmega (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, 1 ≤ a ∧ Ω a = k

/-- `f r N` is the maximum size of a subset `A ⊆ {1,…,N}` such that no `r`-element
subset of `A` has constant pairwise GCD. -/
noncomputable def f (r N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    (∀ S ⊆ A, S.card = r →
      ¬ (∃ d, (S : Set ℕ).Pairwise fun a b => Nat.gcd a b = d)) ∧
    A.card = k}

/--
Let $r \geq 3$, and let $f_r(N)$ denote the size of the largest subset of $\{1,\ldots,N\}$
such that no subset of size $r$ has the same pairwise greatest common divisor between all
elements. Erdős [Er64] proved that $f_3(N) > N^{c/\log\log N}$ for some constant $c > 0$, and
conjectured this should also be an upper bound; here we state the conjectural upper bound
for all $r \geq 3$.

See also [536].
-/
@[category research open, AMS 5 11]
theorem erdos_535 : ∀ r ≥ 3, ∃ c > (0 : ℝ),
    ∀ᶠ (N : ℕ) in atTop,
      (f r N : ℝ) ≤ (N : ℝ) ^ (c / log (log (N : ℝ))) := by
  sorry

/--
The first open case of Erdős Problem 535 is $r = 3$: there should exist $c > 0$ such that
$f_3(N) \leq N^{c/\log\log N}$ for all sufficiently large $N$.
-/
@[category research open, AMS 5 11]
theorem erdos_535.variants.first_open_case : ∃ c > (0 : ℝ),
    ∀ᶠ (N : ℕ) in atTop,
      (f 3 N : ℝ) ≤ (N : ℝ) ^ (c / log (log (N : ℝ))) := by
  sorry

/-- Erdős [Er64] proved that $f_r(N) \leq N^{3/4+o(1)}$ for all $r \geq 3$. -/
@[category research solved, AMS 5 11]
theorem erdos_535.variants.erdos_upper_bound {r : ℕ} (hr : 3 ≤ r) :
    ∀ ε > (0 : ℝ), ∀ᶠ (N : ℕ) in atTop,
      (f r N : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 4 + ε) := by
  sorry

/-- Erdős [Er64] proved that $f_3(N) > N^{c/\log\log N}$ for some constant $c > 0$. -/
@[category research solved, AMS 5 11]
theorem erdos_535.variants.lower_bound : ∃ c > (0 : ℝ),
    ∀ᶠ (N : ℕ) in atTop,
      (N : ℝ) ^ (c / log (log (N : ℝ))) ≤ (f 3 N : ℝ) := by
  sorry

/-- Abbott and Hanson [AbHa70] improved Erdős's upper bound to $f_r(N) \leq N^{1/2+o(1)}$
for all $r \geq 3$. -/
@[category research solved, AMS 5 11]
theorem erdos_535.variants.abbott_hanson {r : ℕ} (hr : 3 ≤ r) :
    ∀ ε > (0 : ℝ), ∀ᶠ (N : ℕ) in atTop,
      (f r N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  sorry

/--
Erdős [Er73] records that Abbott pointed out the ordinary sunflower conjecture
does not seem to suffice here. The stronger auxiliary conjecture uses $Ω(n)=k$,
i.e. prime factors counted with multiplicity; this stronger statement would imply
the conjectured upper bound for $f_r(N)$.
-/
@[category research open, AMS 5 11]
theorem erdos_535.variants.sunflower_strong {r : ℕ} (hr : 3 ≤ r) :
    ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k := by
  sorry

/--
For the stronger $Ω(n)=k$ variant above, the Erdős–Rado method gives the weaker
bound $c_r^k \cdot k!$; see Erdős [Er73].
-/
@[category research solved, AMS 5 11]
theorem erdos_535.variants.sunflower_erdos_rado {r : ℕ} (hr : 3 ≤ r) :
    ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k) := by
  sorry

end Erdos535
