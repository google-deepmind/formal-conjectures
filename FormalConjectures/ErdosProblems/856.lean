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
# Erdős Problem 856

*References:*
- [erdosproblems.com/856](https://www.erdosproblems.com/856)
- [Er70] Erdős, Paul, *Some extremal problems in combinatorial number theory*. Mathematical Essays
  Dedicated to A. J. Macintyre (1970), 123-133.
- [TaZh25b] Q. Tang and S. Zhang, *Harmonic LCM patterns and sunflower-free capacity*.
  arXiv:2512.20055 (2025).
-/

open Asymptotics Filter

namespace Erdos856

/--
A finite set has the same pairwise least common multiple if there is some `ℓ` such that
every two distinct elements have least common multiple `ℓ`. The diagonal is excluded,
since `a.lcm a = a`.
-/
def SamePairwiseLcm (S : Finset ℕ) : Prop :=
  ∃ ℓ, ∀ a ∈ S, ∀ b ∈ S, a ≠ b → a.lcm b = ℓ

/--
`A` contains no subset of size `k` with the same pairwise least common multiple.
-/
def IsAdmissible (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ S ⊆ A, S.card = k → ¬ SamePairwiseLcm S

/-- The reciprocal sum `∑_{n ∈ A} 1/n` of the problem. -/
def reciprocalMass (A : Finset ℕ) : ℚ := ∑ a ∈ A, (1 : ℚ) / a

/--
The largest reciprocal sum `∑_{n ∈ A} 1/n` over admissible `A ⊆ {1, …, N}`.
The empty set is admissible and contributes `0`.
-/
noncomputable def f (k N : ℕ) : ℝ :=
  sSup ((fun A => (reciprocalMass A : ℝ)) ''
    {A : Finset ℕ | A ⊆ Finset.Icc 1 N ∧ IsAdmissible k A})

/--
Let $k\geq 3$ and $f_k(N)$ be the maximum value of $\sum_{n\in A}\frac{1}{n}$, where $A$ ranges
over all subsets of $\{1,\ldots,N\}$ which contain no subset of size $k$ with the same pairwise
least common multiple.

Estimate $f_k(N)$.
-/
@[category research open, AMS 11]
theorem erdos_856 :
    let g : ℕ → ℕ → ℝ := answer(sorry)
    ∀ k : ℕ, 3 ≤ k → f k ~[atTop] g k := by
  sorry

/--
Erdős [Er70] notes that
$$f_k(N) \ll \frac{\log N}{\log\log N}.$$
-/
@[category research solved, AMS 11]
theorem erdos_856.variants.erdos (k : ℕ) (hk : 3 ≤ k) :
    f k =O[atTop] fun N : ℕ => Real.log N / Real.log (Real.log N) := by
  sorry

/--
Tang and Zhang [TaZh25b] proved
$$(\log N)^{b_k-o(1)}\leq f_k(N)\leq (\log N)^{c_k+o(1)}$$
for some constants $0<b_k\leq c_k\leq 1$.
-/
@[category research solved, AMS 11]
theorem erdos_856.variants.tang_zhang (k : ℕ) (hk : 3 ≤ k) :
    ∃ b c : ℝ, 0 < b ∧ b ≤ c ∧ c ≤ 1 ∧
      ∃ ε : ℕ → ℝ, ε =o[atTop] (1 : ℕ → ℝ) ∧
        ∀ᶠ N in atTop,
          Real.log N ^ (b - ε N) ≤ f k N ∧ f k N ≤ Real.log N ^ (c + ε N) := by
  sorry

/--
Tang and Zhang [TaZh25b] proved in particular
$$(\log N)^{0.438}\leq f_3(N)\leq (\log N)^{0.889}$$
for all large $N$.
-/
@[category research solved, AMS 11]
theorem erdos_856.variants.tang_zhang_three :
    ∀ᶠ N in atTop,
      Real.log N ^ (0.438 : ℝ) ≤ f 3 N ∧ f 3 N ≤ Real.log N ^ (0.889 : ℝ) := by
  sorry

end Erdos856
