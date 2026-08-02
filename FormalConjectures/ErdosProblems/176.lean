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
# Erdős Problem 176

*References:*
- [erdosproblems.com/176](https://www.erdosproblems.com/176)
- [Sp73] Spencer, J. Problems 185. Bull. Canad. Math. Soc. (1973), 185.
- [Ly26] Lystad, T. A. Machine-checkable UNSAT certificates for exact values of
  Erdős discrepancy thresholds. [Zenodo v1.2](https://doi.org/10.5281/zenodo.21761884).
-/

open Set ENat

namespace Erdos176

/--
Every coloring of $\{1,\ldots,N\}$ by $\{-1,1\}$ has a $k$-term arithmetic
progression on which the absolute value of the sum is at least $\ell$.
-/
def ForcesDiscrepancy (N k : ℕ) (ℓ : ℝ) : Prop :=
  ∀ f : Finset.Icc 1 N → ℤ, (∀ n, f n = -1 ∨ f n = 1) →
    ∃ P : Finset (Finset.Icc 1 N),
      ({(n : ℕ) | n ∈ P} : Set ℕ).IsAPOfLength k ∧
        ℓ ≤ |((∑ n ∈ P, f n : ℤ) : ℝ)|

/--
The least $N$ such that every $\{-1,1\}$-coloring of $\{1,\ldots,N\}$
forces discrepancy at least $\ell$ on a $k$-term arithmetic progression.
The value is `⊤` if no finite such $N$ exists.
-/
noncomputable def discrepancyAPNumber (k : ℕ) (ℓ : ℝ) : ℕ∞ :=
  sInf ((fun N : ℕ ↦ (N : ℕ∞)) '' {N : ℕ | ForcesDiscrepancy N k ℓ})

/--
For every meaningful proportional threshold $0 < c \leq 1$, is
$N(k,ck)$ at most exponential in $k$?

The source says "for any $c>0$". Values $c>1$ are impossible because a
$k$-term $\{-1,1\}$ sum has absolute value at most $k$, so the statement
records the nontrivial range and retains the boundary case $c=1$.
-/
@[category research open, AMS 5]
theorem erdos_176.parts.i : answer(sorry) ↔
    ∀ c : ℝ, 0 < c → c ≤ 1 → ∃ C : ℕ, 1 < C ∧ ∀ k : ℕ, 2 ≤ k →
      discrepancyAPNumber k (c * k) ≤ (C ^ k : ℕ) := by
  sorry

/-- Is $N(k,2)$ at most exponential in $k$? -/
@[category research open, AMS 5]
theorem erdos_176.parts.ii : answer(sorry) ↔
    ∃ C : ℕ, 1 < C ∧ ∀ k : ℕ, 2 ≤ k →
      discrepancyAPNumber k 2 ≤ (C ^ k : ℕ) := by
  sorry

/-- Is $N(k,\sqrt{k})$ at most exponential in $k$? -/
@[category research open, AMS 5]
theorem erdos_176.parts.iii : answer(sorry) ↔
    ∃ C : ℕ, 1 < C ∧ ∀ k : ℕ, 2 ≤ k →
      discrepancyAPNumber k (Real.sqrt k) ≤ (C ^ k : ℕ) := by
  sorry

/--
$N(13,2)=158$: there is an avoiding coloring at $N=157$, while the
$N=158$ instance is unsatisfiable. Both sides have exact machine-checkable
certificates in [Ly26].
-/
@[category research solved, AMS 5]
theorem erdos_176.variants.n_13_two : discrepancyAPNumber 13 2 = 158 := by
  sorry

/--
$N(15,2)=225$: there is an avoiding coloring at $N=224$, while the
$N=225$ instance is unsatisfiable. Both sides have exact machine-checkable
certificates in [Ly26].
-/
@[category research solved, AMS 5]
theorem erdos_176.variants.n_15_two : discrepancyAPNumber 15 2 = 225 := by
  sorry

end Erdos176
