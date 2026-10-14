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
# Erdős Problem 873

*References:*
- [erdosproblems.com/873](https://www.erdosproblems.com/873)
- [Er92c] Erdős, P., Some of my forgotten problems in number theory. Hardy-Ramanujan J. 15
  (1992), 34-50.
-/

@[expose] public section

namespace Erdos873

/-- Let $a$ be some sequence of natural numbers. We set $F(A,X,k)$ to be the count of
the number of $i$ such that $[a_i,a_{i+1}, \dots ,a_{i+k−1}] < X$,
where the left-hand side is the least common multiple. -/
noncomputable abbrev F (a : ℕ → ℕ) (X : ℝ) (k : ℕ) : ℕ∞ :=
  {i : ℕ | (Finset.range k).lcm (fun m => a (i + m)) < X}.encard

/-- Let $A = \{a_1 < a_2 < \dots\} \subseteq \mathbb{N}$ and let $F(A,X,k)$ count the number of $i$
such that $[a_i,a_{i+1}, \dots ,a_{i+k−1}] < X$, where the left-hand side is the least common
multiple. Is it true that, for every $\epsilon > 0$, there exists some $k$ such that
$F(A,X,k) < X^\epsilon$?-/
@[category research open, AMS 11]
theorem erdos_873 : answer(sorry) ↔ ∀ᵉ (a : ℕ → ℕ) (ε > (0 : ℝ)), 0 < a 0 → StrictMono a →
    ∃ k, ∀ X > 0, F a X k < (X^ε).toEReal := by
  sorry

/-
## Statements following the original question

The paper states (2), (3), and then conjectures an all-X strengthening of (3).
-/

/-- The upper bound (2). -/
@[category research solved, AMS 11]
theorem erdos_873.variants.triple_upper_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℕ → ℕ), 0 < a 0 → StrictMono a →
        ∀ᶠ X : ℝ in Filter.atTop,
          (F a X 3 : EReal) ≤
            (C * X ^ (1 / 3 : ℝ) * Real.log X).toEReal := by
  sorry

/-- The infinitely-often lower bound (3). -/
@[category research solved, AMS 11]
theorem erdos_873.variants.triple_lower_bound_infinitely_often :
    ∃ (a : ℕ → ℕ) (c : ℝ),
      0 < a 0 ∧ StrictMono a ∧ 0 < c ∧
        ∀ X₀ : ℝ, ∃ X > X₀,
          (c * X ^ (1 / 3 : ℝ) * Real.log X).toEReal ≤ (F a X 3 : EReal) := by
  sorry

/-- There may be a sequence for which the lower bound in (3) holds for every $X$, that is, for
all sufficiently large $X$ rather than only for infinitely many $X$. (Asking it for every
$X > 0$ fails trivially: the lcm of three distinct positive integers is at least $4$, so
$F(A,X,3) = 0$ for $X \le 4$.) -/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/KitaKen1/erdos-873-lean/blob/44cbf183239517795522bd3f18124b08c095cc6d/lean/RealBridge.lean#L138-L146"]
theorem erdos_873.variants.supplement_all_scale :
    answer(False) ↔
      ∃ (a : ℕ → ℕ) (c : ℝ),
        0 < a 0 ∧ StrictMono a ∧ 0 < c ∧
          ∀ᶠ X : ℝ in Filter.atTop,
            (c * X ^ (1 / 3 : ℝ) * Real.log X).toEReal ≤ (F a X 3 : EReal) := by
  sorry

end Erdos873
