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
# Erdős Problem 960

*References:*
- [erdosproblems.com/960](https://www.erdosproblems.com/960)
- [Er84] Erdős, P., _Research problems_. Period. Math. Hungar. (1984), 101-103.
- [APSSV26b] B. Alexeev, M. Putterman, M. Sawhney, M. Sellke, and G. Valiant, _Short proofs in
  combinatorics, probability, and number theory II_. arXiv:2604.06609 (2026).
-/

@[expose] public section

open Filter Asymptotics EuclideanGeometry

namespace Erdos960

open scoped Classical in
/-- The number of *ordinary lines* determined by `A` (lines containing exactly two points of
`A`), counted through the pairs of points of `A` spanning them. -/
noncomputable def ordinaryLines (A : Finset ℝ²) : ℕ :=
  ((A.powersetCard 2).filter fun B : Finset ℝ² ↦
    ∀ x ∈ A, x ∈ affineSpan ℝ (B : Set ℝ²) → x ∈ B).card

/-- No `k` points of `A` lie on a line. -/
def NoKCollinear (A : Finset ℝ²) (k : ℕ) : Prop :=
  ∀ B ⊆ A, B.card = k → ¬ Collinear ℝ (B : Set ℝ²)

/-- `A` contains a set `A'` of `r` points such that all $\binom{r}{2}$ lines determined by `A'`
are ordinary (with respect to `A`). -/
def HasOrdinaryClique (A : Finset ℝ²) (r : ℕ) : Prop :=
  ∃ B ⊆ A, B.card = r ∧ ∀ p ∈ B, ∀ q ∈ B, p ≠ q →
    ∀ x ∈ A, x ∈ line[ℝ, p, q] → x = p ∨ x = q

/-- The threshold $f_{r,k}(n)$: the least `t` such that every set of `n` points with no `k` on a
line and at least `t` ordinary lines contains `r` points all of whose joining lines are
ordinary. -/
noncomputable def f (r k n : ℕ) : ℕ :=
  sInf {t | ∀ A : Finset ℝ², A.card = n → NoKCollinear A k → t ≤ ordinaryLines A →
    HasOrdinaryClique A r}

/--
Let $r,k\geq 2$ be fixed. Let $A\subset \mathbb{R}^2$ be a set of $n$ points with no $k$ points
on a line. Determine the threshold $f_{r,k}(n)$ such that if there are at least $f_{r,k}(n)$
many ordinary lines (lines containing exactly two points) then there is a set $A'\subseteq A$ of
$r$ points such that all $\binom{r}{2}$ many lines determined by $A'$ are ordinary.

Is it true that $f_{r,k}(n)=o(n^2)$?

The answer is no: an internal OpenAI model (see [APSSV26b]) has shown that in fact for any
$r\geq 3$ and $k\geq 4$, $f_{r,k}(n) \geq \frac{n^2}{12}-O(n)$.
-/
@[category research solved, AMS 52, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos960.lean#L1533"]
theorem erdos_960.parts.i : answer(False) ↔
    ∀ r ≥ 2, ∀ k ≥ 2,
      (fun n : ℕ ↦ (f r k n : ℝ)) =o[atTop] fun n : ℕ ↦ (n : ℝ) ^ 2 := by
  sorry

/--
Is it true that $f_{r,k}(n) \ll n$?

The answer is no, since $f_{r,k}(n) \geq \frac{n^2}{12}-O(n)$ for $r\geq 3$, $k\geq 4$
[APSSV26b].
-/
@[category research solved, AMS 52, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos960.lean#L1533"]
theorem erdos_960.parts.ii : answer(False) ↔
    ∀ r ≥ 2, ∀ k ≥ 2,
      (fun n : ℕ ↦ (f r k n : ℝ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) := by
  sorry

/-- Turán's theorem implies $f_{r,k}(n) \leq \left(1-\frac{1}{r-1}\right)\frac{n^2}{2}+1$, and
an internal OpenAI model [APSSV26b] showed that $f_{r,k}(n) \geq \frac{n^2}{12}-O(n)$ for
$r\geq 3$ and $k\geq 4$. -/
@[category research solved, AMS 52, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos960.lean#L1533"]
theorem erdos_960.variants.bounds (r k : ℕ) (hr : 3 ≤ r) (hk : 4 ≤ k) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 / 12 - C * n ≤ f r k n ∧
      (f r k n : ℝ) ≤ (1 - 1 / (r - 1 : ℝ)) * (n : ℝ) ^ 2 / 2 + 1 := by
  sorry

end Erdos960
