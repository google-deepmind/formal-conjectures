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
# Erdős Problem 960

*References:*
- [erdosproblems.com/960](https://www.erdosproblems.com/960)
- [APSSV26b] B. Alexeev, M. Putterman, M. Sawhney, M. Sellke, and G. Valiant, *Short proofs in
  combinatorics, probability, and number theory II*. arXiv:2604.06609 (2026).
-/

open EuclideanGeometry Filter Asymptotics

namespace Erdos960

/--
The set of lines determined by pairs of points of `S`.
-/
noncomputable def determinedLines (S : Set ℝ²) : Set (AffineSubspace ℝ ℝ²) :=
  { affineSpan ℝ {p, q} | (p ∈ S) (q ∈ S) (_ : p ≠ q) }

/--
Ordinary lines of `S`: lines containing exactly two points of `S`.
-/
noncomputable def ordinaryLines (S : Set ℝ²) : Set (AffineSubspace ℝ ℝ²) :=
  { L ∈ determinedLines S | ((L : Set ℝ²) ∩ S).ncard = 2 }

/--
`A` contains `r` points such that every line they determine is an ordinary line of `A`.
-/
def HasOrdinaryRSet (r : ℕ) (A : Finset ℝ²) : Prop :=
  ∃ A' ⊆ A, A'.card = r ∧
    ∀ p ∈ A', ∀ q ∈ A', p ≠ q → affineSpan ℝ {p, q} ∈ ordinaryLines (A : Set ℝ²)

/--
The threshold $f_{r,k}(n)$: the least $m$ such that every set of $n$ points in $\mathbb{R}^2$
with no $k$ on a line and at least $m$ ordinary lines contains an ordinary $r$-set.
-/
noncomputable def f (r k n : ℕ) : ℕ :=
  sInf { m : ℕ | ∀ A : Finset ℝ², A.card = n →
    NonCollinearFor k (A : Set ℝ²) →
    m ≤ (ordinaryLines (A : Set ℝ²)).ncard →
    HasOrdinaryRSet r A }

/--
Let $r,k\geq 2$ be fixed. Let $A\subset \mathbb{R}^2$ be a set of $n$ points with no $k$ points on a line. Determine the threshold $f_{r,k}(n)$ such that if there are at least $f_{r,k}(n)$ many ordinary lines (lines containing exactly two points) then there is a set $A'\subseteq A$ of $r$ points such that all $\binom{r}{2}$ many lines determined by $A'$ are ordinary.

Is it true that $f_{r,k}(n)=o(n^2)$, or perhaps even $\ll n$?
-/
@[category research open, AMS 52]
theorem erdos_960 (r k : ℕ) (hr : 2 ≤ r) (hk : 2 ≤ k) :
    ∀ n, f r k n = answer(sorry) := by
  sorry

/--
Is it true that $f_{r,k}(n)=o(n^2)$?
-/
@[category research open, AMS 52]
theorem erdos_960.variants.littleO :
    answer(sorry) ↔ ∀ r ≥ 2, ∀ k ≥ 2,
      (fun n : ℕ ↦ (f r k n : ℝ)) =o[atTop] fun n ↦ (n : ℝ) ^ 2 := by
  sorry

/--
Is it true that $f_{r,k}(n)\ll n$?
-/
@[category research open, AMS 52]
theorem erdos_960.variants.linear :
    answer(sorry) ↔ ∀ r ≥ 2, ∀ k ≥ 2,
      (fun n : ℕ ↦ (f r k n : ℝ)) =O[atTop] fun n ↦ (n : ℝ) := by
  sorry

/--
Turán's theorem implies
$$
f_{r,k}(n) \leq \left(1-\frac{1}{r-1}\right)\frac{n^2}{2}+1.
$$
-/
@[category research solved, AMS 52]
theorem erdos_960.variants.turan (r k n : ℕ) (hr : 2 ≤ r) (hk : 2 ≤ k) :
    (f r k n : ℝ) ≤ (1 - 1 / (r - 1 : ℝ)) * (n : ℝ) ^ 2 / 2 + 1 := by
  sorry

/--
An internal OpenAI model (see [APSSV26b]) has shown that in fact for any $r\geq 3$ and $k\geq 4$
$$
f_{r,k}(n) \geq \frac{n^2}{12}-O(n).
$$
-/
@[category research solved, AMS 52]
theorem erdos_960.variants.APSSV26b (r k : ℕ) (hr : 3 ≤ r) (hk : 4 ≤ k) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 / 12 - C * n ≤ (f r k n : ℝ) := by
  sorry

end Erdos960
