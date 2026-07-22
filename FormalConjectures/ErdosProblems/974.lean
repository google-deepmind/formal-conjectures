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
# Erdős Problem 974

*References:*
- [erdosproblems.com/974](https://www.erdosproblems.com/974)
- [Ti66] Tijdeman, R., *On a conjecture of Turán and Erdős*. Indag. Math. (1966), 374-383.
-/

namespace Erdos974

/--
The configuration described by Tijdeman: if `n` is odd then the `z i` are exactly the `n`th roots
of unity, and if `n` is even then they are the vertices of two regular `(n / 2)`-gons with the
same circumscribed circle centred at the origin, that is, the `(n / 2)`th roots of `1` together
with the `(n / 2)`th roots of some other point `c` on the unit circle.
-/
def IsTuranConfiguration {n : ℕ} (z : Fin n → ℂ) : Prop :=
  (Odd n → Set.range z = {ζ : ℂ | ζ ^ n = 1}) ∧
    (Even n → ∃ c : ℂ, ‖c‖ = 1 ∧ c ≠ 1 ∧
      Set.range z = {ζ : ℂ | ζ ^ (n / 2) = 1} ∪ {ζ : ℂ | ζ ^ (n / 2) = c})

/--
Let $z_1,\ldots,z_n\in \mathbb{C}$ be a sequence such that $z_1=1$. Suppose that the sequence of
\[s_k=\sum_{1\leq i\leq n}z_i^k\]
contains infinitely many $(n-1)$-tuples of consecutive values of $s_k$ which are all $0$. Then
(essentially)
\[z_j=e(j/n),\]
where $e(x)=e^{2\pi ix}$.

A conjecture of Turán.

This is true (in the stronger form with only two such tuples) - in fact if $n$ is odd then the
$z_i$ must be exactly the $n$th roots of unity, and if $n$ is even they must be the vertices of
two regular $(n/2)$-gons with the same circumscribed circle centred at the origin. This was first
proved by Tijdeman [Ti66]. An independent proof of this was given in the comments section by Hu,
Tang, and Zhang.
-/
@[category research solved, AMS 11 30]
theorem erdos_974 {n : ℕ} [NeZero n] (z : Fin n → ℂ) (hz : z 0 = 1)
    (hs : Set.Infinite {k : ℕ | ∀ j < n - 1, ∑ i, z i ^ (k + j) = 0}) :
    IsTuranConfiguration z := by
  sorry

/--
Erdős speculates that this may be true if there are two distinct $(n-1)$-tuples of consecutive
values of $s_k$ which are $0$. He does not elaborate on what the 'essentially' may mean precisely.

This is true (in the stronger form with only two such tuples) - in fact if $n$ is odd then the
$z_i$ must be exactly the $n$th roots of unity, and if $n$ is even they must be the vertices of
two regular $(n/2)$-gons with the same circumscribed circle centred at the origin. This was first
proved by Tijdeman [Ti66]. An independent proof of this was given in the comments section by Hu,
Tang, and Zhang.
-/
@[category research solved, AMS 11 30]
theorem erdos_974.variants.two_tuples {n : ℕ} [NeZero n] (z : Fin n → ℂ) (hz : z 0 = 1)
    {a b : ℕ} (hab : a ≠ b) (ha : ∀ j < n - 1, ∑ i, z i ^ (a + j) = 0)
    (hb : ∀ j < n - 1, ∑ i, z i ^ (b + j) = 0) :
    IsTuranConfiguration z := by
  sorry

end Erdos974
