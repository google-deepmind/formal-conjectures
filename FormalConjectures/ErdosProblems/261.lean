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
# Erdős Problem 261

*References:*
 - [erdosproblems.com/261](https://www.erdosproblems.com/261)
 - [BoLo90] Borwein, Peter and Loring, Terry A., Some questions of Erdős and Graham on numbers
    of the form $\sum g_n/2^{g_n}$. Math. Comp. (1990), 377--394.
 - [Er88c] Erdős, P., On the irrationality of certain series: problems and results. New advances
    in transcendence theory (Durham, 1986) (1988), 102--109.
 - [TUZ20] Tengely, Szabolcs and Ulas, Maciej and Zygadlo, Jakub, On a Diophantine equation of
    Erdős and Graham. J. Number Theory (2020), 445--459.
-/

open scoped Cardinal

namespace Erdos261

/-- A natural number $n$ is said to have property `Erdos261Prop` if there exist $t \ge 2$
pairwise distinct positive integers $a_1, \ldots, a_t$ such that
$n / 2^n = \sum_{1 \le k \le t} a_k / 2^{a_k}$. -/
def Erdos261Prop (n : ℕ) : Prop := ∃ᵉ (t ≥ 2) (a : Fin t → ℕ), a.Injective ∧
  (1 ≤ a) ∧ n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)

/-- A canonical infinite representation of a rational number $x$ by positive integers. The
denominators are strictly increasing so that reorderings are not counted as different
representations. -/
def Erdos261InfiniteRepresentation (x : ℚ) (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ (1 ≤ a) ∧ Summable (fun k => (a k) / (2 ^ (a k) : ℚ)) ∧
    x = ∑' k, (a k) / (2 ^ (a k) : ℚ)

/-- For every positive integer $m$, if $n = 2^{m+1} - m - 2$, then
$$\frac{n}{2^n} = \sum_{n < k \le n + m} \frac{k}{2^k}.$$

This construction is due to Borwein and Loring [BoLo90]. -/
@[category textbook, AMS 11]
theorem erdos_261.variants.borwein_loring (m : ℕ) (hm : 0 < m) :
    let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ) := by
  sorry

/-- The Borwein--Loring construction gives the required property when $m \ge 2$. This lower
bound ensures that the representation contains at least two terms. -/
@[category textbook, AMS 11]
theorem erdos_261.variants.borwein_loring_property (m : ℕ) (hm : 2 ≤ m) :
    Erdos261Prop (2 ^ (m + 1) - m - 2) := by
  sorry

/-- Are there infinitely many positive integers $n$ such that there exist some $t \ge 2$ and
distinct integers $a_1, \ldots, a_t \ge 1$ satisfying
$$\frac{n}{2^n} = \sum_{1 \le k \le t} \frac{a_k}{2^{a_k}}?$$

In [Er88c], Erdős notes that Cusick had a simple proof that infinitely many such $n$ exist. -/
@[category research solved, AMS 11]
theorem erdos_261.parts.i : answer(True) ↔ {n : ℕ | 0 < n ∧ Erdos261Prop n}.Infinite := by
  sorry

/-- Tengely, Ulas, and Zygadlo [TUZ20] verified that every positive integer $n \le 10000$ has
the required property. -/
@[category research solved, AMS 11]
theorem erdos_261.variants.le_10000 {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000) :
    Erdos261Prop n := by
  sorry

/-- Do all positive integers $n$ have the required property? -/
@[category research open, AMS 11]
theorem erdos_261.parts.ii : answer(sorry) ↔ ∀ n > 0, Erdos261Prop n := by
  sorry

/-- Is there a rational number $x$ such that
$$x = \sum_{k=1}^{\infty} \frac{a_k}{2^{a_k}}$$
has at least $2^{\aleph_0}$ representations by pairwise distinct positive integers $a_k$? -/
@[category research open, AMS 11]
theorem erdos_261.parts.iii : answer(sorry) ↔ ∃ x : ℚ,
    𝔠 ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a} := by
  sorry

/-- In [Er88c], Erdős asks the weaker question of whether there exists a rational $x$ with at
least two representations
$$x = \sum_{k=1}^{\infty} \frac{a_k}{2^{a_k}}$$
by pairwise distinct positive integers $a_k$. -/
@[category research open, AMS 11]
theorem erdos_261.variants.two_representations : answer(sorry) ↔ ∃ x : ℚ,
    2 ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a} := by
  sorry

end Erdos261
