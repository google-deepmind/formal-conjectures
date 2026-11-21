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
# Erdős Problem 954

*References:*
- [erdosproblems.com/954](https://www.erdosproblems.com/954)
- [Er77c] Erdős, P., *Problems and results on combinatorial number theory. III*. Number theory
  day (Proc. Conf., Rockefeller Univ., New York, 1976), Lecture Notes in Math. 626, Springer
  (1977), 43-72. [PDF](https://www.renyi.hu/~p_erdos/1977-27.pdf)
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos954

/-- `pairCount a m n` is the number of pairs `(i, j)` with `0 ≤ i ≤ j ≤ m`, `1 ≤ j` and
`a i + a j ≤ n`. -/
def pairCount (a : ℕ → ℕ) (m n : ℕ) : ℕ :=
  ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter
    fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ 1 ≤ p.2 ∧ a p.1 + a p.2 ≤ n).card

/-- Stage `k` of the construction of Rosen's sequence: `rosenAux k i = a_i` for `i ≤ k + 1`.

Stage `0` holds `a_0 = 0` and `a_1 = 1` (the value `1` at the unused indices `i ≥ 2` is a
placeholder). Stage `k + 1` appends `a_{k+2}`, the least `n` such that the number of pairs
`(i, j)` with `0 ≤ i ≤ j ≤ k + 1`, `1 ≤ j` and `a_i + a_j ≤ n` is less than `n`. This count is
below `(k + 2) ^ 2`, so the set is nonempty and `sInf` is a genuine minimum. -/
noncomputable def rosenAux : ℕ → ℕ → ℕ
  | 0 => fun i => if i = 0 then 0 else 1
  | k + 1 => fun i =>
      if i = k + 2 then sInf {n : ℕ | pairCount (rosenAux k) (k + 1) n < n} else rosenAux k i

/-- Rosen's sequence $a_0=0$, $a_1=1$, $a_{k+1}=\min\{n : \#\{(i,j) : 0\le i\le j\le k,\ j\ge 1,
a_i+a_j\le n\} < n\}$. It begins $0,1,3,5,9,13,17,24,31,38,45,\ldots$ -/
noncomputable def rosen (k : ℕ) : ℕ := rosenAux k k

/-- The number of solutions of $a_i+a_j\le x$ with $0\le i\le j$ and $j\ge 1$, over the whole
sequence `rosen`. The sequence is strictly increasing with `rosen 0 = 0`, so `rosen j ≥ j`.
Hence a pair with `rosen i + rosen j ≤ x` has `j ≤ x`, and counting the pairs with `j ≤ x`
counts all solutions. -/
noncomputable def solutionCount (x : ℕ) : ℕ := pairCount rosen x x

@[category test, AMS 11]
theorem rosen_zero : rosen 0 = 0 := by
  decide

@[category test, AMS 11]
theorem rosen_one : rosen 1 = 1 := by
  decide

@[category test, AMS 11]
theorem rosen_two : rosen 2 = 3 := by
  show sInf {n : ℕ | pairCount (rosenAux 0) 1 n < n} = 3
  exact IsLeast.csInf_eq (by decide)

/--
Let $0=a_0<a_1<a_2<\cdots$ be the sequence of integers defined by $a_0=0$ and $a_1=1$, and
$a_{k+1}$ is the smallest integer $n$ for which the number of solutions to $a_i+a_j \leq n$
(with $0\leq i\leq j\leq k$ and $j\geq 1$) is $<n$.

Is the number of solutions to $a_i+a_j \leq x$ equal to $x+O(x^{1/4+o(1)})$?

The sequence was constructed by Rosen [Er77c, p. 71]. We read $O(x^{1/4+o(1)})$ as
$O(x^{1/4+\varepsilon})$ for every $\varepsilon>0$, and use the version with $a_0=0$.
-/
@[category research open, question, AMS 11]
theorem erdos_954 :
    ∀ ε > (0 : ℝ), (fun x : ℕ ↦ (solutionCount x : ℝ) - x) =O[atTop]
      (fun x : ℕ ↦ (x : ℝ) ^ ((1 : ℝ) / 4 + ε)) := by
  sorry

/--
Erdős and Rosen could not even prove that the number of solutions to $a_i+a_j\leq x$ is at most
$(1+o(1))x$ [Er77c, p. 71].
-/
@[category research open, AMS 11]
theorem erdos_954.variants.upper :
    ∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in atTop, (solutionCount x : ℝ) ≤ (1 + ε) * x := by
  sorry

/--
The number of solutions to $a_i+a_j\leq x$ is always at least $x$ by construction
[Er77c, p. 71].
-/
@[category textbook, AMS 11]
theorem erdos_954.variants.lower : ∀ x : ℕ, x ≤ solutionCount x := by
  sorry

end Erdos954
