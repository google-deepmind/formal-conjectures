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
# Erdős Problem 782

*References:*
- [erdosproblems.com/782](https://www.erdosproblems.com/782)
- [BEF90] Brown, T. C. and Erdős, P. and Freedman, A. R., _Quasi-progressions and descending
  waves_. J. Combin. Theory Ser. A 53 (1990), 81-95.
- [BFS03] Brown, T. C., Freedman, A. R. and Shiue, P. J.-S., _Progressions of squares_.
  Australas. J. Combin. 27 (2003), 187-192.
- [BEU26] Bremner, A., Elsholtz, C. and Ulas, M., _There are infinitely many Hilbert cubes of
  dimension 3 in the set of squares_. [arXiv:2604.05459](https://arxiv.org/abs/2604.05459) (2026).
- [CiGr07] Cilleruelo, J. and Granville, A., _Lattice points on circles, squares in arithmetic
  progressions and sumsets of squares_. Additive combinatorics (2007), 241-262.
- [DiEl12] Dietmann, R. and Elsholtz, C., _Hilbert cubes in progression-free sets and in the set
  of squares II_. [arXiv:1207.1461](https://arxiv.org/abs/1207.1461) (2012).
- [So07] Solymosi, J., _Elementary additive combinatorics_. Additive combinatorics (2007), 29-38.
-/

@[expose] public section

namespace Erdos782

/-- `ContainsQuasiProgression S C k` says that `S` contains a $k$-term quasi-progression of
diameter $C$: terms $x_1,\ldots,x_k\in S$ and a difference $d\geq 1$ with
$x_i+d\leq x_{i+1}\leq x_i+d+C$ for all $1\leq i<k$ (indexed from $0$ in Lean). The condition
$d\geq 1$ makes the terms strictly increasing, as in [BFS03]. -/
def ContainsQuasiProgression (S : Set ℕ) (C k : ℕ) : Prop :=
  ∃ (x : ℕ → ℕ) (d : ℕ), 0 < d ∧ (∀ i < k, x i ∈ S) ∧
    ∀ i, i + 1 < k → x i + d ≤ x (i + 1) ∧ x (i + 1) ≤ x i + d + C

/-- The Hilbert cube with presentation $(a_0; b_1,\ldots,b_d)$, that is,
$$a_0+\left\{ \sum_i \epsilon_ib_i : \epsilon_i\in \{0,1\}\right\}.$$
The index set of the sum is the set of $i$ with $\epsilon_i=1$. -/
def hilbertCube {d : ℕ} (a₀ : ℤ) (b : Fin d → ℤ) : Set ℤ :=
  {x | ∃ ε : Finset (Fin d), x = a₀ + ∑ i ∈ ε, b i}

/-- The base point $a_0$ lies in its Hilbert cube: take all $\epsilon_i=0$. -/
@[category API, AMS 11]
theorem mem_hilbertCube_self {d : ℕ} (a₀ : ℤ) (b : Fin d → ℤ) :
    a₀ ∈ hilbertCube a₀ b :=
  ⟨∅, by simp⟩

/-- The squares $1, 25, 49$ form a $3$-term arithmetic progression, hence the squares contain a
$3$-term quasi-progression of diameter $0$. -/
@[category test, AMS 11]
theorem containsQuasiProgression_squares_three :
    ContainsQuasiProgression {n : ℕ | IsSquare n} 0 3 := by
  refine ⟨fun i ↦ 1 + 24 * i, 24, by norm_num, ?_, ?_⟩
  · intro i hi
    interval_cases i
    · exact ⟨1, by norm_num⟩
    · exact ⟨5, by norm_num⟩
    · exact ⟨7, by norm_num⟩
  · intro i _
    show 1 + 24 * i + 24 ≤ 1 + 24 * (i + 1) ∧ 1 + 24 * (i + 1) ≤ 1 + 24 * i + 24 + 0
    omega

/--
Do the squares contain arbitrarily long quasi-progressions? That is, does there exist some
constant $C>0$ such that, for any $k$, the squares contain a sequence $x_1,\ldots,x_k$ where, for
some $d$ and all $1\leq i<k$,
$$x_i+d\leq x_{i+1}\leq x_i+d+C.$$

A question of Brown, Erdős, and Freedman [BEF90]. This is the first question. Here $C$ and $d$ are
positive integers; $d\geq 1$ excludes constant sequences.
-/
@[category research open, question, AMS 11]
theorem erdos_782.parts.i :
    ∃ C : ℕ, 0 < C ∧ ∀ k : ℕ, ContainsQuasiProgression {n : ℕ | IsSquare n} C k := by
  sorry

/--
Do the squares contain arbitrarily large cubes
$$a+\left\{ \sum_i \epsilon_ib_i : \epsilon_i\in \{0,1\}\right\}?$$

A question of Brown, Erdős, and Freedman [BEF90]. This is the second question. The generators
$b_i$ are nonzero integers, as in [BEU26]. Solymosi [So07] conjectured that the answer is no, and
Cilleruelo and Granville [CiGr07] observed that the answer is no conditional on the
Bombieri-Lang conjecture.
-/
@[category research open, question, AMS 11]
theorem erdos_782.parts.ii :
    ∀ d : ℕ, ∃ (a : ℤ) (b : Fin d → ℤ),
      (∀ i, b i ≠ 0) ∧ hilbertCube a b ⊆ {n : ℤ | IsSquare n} := by
  sorry

/-- It is a classical fact that the squares do not contain arithmetic progressions of length
$4$. -/
@[category research solved, AMS 11]
theorem erdos_782.variants.no_four_term_ap :
    Set.IsAPOfLengthFree {n : ℕ | IsSquare n} 4 := by
  sorry

/--
Dietmann and Elsholtz [DiEl12, Theorem 1] proved that, for all sufficiently large $N$, if
$a_0\geq 0$ and $b_1,\ldots,b_d$ are distinct positive integers such that the Hilbert cube
$a_0+\{0,b_1\}+\cdots+\{0,b_d\}$ consists of squares in $[1,N]$, then $d\leq 7\log\log N$.
-/
@[category research solved, AMS 11]
theorem erdos_782.variants.dietmann_elsholtz :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (d : ℕ) (a₀ : ℤ) (b : Fin d → ℤ),
      0 ≤ a₀ → Function.Injective b → (∀ i, 0 < b i) →
      hilbertCube a₀ b ⊆ {n : ℤ | IsSquare n ∧ 1 ≤ n ∧ n ≤ N} →
        (d : ℝ) ≤ 7 * Real.log (Real.log N) := by
  sorry

end Erdos782
