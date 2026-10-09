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
# Erdős Problem 724

*References:*
- [erdosproblems.com/724](https://www.erdosproblems.com/724)
- [OEIS A001438](https://oeis.org/A001438)
- [Be83c] Beth, Thomas, *Eine Bemerkung zur Abschätzung der Anzahl orthogonaler lateinischer
  Quadrate mittels Siebverfahren*. Abh. Math. Sem. Univ. Hamburg (1983), 284-288.
- [BPS60] Bose, R. C. and Shrikhande, S. S. and Parker, E. T., *Further results on the
  construction of mutually orthogonal Latin squares and the falsity of Euler's conjecture*.
  Canadian J. Math. (1960), 189-203.
- [CES60] Chowla, S. and Erdős, P. and Straus, E. G., *On the maximal number of pairwise
  orthogonal Latin squares of a given order*. Canadian J. Math. (1960), 204-208.
- [Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*.
  Combinatorica (1981), 25-42.
- [Wi74] Wilson, Richard M., *Concerning the number of mutually orthogonal Latin squares*.
  Discrete Math. (1974), 181-198.
-/

@[expose] public section

open Filter Finset

namespace Erdos724

/--
Two Latin squares $L, M$ of order $n$ are orthogonal if superimposing them gives each ordered
pair of symbols at most once, i.e. the map $(i, j) \mapsto (L_{ij}, M_{ij})$ is injective
(hence bijective).
-/
def IsOrthogonal {n : ℕ} (L M : LatinSquare n) : Prop :=
  Function.Injective fun p : Fin n × Fin n => (L.mat p.1 p.2, M.mat p.1 p.2)

/--
`maxMOLS n` is $f(n)$, the maximum number of mutually orthogonal Latin squares of order $n$:
the largest size of a set of Latin squares of order $n$ that are pairwise orthogonal. For
$n \leq 1$ this gives $f(n) = 1$, while OEIS A001438 uses $\infty$.
-/
noncomputable def maxMOLS (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset (LatinSquare n), #S = k ∧
    (S : Set (LatinSquare n)).Pairwise IsOrthogonal}

/--
Let $f(n)$ be the maximum number of mutually orthogonal Latin squares of order $n$. Is it true
that
$$f(n) \gg n^{1/2}?$$
This question is from [Er81].
-/
@[category research open, AMS 5]
theorem erdos_724 : answer(sorry) ↔
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, c * Real.sqrt (n : ℝ) ≤ (maxMOLS n : ℝ) := by
  sorry

/--
Euler conjectured that $f(n) = 1$ when $n \equiv 2 \pmod{4}$. This is false: Bose, Parker, and
Shrikhande [BPS60] proved $f(n) \geq 2$ for $n \geq 7$, so for example $f(10) \geq 2$.
-/
@[category research solved, AMS 5]
theorem erdos_724.variants.euler_conjecture : answer(False) ↔
    ∀ n : ℕ, n ≡ 2 [MOD 4] → maxMOLS n = 1 := by
  sorry

/--
Bose, Parker, and Shrikhande [BPS60] proved that $f(n) \geq 2$ for all $n \geq 7$.
-/
@[category research solved, AMS 5]
theorem erdos_724.variants.bose_parker_shrikhande :
    ∀ n : ℕ, 7 ≤ n → 2 ≤ maxMOLS n := by
  sorry

/--
Chowla, Erdős, and Straus [CES60] proved that
$$f(n) \gg n^{1/91}.$$
-/
@[category research solved, AMS 5]
theorem erdos_724.variants.chowla_erdos_straus :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((1 : ℝ) / 91) ≤ (maxMOLS n : ℝ) := by
  sorry

/--
Wilson [Wi74] proved that
$$f(n) \gg n^{1/17}.$$
-/
@[category research solved, AMS 5]
theorem erdos_724.variants.wilson :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((1 : ℝ) / 17) ≤ (maxMOLS n : ℝ) := by
  sorry

/--
Beth [Be83c] proved that
$$f(n) \gg n^{1/14.8}.$$
-/
@[category research solved, AMS 5]
theorem erdos_724.variants.beth :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((1 : ℝ) / 14.8) ≤ (maxMOLS n : ℝ) := by
  sorry

/--
For $n \geq 2$ there are at most $n - 1$ mutually orthogonal Latin squares of order $n$:
$$f(n) \leq n - 1.$$
This is classical; see OEIS A001438.
-/
@[category textbook, AMS 5]
theorem erdos_724.variants.le_sub_one :
    ∀ n : ℕ, 2 ≤ n → maxMOLS n ≤ n - 1 := by
  sorry

end Erdos724
