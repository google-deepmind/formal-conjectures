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
# Erdős Problem 556

A problem of Bondy and Erdős: for the cycle $C_n$, the $3$-colour Ramsey number satisfies
$$R(C_n; 3) \le 4n - 3.$$
The bound is best possible for odd $n$, where equality is conjectured (and known for large odd
$n$). Łuczak proved the asymptotic bound $R(C_n; 3) \le (4 + o(1))n$; Kohayakawa, Simonovits and
Skokan settled large odd $n$, and Benevides and Skokan large even $n$, but the inequality for all
$n$ remains open.

*References:*
- [erdosproblems.com/556](https://www.erdosproblems.com/556)
- [Er81] P. Erdős, *On the combinatorial problems which I would most like to see solved*,
  Combinatorica 1 (1981), 25-42.
- [Lu99] T. Łuczak, *$R(C_n, C_n, C_n) \le (4 + o(1))n$*, J. Combin. Theory Ser. B 75 (1999),
  174-187.
- [KSS05] Y. Kohayakawa, M. Simonovits, J. Skokan, *The 3-colored Ramsey number of odd cycles*,
  Proceedings of GRACO2005 (2005), 397-402.
- [BeSk09] F. S. Benevides, J. Skokan, *The 3-colored Ramsey number of even cycles*, J. Combin.
  Theory Ser. B 99 (2009), 690-708.
-/

open Filter

namespace Erdos556

open SimpleGraph

/--
The $k$-colour Ramsey number of a graph `G`: the least `N` such that every `k`-colouring of the
edges of the complete graph on `Fin N` (an edge-colouring `c : Fin k → SimpleGraph (Fin N)` of
`⊤`) contains a monochromatic copy of `G`, i.e. `G ⊑ c i` for some colour `i`.
-/
noncomputable def multicolourRamsey {V : Type*} (G : SimpleGraph V) (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ c : Fin k → SimpleGraph (Fin N),
    (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c → ∃ i, G ⊑ c i}

/--
Erdős Problem 556 (Bondy–Erdős): for all $n \ge 3$,
$$R(C_n; 3) \le 4n - 3.$$
-/
@[category research open, AMS 5]
theorem erdos_556 (n : ℕ) (hn : 3 ≤ n) :
    multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3 := by
  sorry

/--
Łuczak's asymptotic bound [Lu99]: for every $\varepsilon > 0$, for all sufficiently large $n$,
$$R(C_n; 3) \le (4 + \varepsilon)n.$$
-/
@[category research solved, AMS 5]
theorem erdos_556.variants.luczak_asymptotic :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (multicolourRamsey (cycleGraph n) 3 : ℝ) ≤ (4 + ε) * n := by
  sorry

/--
For odd $n$ the bound $4n - 3$ is best possible: the $3$-colour Ramsey number is at least
$4n - 3$, so equality holds whenever the conjectured upper bound does.
-/
@[category research solved, AMS 5]
theorem erdos_556.variants.odd_lower_bound (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3 := by
  sorry

end Erdos556
