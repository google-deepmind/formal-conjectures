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

import FormalConjectures.Util.ProblemImports

/-!
# Ramsey numbers

This file records benchmark statements about (graph) Ramsey numbers. In particular, the exact
value of $R(5,5)$ is currently unknown, but it is known to satisfy $43 \le R(5,5) \le 46$.

Note: the diagonal Ramsey number $R(n,n)$ can also be formulated in terms of 2-colorings of
$2$-subsets, as `Combinatorics.hypergraphRamsey 2 n` (see `FormalConjecturesForMathlib/Combinatorics/Ramsey.lean`).

*References:*
- [Wikipedia: Ramsey number](https://en.wikipedia.org/wiki/Ramsey_number)
- [Rad] S. P. Radziszowski, *Small Ramsey Numbers*, Electronic Journal of Combinatorics, Dynamic
  Survey DS1. (Updated periodically.) https://www.combinatorics.org/ojs/index.php/eljc/article/view/DS1
- [Exoo89] G. Exoo, *A lower bound for* $R(5,5)$, Journal of Graph Theory 13 (1989), 97–98.
  DOI: 10.1002/jgt.3190130113
- [AM24] V. Angeltveit and B. McKay, *$R(5,5) \le 46$*, arXiv:2409.15709 (2024).
- [OEIS A212954](https://oeis.org/A212954)
- [MathWorld: Ramsey Number](https://mathworld.wolfram.com/RamseyNumber.html)
-/

namespace RamseyNumbers

/--
`IsGraphRamsey n k l` means that for every simple graph `G` on `n` vertices, either
- `G` contains a clique of size `k`, or
- the complement graph `Gᶜ` contains a clique of size `l` (equivalently, `G` contains an
  independent set of size `l`).
-/
def IsGraphRamsey (n k l : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ (G.CliqueFree k ∧ (Gᶜ).CliqueFree l)

/--
The (graph) Ramsey number `R(k,l)` is the least natural number `n` such that `IsGraphRamsey n k l`
holds.
-/
noncomputable def graphRamseyNumber (k l : ℕ) : ℕ :=
  sInf {n : ℕ | IsGraphRamsey n k l}

/--
The open problem: determine the Ramsey number $R(5,5)$.

It is known that $43 \le R(5,5) \le 46$.
-/
@[category research open, AMS 05]
theorem ramsey_number_five_five :
    IsLeast {n : ℕ | IsGraphRamsey n 5 5} answer(sorry) := by
  sorry

/--
Lower bound $43 \le R(5,5)$, equivalently: there exists a graph on $42$ vertices with no
$5$-clique and no independent set of size $5$.
-/
@[category research solved, AMS 05]
theorem ramsey_number_five_five_lower_bound :
    ∃ G : SimpleGraph (Fin 42), G.CliqueFree 5 ∧ (Gᶜ).CliqueFree 5 := by
  sorry

/--
Upper bound $R(5,5) \le 46$, i.e. every graph on $46$ vertices contains a $5$-clique or an
independent set of size $5$.
-/
@[category research solved, AMS 05]
theorem ramsey_number_five_five_upper_bound :
    IsGraphRamsey 46 5 5 := by
  sorry

end RamseyNumbers
