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
# Erdős Problem 165

Related problems: [544](https://www.erdosproblems.com/544),
[986](https://www.erdosproblems.com/986), [1013](https://www.erdosproblems.com/1013).
OEIS: [A000791](https://oeis.org/A000791).

*References:*
- [erdosproblems.com/165](https://www.erdosproblems.com/165)
- [AKS80] Ajtai, M., Komlós, J. and Szemerédi, E., _A note on Ramsey numbers_.
  J. Combin. Theory Ser. A **29** (1980), 354–360.
- [Sh83] Shearer, J. B., _A note on the independence number of triangle-free
  graphs_. Discrete Math. **46** (1983), 83–87.
- [Ki95] Kim, J. H., _The Ramsey number R(3,t) has order of magnitude t²/log t_.
  Random Structures and Algorithms (1995), 173–207.
- [PGM20] Fiz Pontiveros, G., Griffiths, S. and Morris, R., _The triangle-free
  process and the Ramsey number R(3,k)_. Mem. Amer. Math. Soc. (2020).
- [BoKe21] Bohman, T. and Keevash, P., _Dynamic concentration of the
  triangle-free process_. Random Structures Algorithms (2021), 221–293.
- [CJMS25] Campos, M., Jenssen, M., Michelen, M. and Sahasrabudhe, J.,
  _A new lower bound for the Ramsey numbers R(3,k)_. arXiv:2505.13371 (2025).
- [HHKP25] Hefty, L., Horn, P., King, R. and Pfender, F., _Improving R(3,k) in
  just two bites_. arXiv:2510.19718 (2025).
- [Er61] Erdős, P., _Some unsolved problems_.
  Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961), 221–254.
- [Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial analysis_.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97–109.
- [Er78] Erdős, P., _Problems and results in combinatorial analysis and combinatorial number
  theory_. Proc. Ninth SE Conf. on Combinatorics, Graph Theory, and Computing (1978), 29–40.
- [Er90b] Erdős, P., _Problems and results on graphs and hypergraphs: similarities and
  differences_. Mathematics of Ramsey theory (1990), 12–28.
- [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_.
  Quaestiones Math. (1993), 333–350.
- [Er97c] Erdős, P., _Some of my favorite problems and results_.
  The mathematics of Paul Erdős, I (1997), 47–67.
-/

open Filter SimpleGraph Real

open scoped Topology

namespace Erdos165

/--
Erdős Conjecture (Problem 165) [Er61, Er71, Er90b, Er93, Er97c]:

There exists a constant $c > 0$ such that $R(3,k) \sim c \cdot k^2 / \log k$, i.e.,
$$
  \lim_{k \to \infty} \frac{R(3,k)}{k^2 / \log k} = c.
$$

The conjectured value is $c = 1/2$.
-/
@[category research open, AMS 5]
theorem erdos_165 : answer(sorry) ↔
    ∃ c : ℝ, 0 < c ∧
    Tendsto (fun k : ℕ =>
      (graphRamseyNumber 3 k : ℝ) / ((k : ℝ) ^ 2 / Real.log (k : ℝ)))
      atTop (nhds c) := by
  sorry

/--
Erdős Problem 165 — conjectured value $c = 1/2$:

$$
  \lim_{k \to \infty} \frac{R(3,k)}{k^2 / \log k} = \frac{1}{2}.
$$
-/
@[category research open, AMS 5]
theorem erdos_165_conjectured_value :
    Tendsto (fun k : ℕ =>
      (graphRamseyNumber 3 k : ℝ) / ((k : ℝ) ^ 2 / Real.log (k : ℝ)))
      atTop (nhds (1 / 2)) := by
  sorry

-- TODO: Formalize the known bounds (c+o(1))k²/log k ≤ R(3,k) ≤ (1+o(1))k²/log k
-- with c ≥ 1/2 [HHKP25].

end Erdos165
