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
# Erdős Problem 77

See also OEIS sequence [A059442](https://oeis.org/A059442) and related problems
[627](https://www.erdosproblems.com/627), [1029](https://www.erdosproblems.com/1029).

*References:*
- [erdosproblems.com/77](https://www.erdosproblems.com/77)
- [Er61] Erdős, P., _Some unsolved problems_.
  Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961), 221–254.
- [Er69b] Erdős, P., _Problems and results in chromatic graph theory_.
  Proof Techniques in Graph Theory (Proc. Second Ann Arbor Graph Theory Conf., 1968) (1969), 27–35.
- [Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial analysis_.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97–109.
- [Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_.
  Combinatorica **1** (1981), 25–42.
- [Er88] Erdős, P., _Problems and results in combinatorial analysis and graph theory_.
  Discrete Math. (1988), 81–92.
- [Er90b] Erdős, P., _Problems and results on graphs and hypergraphs: similarities and
  differences_. Mathematics of Ramsey theory (1990), 12–28.
- [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_.
  Quaestiones Math. (1993), 333–350.
- [Er95] Erdős, P., _Some of my favourite problems in number theory, combinatorics, and
  geometry_. Resenhas (1995), 165–186.
- [Er97c] Erdős, P., _Some of my favorite problems and results_.
  The mathematics of Paul Erdős, I (1997), 47–67.
- [Er97d] Erdős, P., _Some recent problems and results in graph theory_.
  Discrete Math. (1997), 81–85.
- [Va99] Various authors, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest (1999).
- [CGMS23] Campos, M., Griffiths, S., Morris, R., and Sahasrabudhe, J.,
  _An exponential improvement for diagonal Ramsey_. arXiv:2303.09521 (2023).
- [GNNW24] Gupta, P., Ndiaye, N., Norin, S., and Wei, L.,
  _Optimizing the CGMS upper bound on Ramsey numbers_. arXiv:2407.19026 (2024).
- [BBCGHMST24] Balister, P., Bollobás, B., Campos, M., Griffiths, S., Hurley, E.,
  Morris, R., Sahasrabudhe, J., and Tiba, M., _Upper bounds for multicolour Ramsey numbers_.
  arXiv:2410.17197 (2024).
-/

open Filter SimpleGraph

open scoped Topology

namespace Erdos77

/--
Erdős Problem 77:

Find the value of $\lim_{k \to \infty} R(k)^{1/k}$, where $R(k)$ is the diagonal
Ramsey number.
-/
@[category research open, AMS 5]
theorem erdos_77 :
    Tendsto (fun k : ℕ =>
      (diagRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
      atTop (nhds (answer(sorry) : ℝ)) := by
  sorry

/--
Erdős Problem 77 — Existence variant:

The limit $\lim_{k \to \infty} R(k)^{1/k}$ exists. Erdős offered \$100 for a proof.
-/
@[category research open, AMS 5]
theorem erdos_77.variants.limit_exists :
    ∃ L : ℝ, Tendsto (fun k : ℕ =>
      (diagRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
      atTop (nhds L) := by
  sorry

/--
Erdős Problem 77 — Non-existence variant:

The limit $\lim_{k \to \infty} R(k)^{1/k}$ does not exist, i.e.,
$\liminf R(k)^{1/k} < \limsup R(k)^{1/k}$.
Erdős offered \$1,000 (later raised to \$10,000) for a proof.
-/
@[category research open, AMS 5]
theorem erdos_77.variants.limit_does_not_exist :
    ¬ ∃ L : ℝ, Tendsto (fun k : ℕ =>
      (diagRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
      atTop (nhds L) := by
  sorry

-- TODO: Formalize the known bounds √2 ≤ liminf R(k)^{1/k} ≤ limsup R(k)^{1/k} ≤ 3.7992...

end Erdos77
