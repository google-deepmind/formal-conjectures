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
import FormalConjectures.ErdosProblems.«87»

/-!
# Erdős Problem 77

*Reference:* [erdosproblems.com/77](https://www.erdosproblems.com/77)

If $R(k)$ is the diagonal Ramsey number, the minimal $n$ such that every 2-colouring
of the edges of $K_n$ contains a monochromatic copy of $K_k$, then find the value of
$$\lim_{k \to \infty} R(k)^{1/k}.$$

Erdős proved $\sqrt{2} \leq \liminf R(k)^{1/k} \leq \limsup R(k)^{1/k} \leq 4$.
The upper bound has been improved to $3.7992\ldots$ by Gupta, Ndiaye, Norin, and
Wei [GNNW24], building on the breakthrough of Campos, Griffiths, Morris,
and Sahasrabudhe [CGMS23] who first improved the upper bound below 4.
A simplified proof of the sub-4 bound was given by Balister, Bollobás, Campos,
Griffiths, Hurley, Morris, Sahasrabudhe, and Tiba [BBCGHMST24].

Erdős conjectured the limit is "perhaps 2 but we have no real evidence for this" [Er93].

Erdős offered \$100 for proving the limit exists, and \$1,000 (later raised to \$10,000
in [Er88]) for proving it does not exist.

See also OEIS sequence A059442 and related problems #627, #1029.

[Er61] Erdős, P., _Graph theory and probability, II_. Canad. J. Math. **13** (1961), 346–352.

[Er69b] Erdős, P., _Some applications of Ramsey's theorem to additive number theory_.
European J. Combin. (1969).

[Er71] Erdős, P., _On some extremal problems on r-graphs_. Discrete Math. **1** (1971), 1–6.

[Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_.
Combinatorica **1** (1981), 25–42.

[Er88] Erdős, P., _Problems and results on chromatic numbers in finite and infinite graphs_.
Graph Theory with Applications to Algorithms and Computer Science (1988).

[Er90b] Erdős, P., _Some of my old and new problems in elementary number theory and
combinatorics_. Congressus Numerantium (1990).

[Er93] Erdős, P., _On some of my favourite theorems_. Combinatorics, Paul Erdős is Eighty,
Vol. 2 (1993).

[Er95] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Congressus Numerantium 107 (1995).

[Er97c] Erdős, P., _Some recent problems and results in graph theory_. Discrete Math.
**164** (1997), 81–85.

[Er97d] Erdős, P., _Some of my favourite problems in number theory, combinatorics,
and geometry_.

[Va99] Vaughan, R. C., _On the number of monochromatic complete subgraphs_.

[CGMS23] Campos, M., Griffiths, S., Morris, R., and Sahasrabudhe, J.,
_An exponential improvement for diagonal Ramsey_. (2023).

[GNNW24] Gupta, A., Ndiaye, M., Norin, S., and Wei, F.,
_An improved upper bound for diagonal Ramsey numbers_. (2024).

[BBCGHMST24] Balister, P., Bollobás, B., Campos, M., Griffiths, S., Hurley, E.,
Morris, R., Sahasrabudhe, J., and Tiba, M., _A simple proof of the upper bound for
diagonal Ramsey numbers_. (2024).
-/

open Filter Erdos87

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
      (diagRamsey k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
      atTop (nhds (answer(sorry) : ℝ)) := by
  sorry

/--
Erdős Problem 77 — Existence variant:

The limit $\lim_{k \to \infty} R(k)^{1/k}$ exists. Erdős offered \$100 for a proof.
-/
@[category research open, AMS 5]
theorem erdos_77.variants.limit_exists :
    ∃ L : ℝ, Tendsto (fun k : ℕ =>
      (diagRamsey k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
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
      (diagRamsey k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
      atTop (nhds L) := by
  sorry

end Erdos77
