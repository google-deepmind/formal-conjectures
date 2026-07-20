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
# Erdős Problem 750

*References:*
- [erdosproblems.com/750](https://www.erdosproblems.com/750)
- [EHS82] Erdős, P. and Hajnal, A. and Szemerédi, E., On almost bipartite large chromatic graphs.
  Theory and practice of combinatorics (1982), 117-123.
- [Er69b] Erdős, P., Problems and results in chromatic graph theory. Proof Techniques in Graph
  Theory (1969), 27-35.
- [Er94b] Erdős, Paul, _Some problems in number theory, combinatorics and combinatorial geometry_.
  Math. Pannon. (1994), 261-269.
- [Er95d] Erdős, Paul, On some problems in combinatorial set theory. Publ. Inst. Math. (Beograd)
  (N.S.) (1995), 61-65.
- [ErHa67b] Erdős, P. and Hajnal, András, On chromatic graphs. Mat. Lapok (1967), 1--4.
- [UlamErdos750](https://www.ulam.ai/research/erdos750.pdf)
-/

open Filter Finset NNReal

namespace Erdos750

/--
Let $f(m)$ be some function such that $f(m)\to \infty$ as $m\to \infty$. Does there exist a
graph $G$ of infinite chromatic number such that every subgraph on $m$ vertices contains
an independent set of size at least $\frac{m}{2}-f(m)$?

Note that in [Er94b] the function $f$ generalises a (proven) result for $f(m) = \epsilon m$,
where $\epsilon > 0$. Hence we should assume it is non-negative valued.

The existence of such a graph was proved [UlamErdos750] by GPT 5.5 Pro (prompted by Chojecki).
Indeed, this constructs a graph with infinite chromatic number such that every subgraph on $m$
vertices can be made bipartite after deleting at most $f(m)$ many vertices.

This was formalized in Lean by Ammanamanchi using Claude Code 4.7 and GPT-5.5 Pro.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/Shashi456/erdos-formalizations/blob/main/Erdos/P750/Proof.lean"]
theorem erdos_750 :
    answer(True) ↔ ∀ (f : ℕ → ℝ≥0) (hf : atTop.Tendsto f atTop),
      ∃ (V : Type*) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
        ∀ (m : ℕ) (S : Set V), 0 < m → S.ncard = m →
          ∃ I ⊆ S, G.IsIndepSet I ∧ m / 2 - f m ≤ I.ncard := by
  sorry

/--
In [Er69b] Erdős conjectures this for $f(m)=\epsilon m$ for any fixed $\epsilon>0$. This follows
from a result of Erdős, Hajnal, and Szemerédi [EHS82], as described by Sellke in the comments.
-/
@[category research solved, AMS 5]
theorem erdos_750.variants.epsilon :
    answer(True) ↔ ∀ (ε : ℝ≥0), ε > 0 →
      ∃ (V : Type*) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
        ∀ (m : ℕ) (S : Set V), 0 < m → S.ncard = m →
          ∃ I ⊆ S, G.IsIndepSet I ∧ m / 2 - ε * m ≤ I.ncard := by
  sorry

/--
In [ErHa67b] Erdős and Hajnal prove this for $f(m)\geq cm$ for all $c>1/4$.
-/
@[category research solved, AMS 5]
theorem erdos_750.variants.c_gt_quarter :
    answer(True) ↔ ∀ (c : ℝ≥0), c > 1 / 4 →
      ∃ (V : Type*) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
        ∀ (m : ℕ) (S : Set V), 0 < m → S.ncard = m →
          ∃ I ⊆ S, G.IsIndepSet I ∧ m / 2 - c * m ≤ I.ncard := by
  sorry

end Erdos750
