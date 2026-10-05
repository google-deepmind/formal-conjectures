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
# Erdős Problem 1010

*References:*
- [erdosproblems.com/1010](https://www.erdosproblems.com/1010)
- [Er62d] Erdős, P., *On a theorem of Rademacher-Turán*. Illinois J. Math. (1962), 122-127.
- [LoSi76] Lovász, L. and Simonovits, Miklós, *On the number of complete subgraphs of a graph*.
  (1976), 431-441.
- [NiKh81] Nikiforov, V. S. and Khadzhiivanov, N. G., *Solution of the problem of P. Erdős on the
  number of triangles in graphs with $n$ vertices and $[n^2/4]+l$ edges*. C. R. Acad. Bulgare
  Sci. (1981), 969-970.
-/

@[expose] public section

open SimpleGraph

namespace Erdos1010

open scoped Classical in
/--
Let $t<\lfloor n/2\rfloor$. Does every graph on $n$ vertices with $\lfloor n^2/4\rfloor+t$ edges
contain at least $t\lfloor n/2\rfloor$ triangles?

Rademacher proved that every graph on $n$ vertices with $\lfloor n^2/4\rfloor+1$ edges contains at
least $\lfloor n/2\rfloor$ triangles. Erdős [Er62d] proved that every graph on $n$ vertices with
$\lfloor n^2/4\rfloor+t$ edges contains at least $t\lfloor n/2\rfloor$ triangles, for all $t<cn$,
for some constant $c>0$.

This is true, and was proved independently by Lovász and Simonovits [LoSi76] and Nikiforov and
Khadzhiivanov [NiKh81].
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1010.lean#L612"]
theorem erdos_1010 : answer(True) ↔ ∀ n t : ℕ, t < n / 2 → ∀ G : SimpleGraph (Fin n),
    G.edgeFinset.card = n ^ 2 / 4 + t → t * (n / 2) ≤ (G.cliqueFinset 3).card := by
  sorry

open scoped Classical in
/--
Rademacher proved that every graph on $n$ vertices with $\lfloor n^2/4\rfloor+1$ edges contains at
least $\lfloor n/2\rfloor$ triangles.
-/
@[category research solved, AMS 5]
theorem erdos_1010.variants.rademacher : ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    G.edgeFinset.card = n ^ 2 / 4 + 1 → n / 2 ≤ (G.cliqueFinset 3).card := by
  sorry

open scoped Classical in
/--
Erdős [Er62d] proved that every graph on $n$ vertices with $\lfloor n^2/4\rfloor+t$ edges contains
at least $t\lfloor n/2\rfloor$ triangles, for all $t<cn$, for some constant $c>0$.
-/
@[category research solved, AMS 5]
theorem erdos_1010.variants.erdos : ∃ c : ℝ, 0 < c ∧ ∀ n t : ℕ, t < c * n →
    ∀ G : SimpleGraph (Fin n), G.edgeFinset.card = n ^ 2 / 4 + t →
      t * (n / 2) ≤ (G.cliqueFinset 3).card := by
  sorry

end Erdos1010
