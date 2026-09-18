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
# Erdős Problem 914

*References:*
- [erdosproblems.com/914](https://www.erdosproblems.com/914)
- [CoHa63] Corrádi, K. and Hajnal, A., *On the maximal number of independent circuits in a graph*.
  Acta Math. Acad. Sci. Hungar. (1963), 423-439.
- [HaSz70] Hajnal, A. and Szemerédi, E., *Proof of a conjecture of P. Erdős*. (1970), 601-623.
- [KiKo08] Kierstead, H. A. and Kostochka, A. V., *A short proof of the Hajnal-Szemerédi theorem on
  equitable colouring*. Combin. Probab. Comput. (2008), 265-270.
-/

namespace Erdos914

/--
Let $r\geq 2$ and $m\geq 1$. Every graph with $rm$ vertices and minimum degree at least $m(r-1)$
contains $m$ vertex disjoint copies of $K_r$.

When $r=2$ this follows from Dirac's theorem. Corrádi and Hajnal [CoHa63] proved this when $r=3$.
Hajnal and Szemerédi [HaSz70] proved this for all $r\geq 4$.

A shorter proof was given by Kierstead and Kostochka [KiKo08].
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos914.lean"]
theorem erdos_914 {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m)
    (hdeg : m * (r - 1) ≤ G.minDegree) :
    ∃ K : Fin m → Finset V, (∀ i, G.IsNClique r (K i)) ∧
      Pairwise fun i j => Disjoint (K i) (K j) := by
  sorry

/--
Equivalently, every graph with $rm$ vertices and maximum degree at most $m-1$ has a proper vertex
colouring with $m$ colours in which every colour class has exactly $r$ vertices (an equitable
colouring).
-/
@[category research solved, AMS 5]
theorem erdos_914.variants.equitable_colouring {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type*}
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m)
    (hdeg : G.maxDegree ≤ m - 1) :
    ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r := by
  sorry

end Erdos914
