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
# Erdős Problem 582

*References:*
- [erdosproblems.com/582](https://www.erdosproblems.com/582)
- [BiNe20] Bikov, Aleksandar and Nenov, Nedyalko, *On the independence number of
  $(3,3)$-Ramsey graphs and the Folkman number $F_e(3,3;4)$*. Australas. J. Combin.
  (2020), 35-50.
- [ErHa67] Erdős, P. and Hajnal, A., *Research Problem 2.5*. J. Comb. Theory (1967).
- [Fo70] Folkman, Jon, *Graphs with monochromatic complete subgraphs in every edge coloring*.
  SIAM J. Appl. Math. (1970), 19-24.
- [LRX14] Lange, Alexander R. and Radziszowski, Stanisław P. and Xu, Xiaodong, *Use of MAX-CUT
  for Ramsey arrowing of triangles*. J. Combin. Math. Combin. Comput. (2014), 61-71.
-/

namespace Erdos582

/--
A graph `G` is *edge-Ramsey for triangles* (in arrow notation, $G \to (K_3, K_3)^e$) if any
$2$-colouring of the edges of `G` produces a monochromatic $K_3$: three pairwise adjacent
vertices whose three connecting edges all receive the same colour.
-/
def EdgeRamseyTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ c : G.edgeSet → Fin 2,
    ∃ (u v w : V) (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w),
      c ⟨s(u, v), huv⟩ = c ⟨s(v, w), hvw⟩ ∧ c ⟨s(v, w), hvw⟩ = c ⟨s(u, w), huw⟩

/--
Does there exist a graph $G$ which contains no $K_4$, and yet any $2$-colouring of the edges
produces a monochromatic $K_3$?

Erdős and Hajnal [ErHa67] first asked for the existence of any such graph. Existence was proved
by Folkman [Fo70], but with very poor quantitative bounds. (As a result these quantities are
often called Folkman numbers.) The current best bounds on the minimal number of vertices $N$ of
such a graph are $21 \leq N \leq 786$, where the lower bound is due to Bikov and Nenov [BiNe20]
and the upper bound is due to Lange, Radziszowski, and Xu [LRX14].

We ask for a graph on a finite vertex type, following the quantitative discussion above (Folkman
numbers count the vertices of finite examples); the problem text itself does not stipulate
finiteness. A $2$-colouring of the edges is a map `G.edgeSet → Fin 2`, and "contains no $K_4$"
is `G.CliqueFree 4`.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos582.lean"]
theorem erdos_582 : answer(True) ↔
    ∃ (V : Type*) (_ : Fintype V) (G : SimpleGraph V),
      G.CliqueFree 4 ∧ EdgeRamseyTriangle G := by
  sorry

-- Divergences from the hosted formalisations (used as shape priors only):
-- * plby states `G.cliqueNum = 3`; the problem text asks only that $G$ "contains no $K_4$",
--   i.e. `G.CliqueFree 4` (jayyhk agrees). `cliqueNum = 3` is strictly stronger (it also
--   asserts that a triangle exists) and implies our conjunct.
-- * both hosted theorems are bare existentials; we wrap in `answer(True) ↔` per FC house
--   style for solved yes/no problems.
-- * both hosted theorems colour with `c : G.edgeSet → Bool`; we use `Fin 2`, the FC
--   convention for $r$-colourings (cf. ErdosProblems/617.lean).
-- * both hosted theorems carry an extra `(_ : DecidableEq V)` binder; dropped as
--   proof-irrelevant.
-- * both hosted theorems quantify `V : Type`; we use `V : Type*` following the FC precedent
--   in ErdosProblems/595.lean (the infinite version of this problem).

end Erdos582
