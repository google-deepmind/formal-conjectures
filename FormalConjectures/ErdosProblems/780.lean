/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 780

*References:*
- [erdosproblems.com/780](https://www.erdosproblems.com/780)
- [Er76] Erdős, Paul, _Problems and results in combinatorial analysis_. Colloquio Internazionale
  sulle Teorie Combinatorie (Roma, 1973), Tomo II (1976), 3-17.
- [Lo78] Lovász, L., _Kneser's conjecture, chromatic number, and homotopy_. J. Combin. Theory
  Ser. A (1978), 319-324.
- [AFL86] Alon, N. and Frankl, P. and Lovász, L., _The chromatic number of Kneser hypergraphs_.
  Trans. Amer. Math. Soc. (1986), 359-370.
-/

@[expose] public section

namespace Erdos780

/--
Suppose $n\geq kr+(t-1)(k-1)$ and the edges of the complete $r$-uniform hypergraph on $n$
vertices are $t$-coloured. Prove that some colour class must contain $k$ pairwise disjoint edges.

In other words, this problem asks to determine the chromatic number of the Kneser hypergraph.
When $k=2$ this was conjectured by Kneser and proved by Lovász [Lo78]. The general case was
proved by Alon, Frankl, and Lovász [AFL86].
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos780.lean#L345"]
theorem erdos_780 (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t)
    (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1 := by
  sorry

/--
This would be best possible: if $n=kr-1+(t-1)(k-1)$ then decomposing $[n]$ as one set $X_1$ of
size $kr-1$ and $t-1$ sets $X_2,\ldots,X_{t}$ of size $k-1$, a colouring without $k$ pairwise
disjoint edges is given colouring all subsets of $X_1$ in colour $1$ and assigning an edge with
colour $2\leq i\leq t$ if $i$ is minimal such that $X_i$ intersects the edge.
-/
@[category textbook, AMS 5]
theorem erdos_780.variants.sharp (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1 := by
  sorry

end Erdos780
