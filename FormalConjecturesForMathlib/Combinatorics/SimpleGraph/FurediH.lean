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

public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace SimpleGraph

/-- Index set for the pair-vertices $z_{ij}$ of Füredi's $H_k$, encoded as ordered pairs $i < j$. -/
abbrev FurediH.Pair (k : ℕ) := {p : Fin k × Fin k // p.1 < p.2}

/--
Vertices of Füredi's $H_k$: an apex $x$, vertices $y_1,\ldots,y_k$, and a vertex $z_{ij}$ for each
pair $i < j$.
-/
inductive FurediH.Vertex (k : ℕ) where
  | apex : Vertex k
  | leaf : Fin k → Vertex k
  | pair : FurediH.Pair k → Vertex k

/--
Adjacency of $H_k$ before `fromRel`: the apex is joined to every $y_i$, and each $z_{ij}$ is joined
to $y_i$ and $y_j$.
-/
def FurediH.adjRel {k : ℕ} : FurediH.Vertex k → FurediH.Vertex k → Prop
  | .apex, .leaf _ => True
  | .leaf a, .pair p => a = p.1.1 ∨ a = p.1.2
  | _, _ => False

/--
Füredi's graph $H_k$: vertices $x,y_1,\ldots,y_k$ and $z_{ij}$ for $i<j$, with $x$ adjacent to every
$y_i$ and each pair $y_i,y_j$ adjacent to the unique vertex $z_{ij}$.
-/
def furediH (k : ℕ) : SimpleGraph (FurediH.Vertex k) :=
  fromRel (FurediH.adjRel (k := k))

end SimpleGraph
