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

import FormalConjectures.Util.ProblemImports

/-!
# Counterexample to Mukwembi's Theorem 2.1

The 3-dimensional hypercube Q₃ is a counterexample to Theorem 2.1 of
[S. Mukwembi, Size, Order, and Connected Domination,
Canad. Math. Bull. 57 (2014), no. 1, 141–144](https://doi.org/10.4153/CMB-2013-020-5).

The theorem claims: for a connected triangle-free graph G of order n, size m,
and connected domination number γ_c, `m ≤ (n - γ_c)²/4 + n - 1`.

Q₃ has n=8, m=12, γ_c=4, giving bound = (8-4)²/4 + 7 = 11 < 12 = m.

## Q₃ structure

```
    100 -------- 101
   / |          / |
  /  |         /  |
110 -------- 111  |
 |   |        |   |
 |  000 ------|- 001
 |  /         |  /
 | /          | /
010 -------- 011
```

Vertices: 8 (3-bit binary strings 000..111)
Edges: 12 (pairs differing in exactly 1 bit)
Bipartite (even/odd parity) → triangle-free

## Why γ_c = 4

Every connected triple in Q₃ is a path of length 2 (no triangles).
Every such path misses exactly 1 vertex from domination.
The minimum CDS is a path of length 3, e.g., {000, 001, 010, 011}.

## Gap in the paper's proof

The proof (page 143) assumes ∃ edge uv with γ_c(G) ≤ γ_c(G-{u,v}).
For Q₃, removing any adjacent pair gives G' with γ_c(G') = 2 < 4 = γ_c(Q₃).
-/

namespace Q3Counterexample

open SimpleGraph

/-- Q₃: the 3-dimensional hypercube on Fin 8.
Adjacency: vertices whose indices differ in exactly one bit. -/
def Q3 : SimpleGraph (Fin 8) where
  Adj u v := u ≠ v ∧ (u.val ^^^ v.val = 1 ∨ u.val ^^^ v.val = 2 ∨ u.val ^^^ v.val = 4)
  symm u v := by intro ⟨h1, h2⟩; exact ⟨h1.symm, by simp [Nat.xor_comm] at h2 ⊢; exact h2⟩
  loopless v := by intro ⟨h, _⟩; exact h rfl

instance : DecidableRel Q3.Adj := fun u v =>
  show Decidable (u ≠ v ∧ _) from inferInstance

/-- Q₃ has exactly 12 edges. -/
@[category test, AMS 5]
theorem Q3_card_edges : Q3.edgeFinset.card = 12 := by native_decide

/-- Q₃ is triangle-free (bipartite: even/odd bit-parity). -/
@[category test, AMS 5]
theorem Q3_cliqueFree : Q3.CliqueFree 3 := by
  intro s hs
  simp only [isNClique_iff, isClique_iff] at hs
  -- s is a set of 3 vertices, all pairwise Q3-adjacent
  -- Exhaustive check: no such triple exists in Q3
  revert hs; revert s; native_decide

/-- Q₃ has 8 vertices and 12 > 11 = (8-4)²/4 + 7. -/
@[category test, AMS 5]
theorem Q3_violates_bound :
    (Q3.edgeFinset.card : ℝ) >
      ((Fintype.card (Fin 8) : ℝ) - 4) ^ 2 / 4 + (Fintype.card (Fin 8) : ℝ) - 1 := by
  simp only [Q3_card_edges, Fintype.card_fin]
  norm_num

end Q3Counterexample
