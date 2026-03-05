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
# Erdős Problem 914

*Reference:* [erdosproblems.com/914](https://www.erdosproblems.com/914)

Let $r \geq 2$ and $m \geq 1$. Every graph with $r \cdot m$ vertices and minimum degree at
least $m \cdot (r-1)$ contains $m$ vertex-disjoint copies of $K_r$.

When $r = 2$ this follows from Dirac's theorem. Corrádi and Hajnal proved this when $r = 3$.
Hajnal and Szemerédi proved this for all $r \geq 4$.

This is known as the Hajnal–Szemerédi theorem.

[HaSz70] Hajnal, A. and Szemerédi, E., _Proof of a conjecture of P. Erdős_. Combinatorial theory
and its applications, II (Proc. Colloq., Balatonfüred, 1969) (1970), 601-623.
-/

open SimpleGraph Finset

namespace Erdos914

/--
Erdős Problem 914 (proved by Hajnal and Szemerédi [HaSz70]):

Let $r \geq 2$ and $m \geq 1$. Every graph on $r \cdot m$ vertices with minimum degree at
least $m \cdot (r-1)$ contains $m$ vertex-disjoint copies of $K_r$ (complete graphs
on $r$ vertices).
-/
@[category research solved, AMS 5]
theorem erdos_914 (r m : ℕ) (hr : r ≥ 2) (hm : m ≥ 1)
    (G : SimpleGraph (Fin (r * m))) [DecidableRel G.Adj]
    (hdeg : ∀ v : Fin (r * m), G.degree v ≥ m * (r - 1)) :
    ∃ S : Fin m → Finset (Fin (r * m)),
      (∀ i, (S i).card = r) ∧
      (∀ i, G.IsClique (S i : Set (Fin (r * m)))) ∧
      (∀ i j, i ≠ j → Disjoint (S i) (S j)) := by
  sorry

end Erdos914
