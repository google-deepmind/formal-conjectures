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
# Ryser's conjecture

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Ryser%27s_conjecture)
- [Kő31] D. Kőnig, *Gráfok és mátrixok*, Matematikai és Fizikai Lapok **38** (1931), 116–119.
- [Ah01] R. Aharoni, *Ryser's conjecture for tripartite 3-graphs*, Combinatorica **21** (2001),
  1–4. [doi:10.1007/s004930170001](https://doi.org/10.1007/s004930170001)
- [Gy77] A. Gyárfás, *Partition coverings and blocking sets in hypergraphs* (in Hungarian),
  Communications of the Computer and Automation Institute of the Hungarian Academy of Sciences
  **71** (1977).
- [Tu79] Zs. Tuza, *Some special cases of Ryser's conjecture*, unpublished manuscript (1979).
- [Tu94] Zs. Tuza, *Monochromatic coverings and tree Ramsey numbers*, Discrete Math. **125**
  (1994), 377–384.
- [Wh26] P. White, *Tuza's Ryser-conjecture claim for four-partite hypergraphs with matching
  number two*, arXiv:2609.14281 (2026).
- [DKMS21] L. DeBiasio, Y. Kamel, G. McCourt and H. Sheats, *Generalizations and strengthenings
  of Ryser's conjecture*, Electron. J. Combin. **28(4)** (2021), P4.37.
  [doi:10.37236/9914](https://doi.org/10.37236/9914)
-/

@[expose] public section

namespace RyserConjecture

/-- An edge of an `r`-partite `r`-uniform hypergraph with vertex classes `V 0, ..., V (r - 1)`:
a choice of one vertex in each class. -/
abbrev Edge {r : ℕ} (V : Fin r → Type*) : Type _ := (i : Fin r) → V i

/-- The matching number $\nu(H)$: the largest number of pairwise disjoint edges of `H`. Two edges
are disjoint when they differ in every class. -/
noncomputable def matchingNumber {r : ℕ} {V : Fin r → Type*} (H : Finset (Edge V)) : ℕ :=
  sSup {n | ∃ M ⊆ H, (M : Set (Edge V)).Pairwise (fun e f ↦ ∀ i, e i ≠ f i) ∧ M.card = n}

/-- The cover number $\tau(H)$: the smallest number of vertices meeting every edge of `H`. A vertex
is an element of one of the classes, tagged with its class. -/
noncomputable def coverNumber {r : ℕ} {V : Fin r → Type*} (H : Finset (Edge V)) : ℕ :=
  sInf {n | ∃ C : Finset ((i : Fin r) × V i), (∀ e ∈ H, ∃ i, ⟨i, e i⟩ ∈ C) ∧ C.card = n}

/-- Ryser's bound for `r`-partite hypergraphs with matching number `n`: every finite `r`-partite
`r`-uniform hypergraph $H$ with $\nu(H) = n$ satisfies $\tau(H) \le (r - 1) \nu(H)$. -/
def RyserBound (r n : ℕ) : Prop :=
  ∀ (V : Fin r → Type*) (H : Finset (Edge V)), matchingNumber H = n →
    coverNumber H ≤ (r - 1) * matchingNumber H

/--
**Ryser's conjecture.** Every finite $r$-partite $r$-uniform hypergraph $H$ with $r \ge 2$
satisfies $\tau(H) \le (r - 1) \nu(H)$.
-/
@[category research open, AMS 5]
theorem ryser_conjecture :
    ∀ (r n : ℕ), 2 ≤ r → RyserBound r n := by
  sorry

/-- $r = 2$: Kőnig's theorem, $\tau(H) \le \nu(H)$ [Kő31]. -/
@[category research solved, AMS 5]
theorem ryser_conjecture.variants.two_partite :
    ∀ n : ℕ, RyserBound 2 n := by
  sorry

/-- $r = 3$: $\tau(H) \le 2 \nu(H)$ [Ah01]. -/
@[category research solved, AMS 5]
theorem ryser_conjecture.variants.three_partite :
    ∀ n : ℕ, RyserBound 3 n := by
  sorry

/-- $r = 4$, $\nu(H) = 1$: $\tau(H) \le 3$ [Gy77, Tu79, Tu94]. -/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/ryser-4partite-nu3/blob/48ef9493ec41c4e52d9ddc9ecbb87a51f655cf17/lean/RyserConjectureFC.lean#L77-L79"]
theorem ryser_conjecture.variants.four_partite_matchingNumber_one :
    RyserBound 4 1 := by
  sorry

/-- $r = 4$, $\nu(H) = 2$: $\tau(H) \le 6$ [Wh26]. -/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/ryser-4partite-nu3/blob/48ef9493ec41c4e52d9ddc9ecbb87a51f655cf17/lean/RyserConjectureFC.lean#L83-L85"]
theorem ryser_conjecture.variants.four_partite_matchingNumber_two :
    RyserBound 4 2 := by
  sorry

/-- $r = 4$, $\nu(H) = 3$: $\tau(H) \le 9$. -/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/ryser-4partite-nu3/blob/48ef9493ec41c4e52d9ddc9ecbb87a51f655cf17/lean/RyserConjectureFC.lean#L89-L91"]
theorem ryser_conjecture.variants.four_partite_matchingNumber_three :
    RyserBound 4 3 := by
  sorry

/-- $r = 4$, $\nu(H) \ge 4$. -/
@[category research open, AMS 5]
theorem ryser_conjecture.variants.four_partite_matchingNumber_ge_four :
    ∀ n : ℕ, 4 ≤ n → RyserBound 4 n := by
  sorry

/-- $r = 5$, $\nu(H) = 1$: $\tau(H) \le 4$ [Tu79]. -/
@[category research solved, AMS 5]
theorem ryser_conjecture.variants.five_partite_matchingNumber_one :
    RyserBound 5 1 := by
  sorry

/-- $r = 5$, $\nu(H) \ge 2$. -/
@[category research open, AMS 5]
theorem ryser_conjecture.variants.five_partite_matchingNumber_ge_two :
    ∀ n : ℕ, 2 ≤ n → RyserBound 5 n := by
  sorry

/-- $r \ge 6$: open, already for intersecting hypergraphs ($\nu(H) = 1$). -/
@[category research open, AMS 5]
theorem ryser_conjecture.variants.six_partite_or_more :
    ∀ (r n : ℕ), 6 ≤ r → RyserBound r n := by
  sorry

end RyserConjecture
