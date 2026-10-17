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
# The Alon–Saks–Seymour conjecture (disproved)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Graham%E2%80%93Pollak_theorem)
* [GP71] Graham, R. L. and Pollak, H. O. (1971). "On the addressing problem for loop switching."
  *Bell System Tech. J.* 50, pp. 2495--2519.
* [Ka91] Kahn, J. (1991). "Recent results on some not-so-recent hypergraph matching and covering
  problems." *Extremal problems for finite sets (Visegrád)*, Bolyai Soc. Math. Stud. 3,
  pp. 305--353.
* [HS12] Huang, H. and Sudakov, B. (2012). "A counterexample to the Alon–Saks–Seymour
  conjecture and related problems." *Combinatorica* 32, pp. 205--219.
  [arXiv:1002.4687](https://arxiv.org/abs/1002.4687)
-/

open SimpleGraph Finset

namespace AlonSaksSeymourConjecture

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Membership of the (unordered) pair `u, v` in the biclique with sides `A` and `B`. -/
def InBiclique (A B : Finset V) (u v : V) : Prop :=
  (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)

/-- A family of `k` bicliques with sides `A i`, `B i` is a **biclique partition** of `G` if the
sides are disjoint and every edge of `G` lies in exactly one of the bicliques (and every
biclique pair is an edge of `G`). -/
structure IsBicliquePartition (G : SimpleGraph V) (k : ℕ) (A B : Fin k → Finset V) : Prop where
  disjoint : ∀ i, Disjoint (A i) (B i)
  adj_iff : ∀ u v, G.Adj u v ↔ ∃ i, InBiclique (A i) (B i) u v
  unique : ∀ u v i j, InBiclique (A i) (B i) u v → InBiclique (A j) (B j) u v → i = j

/-- The **biclique partition number** `bp(G)`: the least number of edge-disjoint complete
bipartite subgraphs whose edge sets partition `E(G)`. -/
noncomputable def bicliquePartitionNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ A B : Fin k → Finset V, IsBicliquePartition G k A B}

/--
**The Alon–Saks–Seymour conjecture — disproved.**

It was conjectured (Alon, Saks and Seymour, c. 1991, see [Ka91]) that every graph whose edge
set is partitioned into $k$ complete bipartite subgraphs is $(k+1)$-colourable, i.e.
$\chi(G) \le \operatorname{bp}(G) + 1$ — the natural generalisation of the Graham–Pollak
theorem, which is the case $G = K_n$.

This is **false**: Huang and Sudakov [HS12] constructed graphs with
$\chi(G) \ge c \operatorname{bp}(G)^{6/5}$.
-/
@[category research solved, AMS 5]
theorem alon_saks_seymour_conjecture : answer(False) ↔
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.chromaticNumber ≤ bicliquePartitionNumber G + 1 := by
  sorry

/--
**The Graham–Pollak theorem (1971).**

The edge set of $K_n$ cannot be partitioned into fewer than $n - 1$ complete bipartite
subgraphs, and $n - 1$ suffice: $\operatorname{bp}(K_n) = n - 1$.

*Reference:* [GP71].
-/
@[category research solved, AMS 5]
theorem alon_saks_seymour_conjecture.variants.graham_pollak (n : ℕ) :
    bicliquePartitionNumber (completeGraph (Fin n)) = n - 1 := by
  sorry

/--
**Huang–Sudakov (2012): a polynomial separation.**

There is a constant $c > 0$ and, for every $k$, a graph $G$ with $\operatorname{bp}(G) \le k$
and $\chi(G) \ge c\,k^{6/5}$.

*Reference:* [HS12].
-/
@[category research solved, AMS 5]
theorem alon_saks_seymour_conjecture.variants.huang_sudakov :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V), bicliquePartitionNumber G ≤ k ∧
        (c * (k : ℝ) ^ ((6 : ℝ) / 5) : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) := by
  sorry

omit [Fintype V] [DecidableEq V] in
/-- The empty family is a biclique partition of the empty graph. -/
@[category API, AMS 5]
lemma isBicliquePartition_bot :
    IsBicliquePartition (⊥ : SimpleGraph V) 0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) where
  disjoint i := Fin.elim0 i
  adj_iff u v := by simp
  unique u v i := Fin.elim0 i

omit [Fintype V] [DecidableEq V] in
/-- The empty graph has biclique partition number `0`. -/
@[category API, AMS 5]
lemma bicliquePartitionNumber_bot : bicliquePartitionNumber (⊥ : SimpleGraph V) = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le ⟨_, _, isBicliquePartition_bot⟩)

omit [Fintype V] [DecidableEq V] in
/--
**The conjectured inequality holds for the empty graph.**

The empty graph has `bp = 0` and chromatic number at most `1`, so `χ ≤ bp + 1`.
-/
@[category test, AMS 5]
theorem alon_saks_seymour_conjecture.variants.bot :
    (⊥ : SimpleGraph V).chromaticNumber ≤ bicliquePartitionNumber (⊥ : SimpleGraph V) + 1 := by
  rw [bicliquePartitionNumber_bot, Nat.cast_zero, zero_add]
  exact Colorable.chromaticNumber_le ⟨⟨fun _ => 0, fun h => by simp at h⟩⟩

end AlonSaksSeymourConjecture
