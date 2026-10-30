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
# Erdős Problem 622

*References:*
- [erdosproblems.com/622](https://www.erdosproblems.com/622)
- [DKM25] Draganić, Nemanja and Keevash, Peter and Müyesser, Alp,
  *Cyclic subsets in regular Dirac graphs*. International Mathematics Research Notices
  **2025** (2025), rnaf215. [arXiv:2503.01826](https://arxiv.org/abs/2503.01826).
- [Er99] Erdős, Paul, *A selection of problems and results in combinatorics*.
  Combinatorics, Probability and Computing **8** (1999), 1–6.
-/

@[expose] public section

namespace Erdos622

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A vertex set is spanned by a cycle if its induced subgraph has a Hamiltonian cycle. -/
def IsSpannedByCycle (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ v : (S : Set V), ∃ p : (G.induce (S : Set V)).Walk v v, p.IsHamiltonianCycle

open scoped Classical in
/-- The distinct vertex subsets of $G$ that are spanned by a cycle. -/
noncomputable def cycleSpannedSubsets (G : SimpleGraph V) : Finset (Finset V) :=
  Finset.univ.powerset.filter (IsSpannedByCycle G)

omit [Fintype V] in
/-- A cycle-spanned vertex set has at least three vertices. -/
@[category API, AMS 5]
lemma IsSpannedByCycle.three_le_card {G : SimpleGraph V} {S : Finset V}
    (h : IsSpannedByCycle G S) : 3 ≤ S.card := by
  obtain ⟨v, p, hp⟩ := h
  simpa [hp.length_eq] using hp.isCycle.three_le_length

open scoped Classical in
/--
Let $G$ be a regular graph with $2n$ vertices and degree $n+1$. Must $G$ have
$\gg 2^{2n}$ subsets that are spanned by a cycle?

This has been resolved by Draganić, Keevash, and Müyesser [DKM25], who prove the
asymptotically tight result that there are at least $(\tfrac{1}{2}+o(1))2^{2n}$
subsets which are spanned by a cycle.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos622.lean#L56"]
theorem erdos_622 : answer(True) ↔
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
      ∀ G : SimpleGraph (Fin (2 * n)), G.IsRegularOfDegree (n + 1) →
        c * (2 : ℝ) ^ (2 * n) ≤ (cycleSpannedSubsets G).card := by
  sorry

open scoped Classical in
/--
Draganić, Keevash, and Müyesser [DKM25, Theorem 4.1] proved that every
$(n+1)$-regular graph on $2n$ vertices has at least
$(\tfrac{1}{2}-\varepsilon)2^{2n}$ cycle-spanned subsets for all sufficiently large
$n$, uniformly over all such graphs.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos622.lean#L56"]
theorem erdos_622.variants.asymptotic_half :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      ∀ G : SimpleGraph (Fin (2 * n)), G.IsRegularOfDegree (n + 1) →
        ((1 / 2 : ℝ) - ε) * (2 : ℝ) ^ (2 * n) ≤ (cycleSpannedSubsets G).card := by
  sorry

end Erdos622
