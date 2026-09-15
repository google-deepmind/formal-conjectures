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
# The bunkbed conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Bunkbed_conjecture)
* [Ka85] Kasteleyn, P. W., as reported in van den Berg, J. and Kahn, J. (2001). "A correlation
  inequality for connection events in percolation." *Ann. Probab.* 29, pp. 123--126.
* [GPZ24] Gladkov, N., Pak, I. and Zimin, A. (2024). "The bunkbed conjecture is false."
  [arXiv:2410.02545](https://arxiv.org/abs/2410.02545)
* [Ho24] Hollom, L. (2024). "The bunkbed conjecture is not robust to generalisation."
  [arXiv:2401.07301](https://arxiv.org/abs/2401.07301)
* [Ri22] Richthammer, T. (2022). "Bunkbed conjecture for complete bipartite graphs and related
  classes of graphs." [arXiv:2204.12931](https://arxiv.org/abs/2204.12931)
* [dB18] de Buyer, P. (2018). "A proof of the bunkbed conjecture for the complete graph at
  $p = \tfrac12$." [arXiv:1604.08439](https://arxiv.org/abs/1604.08439)
* [HKN23] Hutchcroft, T., Kent, A. and Nizić-Nikolac, P. (2023). "The bunkbed conjecture holds
  in the $p \uparrow 1$ limit." *Combin. Probab. Comput.* 32, pp. 363--369.
  [arXiv:2110.00282](https://arxiv.org/abs/2110.00282)
-/

open SimpleGraph Finset

namespace BunkbedConjecture

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **bunkbed graph** of `G` with posts `T`: two copies of `G` (the "bunks", indexed by
`Bool`) together with a "post" edge joining the two copies of each vertex in `T`. -/
def bunkbed (G : SimpleGraph V) (T : Finset V) : SimpleGraph (V × Bool) where
  Adj x y := (x.2 = y.2 ∧ G.Adj x.1 y.1) ∨ (x.1 = y.1 ∧ x.2 ≠ y.2 ∧ x.1 ∈ T)
  symm := ⟨fun x y h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h1.symm, h2.symm, h1 ▸ h3⟩⟩
  loopless := ⟨fun x h => by
    rcases h with ⟨-, h⟩ | ⟨-, h, -⟩
    · exact G.irrefl h
    · exact h rfl⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) :
    DecidableRel (bunkbed G T).Adj :=
  fun x y => inferInstanceAs (Decidable ((x.2 = y.2 ∧ G.Adj x.1 y.1) ∨
    (x.1 = y.1 ∧ x.2 ≠ y.2 ∧ x.1 ∈ T)))

open Classical in
/-- The probability that `u` and `v` are connected in the random subgraph of `H` obtained by
keeping each edge independently with probability `p` (Bernoulli bond percolation on `H`),
written as a finite sum over the edge subsets `F ⊆ E(H)`. -/
noncomputable def connectionProbability {W : Type*} [Fintype W] (H : SimpleGraph W) (p : ℝ)
    (u v : W) : ℝ :=
  ∑ F ∈ H.edgeFinset.powerset, p ^ F.card * (1 - p) ^ (H.edgeFinset.card - F.card) *
    (if (fromEdgeSet (↑F : Set (Sym2 W))).Reachable u v then 1 else 0)

/--
**The bunkbed conjecture (Kasteleyn, 1985) — disproved.**

For every finite graph $G$, every set of posts $T \subseteq V(G)$, every $p \in [0, 1]$ and all
vertices $u, v$, in Bernoulli bond percolation on the bunkbed graph the lower copy $(v, 0)$ was
conjectured to be at least as likely to be connected to $(u, 0)$ as the upper copy $(v, 1)$ is:
$\mathbb{P}\big((u,0) \leftrightarrow (v,1)\big) \le \mathbb{P}\big((u,0) \leftrightarrow (v,0)\big)$.

This is **false**: Gladkov, Pak and Zimin [GPZ24] exhibited an explicit counterexample, a graph on
$7222$ vertices with $p = \tfrac12$ (obtained from Hollom's hypergraph counterexample [Ho24]).
-/
@[category research solved, AMS 5 60]
theorem bunkbed_conjecture : answer(False) ↔
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (T : Finset V) (p : ℝ), 0 ≤ p → p ≤ 1 → ∀ u v : V,
      connectionProbability (bunkbed G T) p (u, false) (v, true) ≤
        connectionProbability (bunkbed G T) p (u, false) (v, false) := by
  sorry

/--
**Complete graphs (Richthammer 2022; de Buyer 2018 for $p = \tfrac12$).**

The bunkbed inequality holds when $G$ is a complete graph, for every set of posts and every
$p \in [0, 1]$.

*References:* [Ri22], [dB18].
-/
@[category research solved, AMS 5 60]
theorem bunkbed_conjecture.variants.complete_graph (n : ℕ) (T : Finset (Fin n)) (p : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (u v : Fin n) :
    connectionProbability (bunkbed (completeGraph (Fin n)) T) p (u, false) (v, true) ≤
      connectionProbability (bunkbed (completeGraph (Fin n)) T) p (u, false) (v, false) := by
  sorry

/--
**The $p \uparrow 1$ limit (Hutchcroft–Kent–Nizić-Nikolac 2023).**

For every finite graph $G$ and set of posts $T$ there is a threshold $p_0 < 1$ such that the
bunkbed inequality holds for all $p \in [p_0, 1]$.

*Reference:* [HKN23].
-/
@[category research solved, AMS 5 60]
theorem bunkbed_conjecture.variants.p_near_one {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) :
    ∃ p₀ : ℝ, p₀ < 1 ∧ ∀ p : ℝ, p₀ ≤ p → p ≤ 1 → ∀ u v : V,
      connectionProbability (bunkbed G T) p (u, false) (v, true) ≤
        connectionProbability (bunkbed G T) p (u, false) (v, false) := by
  sorry

open Classical in
/-- The percolation weights sum to `1`: `∑_{F ⊆ E} p^|F| (1-p)^{|E|-|F|} = 1`. -/
@[category API, AMS 5 60]
lemma sum_weights_eq_one {W : Type*} [Fintype W] (H : SimpleGraph W) (p : ℝ) :
    ∑ F ∈ H.edgeFinset.powerset, p ^ F.card * (1 - p) ^ (H.edgeFinset.card - F.card) = 1 := by
  rw [Finset.sum_pow_mul_eq_add_pow]
  simp

open Classical in
/-- A connection probability is at most `1` when `0 ≤ p ≤ 1`. -/
@[category API, AMS 5 60]
lemma connectionProbability_le_one {W : Type*} [Fintype W] (H : SimpleGraph W) (p : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (u v : W) :
    connectionProbability H p u v ≤ 1 := by
  calc connectionProbability H p u v
      ≤ ∑ F ∈ H.edgeFinset.powerset, p ^ F.card * (1 - p) ^ (H.edgeFinset.card - F.card) := by
        unfold connectionProbability
        refine Finset.sum_le_sum fun F _ => ?_
        have hw : 0 ≤ p ^ F.card * (1 - p) ^ (H.edgeFinset.card - F.card) := by
          have : 0 ≤ 1 - p := by linarith
          positivity
        split_ifs <;> simp [hw]
    _ = 1 := sum_weights_eq_one H p

open Classical in
/-- A vertex is connected to itself with probability `1`. -/
@[category API, AMS 5 60]
lemma connectionProbability_self {W : Type*} [Fintype W] (H : SimpleGraph W) (p : ℝ) (u : W) :
    connectionProbability H p u u = 1 := by
  calc connectionProbability H p u u
      = ∑ F ∈ H.edgeFinset.powerset, p ^ F.card * (1 - p) ^ (H.edgeFinset.card - F.card) := by
        unfold connectionProbability
        exact Finset.sum_congr rfl fun F _ => by simp
    _ = 1 := sum_weights_eq_one H p

/--
**The diagonal case `u = v` of the bunkbed inequality holds.**

When `u = v` the right-hand side is the probability that `(u, 0)` is connected to itself, which
is `1`, so the inequality is just `connectionProbability_le_one`.
-/
@[category test, AMS 5 60]
theorem bunkbed_conjecture.variants.diagonal {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (p : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (u : V) :
    connectionProbability (bunkbed G T) p (u, false) (u, true) ≤
      connectionProbability (bunkbed G T) p (u, false) (u, false) := by
  rw [connectionProbability_self]
  exact connectionProbability_le_one _ p hp₀ hp₁ _ _

end BunkbedConjecture
