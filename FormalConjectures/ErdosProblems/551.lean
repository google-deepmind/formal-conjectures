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
# Erdős Problem 551

*Reference:* [erdosproblems.com/551](https://www.erdosproblems.com/551)

Let $R(C_k, K_n)$ denote the Ramsey number for a cycle $C_k$ versus a complete graph $K_n$: the
least $N$ such that every red/blue colouring of the edges of $K_N$ contains a red cycle of length
$k$ or a blue $K_n$. Bondy and Erdős conjectured that for all $k \ge n \ge 3$ with
$(k, n) \neq (3, 3)$,
$$R(C_k, K_n) = (k - 1)(n - 1) + 1.$$

We model a red/blue edge colouring of $K_N$ by a `SimpleGraph (Fin N)`: `G` is the red graph, so a
red $C_k$ is a copy of `cycleGraph k` contained in `G`, and a blue $K_n$ is an independent set of
size `n` in `G` (i.e. an `n`-clique in the complement).
-/

open SimpleGraph

namespace Erdos551

/-- The Ramsey number $R(C_k, K_n)$: the least $N$ such that every `SimpleGraph (Fin N)` (the "red"
graph of a two-colouring of $K_N$) either contains `cycleGraph k` as a subgraph (a red $C_k$) or has
an independent set of size `n` (a blue $K_n$). -/
noncomputable def ramseyCycleClique (k n : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ G : SimpleGraph (Fin N),
    (cycleGraph k).IsContained G ∨ ∃ s : Finset (Fin N), G.IsNIndepSet n s}

/--
**Erdős Problem 551.** For all $k \ge n \ge 3$ with $(k, n) \neq (3, 3)$, the cycle–complete
Ramsey number is
$$R(C_k, K_n) = (k - 1)(n - 1) + 1.$$
-/
@[category research open, AMS 5]
theorem erdos_551 (k n : ℕ) (hn : 3 ≤ n) (hkn : n ≤ k) (hne : (k, n) ≠ (3, 3)) :
    ramseyCycleClique k n = (k - 1) * (n - 1) + 1 := by
  sorry

/-- Sanity check: the defining set of `ramseyCycleClique` is upward closed. If some `N` forces a red
`C_k` or a blue `K_n`, then so does any larger `N'`: pull the red graph on `Fin N'` back along the
inclusion `Fin N ↪ Fin N'` (an induced subgraph on the first `N` vertices), apply the hypothesis for
`N`, and transport the red `C_k` or blue independent set back up along that embedding. This
validates that `ramseyCycleClique` is the infimum of a genuine "threshold" set. -/
@[category test, AMS 5]
theorem ramseyCycleClique_setOf_upward_closed (k n : ℕ) :
    ∀ N ∈ {N : ℕ | ∀ G : SimpleGraph (Fin N),
        (cycleGraph k).IsContained G ∨ ∃ s : Finset (Fin N), G.IsNIndepSet n s},
      ∀ N', N ≤ N' → N' ∈ {N : ℕ | ∀ G : SimpleGraph (Fin N),
        (cycleGraph k).IsContained G ∨ ∃ s : Finset (Fin N), G.IsNIndepSet n s} := by
  intro N hN N' hNN' G'
  set f : Fin N ↪ Fin N' := Fin.castLEEmb hNN' with hf
  set G : SimpleGraph (Fin N) := SimpleGraph.comap f G' with hG
  have emb : G ↪g G' := SimpleGraph.Embedding.comap f G'
  rcases hN G with hcyc | ⟨s, hs⟩
  · exact Or.inl (hcyc.trans ⟨emb.toCopy⟩)
  · refine Or.inr ⟨s.map f, ?_, ?_⟩
    · rw [Finset.coe_map]
      intro x hx y hy hxy
      simp only [Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have hab : a ≠ b := fun h => hxy (by rw [h])
      have := hs.isIndepSet ha hb hab
      rwa [hG, comap_adj] at this
    · rw [Finset.card_map]; exact hs.card_eq

end Erdos551
