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
# Erdős Problem 552

*Reference:* [erdosproblems.com/552](https://www.erdosproblems.com/552)

Determine the Ramsey number $R(C_4, S_n)$, where $S_n = K_{1,n}$ is the star on
$n + 1$ vertices.

[BEFRS89] Burr, Erdős, Faudree, Rousseau, and Schelp.

[Pa75] Parsons.
-/

open SimpleGraph

namespace Erdos552

/-- A graph $H$ contains a copy of graph $G$ (as a subgraph) if there is an injective
function from $V(G)$ to $V(H)$ that preserves adjacency. -/
def ContainsSubgraphCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧ ∀ u v, G.Adj u v → H.Adj (f u) (f v)

/-- The off-diagonal Ramsey number $R(G_1, G_2)$: the minimum $N$ such that every
graph $H$ on $N$ vertices contains a copy of $G_1$ or its complement contains a
copy of $G_2$. -/
noncomputable def offDiagRamseyNumber {V₁ V₂ : Type*}
    (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) : ℕ :=
  sInf {N : ℕ | ∀ (H : SimpleGraph (Fin N)),
    ContainsSubgraphCopy G₁ H ∨ ContainsSubgraphCopy G₂ Hᶜ}

/-- The cycle graph on $k$ vertices ($k \geq 3$): vertex $i$ is adjacent to vertex $j$ iff
they differ by exactly $1$ modulo $k$. -/
def cycleGraph (k : ℕ) (hk : k ≥ 3) : SimpleGraph (Fin k) where
  Adj i j := (i.val + 1) % k = j.val ∨ (j.val + 1) % k = i.val
  symm _ _ h := h.elim Or.inr Or.inl
  loopless v h := by
    rcases h with h | h <;> {
      have := v.isLt
      by_cases heq : v.val + 1 = k
      · rw [heq, Nat.mod_self] at h; omega
      · rw [Nat.mod_eq_of_lt (by omega)] at h; omega
    }

/-- The star graph $S_n = K_{1,n}$ on $n + 1$ vertices: vertex $0$ is the center,
adjacent to all other vertices. -/
def starGraph (n : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj i j := (i.val = 0 ∧ j.val ≠ 0) ∨ (j.val = 0 ∧ i.val ≠ 0)
  symm _ _ h := h.elim Or.inr Or.inl
  loopless v h := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact h2 h1

/--
Erdős Problem 552 [BEFRS89]:

Is it true that, for any $c > 0$, there are infinitely many $n$ such that
$R(C_4, S_n) \leq n + \sqrt{n} - c$?

Here $C_4$ is the cycle on $4$ vertices and $S_n = K_{1,n}$ is the star on $n + 1$
vertices. "Infinitely many" is formalised as: for every $N$ there exists $n \geq N$
satisfying the bound.

The known bounds are:
$$n + \sqrt{n} - 6n^{11/40} \leq R(C_4, S_n) \leq n + \lceil\sqrt{n}\rceil + 1.$$
The lower bound is due to [BEFRS89] and the upper bound is due to Parsons [Pa75].
Erdős offered \$100 for a proof or disproof.
-/
@[category research open, AMS 5]
theorem erdos_552 : answer(sorry) ↔
    ∀ c : ℝ, c > 0 →
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
      (offDiagRamseyNumber (cycleGraph 4 (by omega)) (starGraph n) : ℝ) ≤
        ↑n + Real.sqrt ↑n - c := by
  sorry

end Erdos552
