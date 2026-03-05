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
# Erdős Problem 159

Is there some constant $c > 0$ such that $R(C_4, K_n) \ll n^{2-c}$?

*Reference:* [erdosproblems.com/159](https://www.erdosproblems.com/159)

[Er81] Erdős, P., *Problems and results in graph theory*.

[Er84d] Erdős, P., *On some problems in graph theory, combinatorial analysis and
combinatorial number theory*.

[EFRS78] Erdős, P., Faudree, R.J., Rousseau, C.C., and Schelp, R.H.

[Sp77] Spencer, J.
-/

open SimpleGraph

namespace Erdos159

/-- An injective graph homomorphism from $H$ to $G$ witnesses that $G$ contains
    a subgraph isomorphic to $H$. -/
def ContainsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The 4-cycle $C_4$: vertices $\operatorname{Fin} 4$, with $i$ adjacent to $j$ iff they are
    consecutive modulo 4 (i.e., the edges are $0$–$1$, $1$–$2$, $2$–$3$, $3$–$0$). -/
def C4 : SimpleGraph (Fin 4) where
  Adj i j := (i.val + 1) % 4 = j.val ∨ (j.val + 1) % 4 = i.val
  symm := fun _ _ h => h.elim Or.inr Or.inl
  loopless := by intro i; fin_cases i <;> decide

/-- The graph Ramsey number $R(C_4, K_n)$: the minimum $N$ such that every simple
    graph $G$ on $N$ vertices either contains a copy of $C_4$ as a subgraph, or the
    complement $G^c$ contains a copy of $K_n$ (i.e., $G$ has an independent set of
    size $n$). -/
noncomputable def ramseyC4Kn (n : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)),
    ContainsSubgraph G C4 ∨ ContainsSubgraph Gᶜ (⊤ : SimpleGraph (Fin n))}

/--
Erdős Conjecture (Problem 159) [Er81, Er84d]:

There exists a constant $c > 0$ such that $R(C_4, K_n) \ll n^{2-c}$, i.e.,
$R(C_4, K_n) = O(n^{2-c})$ as $n \to \infty$.

The Ramsey number $R(C_4, K_n)$ is the minimum $N$ such that every 2-colouring
of the edges of $K_N$ contains a monochromatic $C_4$ in one colour or a
monochromatic $K_n$ in the other colour.

The current bounds are:
$$n^{3/2} / (\log n)^{3/2} \ll R(C_4, K_n) \ll n^2 / (\log n)^2,$$
where the upper bound is due to Szemerédi [EFRS78] and the lower bound
to Spencer [Sp77]. Improving the upper bound to $n^{2-c}$ for any fixed
$c > 0$ remains open.
-/
@[category research open, AMS 5]
theorem erdos_159 :
    ∃ c : ℝ, 0 < c ∧
    ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (ramseyC4Kn n : ℝ) ≤ C * (n : ℝ) ^ (2 - c) := by
  sorry

end Erdos159
