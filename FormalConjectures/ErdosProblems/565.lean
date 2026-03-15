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
# Erdős Problem 565

*Reference:* [erdosproblems.com/565](https://www.erdosproblems.com/565)

Let $R^*(G)$ be the induced Ramsey number: the minimal $m$ such that there is a
graph $H$ on $m$ vertices such that any 2-colouring of the edges of $H$ contains
an induced monochromatic copy of $G$.

The existence of $R^*(G)$ for all finite graphs was established independently by
Deuber [De75], Erdős, Hajnal, and Pósa [EHP75], and Rödl [Ro73].

A problem of Erdős and Rödl. Kohayakawa, Prömel, and Rödl [KPR98] proved
$R^*(G) < 2^{O(n(\log n)^2)}$. Fox and Sudakov [FoSu08] gave an alternative
proof. Conlon, Fox, and Sudakov [CFS12] improved this to $R^*(G) < 2^{O(n \log n)}$.
Proved by Aragão, Campos, Dahia, Filipe, and Marciano [ACDFM25].

[De75] Deuber, W., _Generalizations of Ramsey's theorem_. Infinite and finite sets
(Colloq., Keszthely, 1973) (1975), 323-332.

[EHP75] Erdős, P., Hajnal, A., and Pósa, L., _Strong embeddings of graphs into
colored graphs_. Infinite and finite sets (Colloq., Keszthely, 1973) (1975), 585-595.

[Ro73] Rödl, V., _The dimension of a graph and generalized Ramsey theorems_. Thesis
(1973).

[KPR98] Kohayakawa, Y., Prömel, H. J., and Rödl, V., _Induced Ramsey numbers_.
Combinatorica **18** (1998), 373-404.

[FoSu08] Fox, J. and Sudakov, B., _Induced Ramsey-type theorems_. Advances in
Mathematics **219** (2008), 1771-1800.

[CFS12] Conlon, D., Fox, J., and Sudakov, B., _On two problems in graph Ramsey
theory_. Combinatorica **32** (2012), 513-535.

[ACDFM25] Aragão, L., Campos, M., Dahia, G., Filipe, J., and Marciano, J., _An
exponential upper bound for induced Ramsey numbers_. arXiv:2509.22629 (2025).
-/

open SimpleGraph

namespace Erdos565

/-- The induced Ramsey number $R^*(G)$: the minimum $m$ such that there exists a
graph $H$ on $m$ vertices where every 2-colouring of the edges of $H$ contains
an induced monochromatic copy of $G$.

An induced monochromatic copy of $G$ means: there is an injection
$f : V \hookrightarrow [m]$ and a colour $b \in \{0, 1\}$ such that for all
distinct $u, v \in V$, $G$ has edge $\{u, v\}$ if and only if $H$ has edge
$\{f(u), f(v)\}$ with colour $b$. -/
noncomputable def inducedRamseyNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {m : ℕ | ∃ (H : SimpleGraph (Fin m)),
    ∀ (c : Fin m → Fin m → Bool),
    (∀ i j, c i j = c j i) →
    ∃ (b : Bool) (f : V → Fin m), Function.Injective f ∧
      ∀ u v, u ≠ v → (G.Adj u v ↔ (H.Adj (f u) (f v) ∧ c (f u) (f v) = b))}

/--
Erdős Problem 565: There exists a constant $C$ such that for any graph $G$ on
$n$ vertices, the induced Ramsey number $R^*(G) \leq 2^{Cn}$.

A problem of Erdős and Rödl. Proved by Aragão, Campos, Dahia, Filipe,
and Marciano [ACDFM25].
-/
@[category research solved, AMS 5]
theorem erdos_565 :
    ∃ C : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      inducedRamseyNumber G ≤ 2 ^ (C * n) := by
  sorry

end Erdos565
