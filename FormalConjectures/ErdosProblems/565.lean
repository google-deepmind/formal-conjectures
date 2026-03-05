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

A problem of Erdős and Rödl. Proved by Aragão, Campos, Dahia, Filipe,
and Marciano.
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
and Marciano.
-/
@[category research solved, AMS 5]
theorem erdos_565 :
    ∃ C : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      inducedRamseyNumber G ≤ 2 ^ (C * n) := by
  sorry

end Erdos565
