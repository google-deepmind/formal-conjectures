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
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Erdős Problem 87

*Reference:* [erdosproblems.com/87](https://www.erdosproblems.com/87)

[Er95] Erdős, P., _Problems and results in combinatorial analysis and graph theory_, 1995, p. 14.

[FaMc93] Faudree, R. J. and McKay, B., _A conjecture of Erdős and the Ramsey number r(W)_,
J. Combin. Math. Combin. Comput. **13** (1993), 23–31.

Is it true that for every $\varepsilon > 0$ and all sufficiently large $k$, we have
$R(G) > (1 - \varepsilon)^k R(k)$ for every graph $G$ with chromatic number $\chi(G) = k$?
A stronger form asks whether $R(G) > c \cdot R(k)$ for some absolute constant $c > 0$.
Erdős originally conjectured $R(G) \geq R(k)$, which fails already for $k = 4$ [FaMc93].
-/

open SimpleGraph

namespace Erdos87

/-- The (diagonal) graph Ramsey number $R(H)$: the minimum $N$ such that every simple
graph $G$ on $N$ vertices either contains a copy of $H$ as a subgraph or its
complement contains a copy of $H$ (equivalently, every 2-colouring of $K_N$
contains a monochromatic copy of $H$). -/
noncomputable def graphRamseyNumber {U : Type*} (H : SimpleGraph U) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)),
    H.IsContained G ∨ H.IsContained Gᶜ}

/-- The classical diagonal Ramsey number $R(k) := R(K_k, K_k)$. -/
noncomputable def diagRamsey (k : ℕ) : ℕ :=
  graphRamseyNumber (⊤ : SimpleGraph (Fin k))

/--
**Erdős Problem 87** — Weak form (open). [Er95, p. 14]

Let $\varepsilon > 0$. Is it true that, if $k$ is sufficiently large, then
$$R(G) > (1 - \varepsilon)^k \cdot R(k)$$
for every graph $G$ with chromatic number $\chi(G) = k$?
-/
@[category research open, AMS 5]
theorem erdos_87 : answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      G.chromaticNumber = k →
      (diagRamsey k : ℝ) * (1 - ε) ^ k < (graphRamseyNumber G : ℝ) := by
  sorry

/--
**Erdős Problem 87** — Strong form (open). [Er95, p. 14]

Is there some $c > 0$ such that, for all large $k$,
$$R(G) > c \cdot R(k)$$
for every graph $G$ with chromatic number $\chi(G) = k$?
-/
@[category research open, AMS 5]
theorem erdos_87.variants.strong : answer(sorry) ↔
    ∃ c : ℝ, 0 < c ∧
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      G.chromaticNumber = k →
      c * (diagRamsey k : ℝ) < (graphRamseyNumber G : ℝ) := by
  sorry

end Erdos87
