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
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Erdős Problem 551

*Reference:* [erdosproblems.com/551](https://www.erdosproblems.com/551)

Prove that $R(C_k, K_n) = (k-1)(n-1) + 1$ for $k \geq n \geq 3$ (except when $n = k = 3$).

Here $R(C_k, K_n)$ is the off-diagonal Ramsey number, $C_k$ is the cycle graph on
$k$ vertices, and $K_n$ is the complete graph on $n$ vertices.

Asked by Erdős, Faudree, Rousseau, and Schelp [EFRS78]. This identity was
proved for $k > n^2 - 2$ by Bondy and Erdős [BoEr73], extended to $k \geq 4n + 2$ by
Nikiforov [Ni05], and established for $k \geq C \frac{\log n}{\log \log n}$ (for some
constant $C$), thus resolving the conjecture for sufficiently large $n$, by Keevash,
Long, and Skokan [KLS21].

[EFRS78] Erdős, P., Faudree, R. J., Rousseau, C. C., and Schelp, R. H.,
*On cycle-complete graph Ramsey numbers*, J. Graph Theory 2 (1978), 53–64.

[BoEr73] Bondy, J. A. and Erdős, P., *Ramsey numbers for cycles in graphs*,
J. Combin. Theory Ser. B (1973), 46–54.

[Ni05] Nikiforov, V., *The cycle-complete graph Ramsey numbers*,
Combin. Probab. Comput. (2005), 349–370.

[KLS21] Keevash, P., Long, E., and Skokan, J.,
*Cycle-complete Ramsey numbers*, Int. Math. Res. Not. IMRN (2021), 277–302.
-/

open SimpleGraph

namespace Erdos551

/-- The off-diagonal Ramsey number $R(G_1, G_2)$: the minimum $N$ such that every
graph $H$ on $N$ vertices contains a copy of $G_1$ or its complement contains a
copy of $G_2$. -/
noncomputable def offDiagRamseyNumber {V₁ V₂ : Type*}
    (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) : ℕ :=
  sInf {N : ℕ | ∀ (H : SimpleGraph (Fin N)),
    G₁ ⊑ H ∨ G₂ ⊑ Hᶜ}

/--
Erdős Problem 551 [EFRS78]:

Prove that $R(C_k, K_n) = (k - 1)(n - 1) + 1$ for $k \geq n \geq 3$, except when $n = k = 3$.

Here $C_k$ is the cycle graph on $k$ vertices and $K_n$ is the complete graph on $n$
vertices (expressed as $\top : \text{SimpleGraph}(\text{Fin}\; n)$).
-/
@[category research open, AMS 5]
theorem erdos_551 (k n : ℕ) (hk : k ≥ n) (hn : n ≥ 3) (hne : ¬(k = 3 ∧ n = 3)) :
    offDiagRamseyNumber (cycleGraph k) (⊤ : SimpleGraph (Fin n)) =
      (k - 1) * (n - 1) + 1 := by
  sorry

end Erdos551
