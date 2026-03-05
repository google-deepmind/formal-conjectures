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
# Erdős Problem 166

*Reference:* [erdosproblems.com/166](https://www.erdosproblems.com/166)

Prove that $R(4,k) \gg k^3 / (\log k)^{O(1)}$.

$R(4,k)$ is the Ramsey number: the minimum $N$ such that every simple graph
on $N$ vertices contains either a $4$-clique or an independent set of size $k$
(equivalently, a $k$-clique in the complement).

Ajtai, Komlós, and Szemerédi [AKS80] proved the upper bound
$R(4,k) \ll k^3 / (\log k)^2$.
Spencer [Sp77] proved $R(4,k) \gg (k \log k)^{5/2}$.
Mattheus and Verstraëte [MaVe23] proved $R(4,k) \gg k^3 / (\log k)^4$,
resolving this conjecture.

[AKS80] Ajtai, M., Komlós, J., and Szemerédi, E., *A note on Ramsey numbers*,
J. Combin. Theory Ser. A **29** (1980), 354–360.

[Sp77] Spencer, J., *Asymptotic lower bounds for Ramsey functions*, Discrete Math.
**20** (1977), 69–76.

[MaVe23] Mattheus, S. and Verstraëte, J., *The asymptotics of $r(4,t)$*,
Ann. of Math. **199** (2024), 919–941.

[Er90b, Er91, Er93, Er97c] Various papers of Erdős posing and discussing this problem.
-/

open SimpleGraph Real

namespace Erdos166

/-- The Ramsey number $R(4,k)$: the minimum $N$ such that every simple graph
on $N$ vertices contains either a $4$-clique or an independent set of
size $k$ (a $k$-clique in the complement). -/
noncomputable def ramseyR4 (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree 4 ∨ ¬Gᶜ.CliqueFree k}

/--
Erdős Problem 166 [Er90b, Er91, Er93, Er97c]:

There exist constants $C > 0$ and $\alpha \in \mathbb{N}$ such that for all sufficiently large $k$,
$$
  R(4,k) \geq C \cdot k^3 / (\log k)^\alpha.
$$

In asymptotic notation: $R(4,k) \gg k^3 / (\log k)^{O(1)}$.

This was proved by Mattheus and Verstraëte [MaVe23], who showed
$R(4,k) \gg k^3 / (\log k)^4$.
-/
@[category research solved, AMS 5]
theorem erdos_166 :
    ∃ C : ℝ, 0 < C ∧
    ∃ α : ℕ,
    ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
      C * ((k : ℝ) ^ 3 / (Real.log (k : ℝ)) ^ α) ≤ (ramseyR4 k : ℝ) := by
  sorry

end Erdos166
