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
import FormalConjecturesForMathlib.Combinatorics.Basic

/-!
# Erdős Problem 530

*Reference:* [erdosproblems.com/530](https://www.erdosproblems.com/530)

Let $\ell(N)$ be maximal such that in any finite set $A \subset \mathbb{R}$ of size $N$ there
exists a Sidon subset $S$ of size $\ell(N)$ (i.e. the only solutions to $a + b = c + d$ in $S$
are the trivial ones). Is it true that $\ell(N) \sim N^{1/2}$?

Originally asked by Riddell [Ri69]. Erdős noted the bounds
$N^{1/3} \ll \ell(N) \leq (1+o(1))N^{1/2}$ (the upper bound following from the case
$A = \{1, \ldots, N\}$). The lower bound was improved to $N^{1/2} \ll \ell(N)$ by Komlós,
Sulyok, and Szemerédi [KSS75]. The correct constant is unknown, but it is likely that the
upper bound is true, so that $\ell(N) \sim N^{1/2}$.

Alon and Erdős [AlEr85] posed the stronger conjecture that any set of size $N$ can be
decomposed into at most $(1+o(1))N^{1/2}$ Sidon sets.

See also Problem 1088 (higher-dimensional generalization), Guy's collection [Gu04]
(Problem C9), and OEIS sequence A143824.

[Er73] Erdős, P., p.120. [Er75f] Erdős, P., p.104. [Er80e] Erdős, P.

[Ri69] Riddell, J., *On sets of numbers containing no l terms in arithmetic progression*,
Nieuw Arch. Wisk. (3) (1969), 204–209.

[KSS75] Komlós, J., Sulyok, M. and Szemerédi, E., *Linear problems in combinatorial number
theory*, Acta Math. Acad. Sci. Hungar. (1975), 113–121.

[AlEr85] Alon, N. and Erdős, P., *An application of graph theory to additive number theory*,
European J. Combin. 6 (1985), 201–203.

[Gu04] Guy, Richard K., *Unsolved problems in number theory*. (2004), xviii+437.
-/

open Finset Filter

namespace Erdos530

/-- $\ell(N)$: the largest $k$ such that every $N$-element subset of $\mathbb{R}$ contains
a Sidon subset of size at least $k$. Equivalently, the minimum of `Finset.maxSidonSubsetCard A`
over all $N$-element sets $A \subset \mathbb{R}$. -/
noncomputable def sidonSubsetNumber (N : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ A : Finset ℝ, A.card = N ∧ A.maxSidonSubsetCard = m}

/--
Is it true that $\ell(N) \sim N^{1/2}$, i.e. the ratio $\ell(N) / \sqrt{N}$ tends to $1$
as $N \to \infty$? [Er73] [Er75f] [Er80e]

Known bounds: $N^{1/2} \ll \ell(N) \leq (1+o(1))N^{1/2}$. The lower bound
$N^{1/2} \ll \ell(N)$ is due to Komlós, Sulyok, and Szemerédi [KSS75]. The upper bound
follows from the case $A = \{1, \ldots, N\}$.
-/
@[category research open, AMS 5 11]
theorem erdos_530 :
    answer(sorry) ↔
    Tendsto (fun N : ℕ => (sidonSubsetNumber N : ℝ) / Real.sqrt (N : ℝ))
      atTop (nhds 1) := by
  sorry

end Erdos530
