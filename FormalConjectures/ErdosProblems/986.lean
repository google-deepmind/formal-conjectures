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
# Erdős Problem 986

*Reference:* [erdosproblems.com/986](https://www.erdosproblems.com/986)

Erdős conjectured that for any fixed $k \geq 3$, the Ramsey number $R(k,n)$ satisfies
$R(k,n) \gg n^{k-1}/(\log n)^c$ for some constant $c > 0$.

Spencer [Sp77] proved the $k = 3$ case and Mattheus and Verstraëte [MaVe23]
proved the $k = 4$ case.

The best general bounds available are:
$$
n^{(k+1)/2} / (\log n)^{1/(k-2) - (k+1)/2} \ll_k R(k,n) \ll_k n^{k-1} / (\log n)^{k-2}
$$
The lower bound was proved by Bohman and Keevash [BoKe10].
The upper bound was proved by Ajtai, Komlós, and Szemerédi [AKS80].

[Sp77] Spencer, J., _Asymptotic lower bounds for Ramsey functions_. Discrete Math. 20 (1977),
69-76.

[MaVe23] Mattheus, S. and Verstraëte, J., _The asymptotics of $r(4,t)$_. Ann. of Math. 199
(2024), 919-941.

[BoKe10] Bohman, T. and Keevash, P., _The early evolution of the $H$-free process_. Invent.
Math. 181 (2010), 291-336.

[AKS80] Ajtai, M., Komlós, J. and Szemerédi, E., _A note on Ramsey numbers_. J. Combin.
Theory Ser. A 29 (1980), 354-360.

[Er90b] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Matematiche (Catania) 47 (1992), 231-240.
-/

open SimpleGraph Real

namespace Erdos986

/-- The Ramsey number $R(k,n)$: the minimum $N$ such that every simple graph
on $N$ vertices contains either a $k$-clique or an independent set of
size $n$ (an $n$-clique in the complement). -/
noncomputable def ramseyR (k n : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree k ∨ ¬Gᶜ.CliqueFree n}

/--
Erdős Conjecture (Problem #986) [Er90b]:

For any fixed $k \geq 3$, there exist constants $C > 0$ and $c \in \mathbb{N}$ with $c > 0$
such that for all sufficiently large $n$:
$$
R(k,n) \geq C \cdot n^{k-1} / (\log n)^c.
$$
In asymptotic notation: $R(k,n) \gg n^{k-1}/(\log n)^c$ for some $c > 0$.
-/
@[category research open, AMS 5]
theorem erdos_986 (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧
    ∃ c : ℕ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      C * ((n : ℝ) ^ (k - 1) / (Real.log (n : ℝ)) ^ c) ≤ (ramseyR k n : ℝ) := by
  sorry

end Erdos986
