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
# Erdős Problem 171

*Reference:* [erdosproblems.com/171](https://www.erdosproblems.com/171)

The density Hales-Jewett theorem: for every $\varepsilon > 0$ and integer $t \geq 1$, if $N$ is
sufficiently large and $A$ is a subset of $[t]^N$ of size at least $\varepsilon \cdot t^N$ then $A$
must contain a combinatorial line.

A combinatorial line in $[t]^N$ is a set $\{p_1, \ldots, p_t\}$ where there is a
non-empty set $S$ of "active" coordinates such that for each active coordinate $j$,
the $j$-th coordinate of $p_i$ is $i$, and for each inactive coordinate $j$, all points
share the same constant value.

This was proved by Furstenberg and Katznelson [FuKa91]. A new elementary proof
with quantitative bounds was given by the Polymath project [Po12].

[FuKa91] Furstenberg, H. and Katznelson, Y., _A density version of the Hales-Jewett theorem_.
J. Anal. Math. 57 (1991), 64-119.

[Po12] Polymath, D.H.J., _A new proof of the density Hales-Jewett theorem_.
Ann. of Math. 175 (2012), 1283-1327.

[ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory: some problems on additive number theory_. (1979).

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).
-/

namespace Erdos171

/-- A combinatorial line in $[t]^N$ is a family of $t$ points parametrized by $\operatorname{Fin} t$,
determined by a non-empty set $S$ of "active" coordinates and fixed values $c$
for inactive coordinates. The $i$-th point has coordinate $j$ equal to $i$ if $j$ is
active, and equal to $c(j)$ if $j$ is inactive. -/
def IsCombLine (t N : ℕ) (P : Fin t → (Fin N → Fin t)) : Prop :=
  ∃ (S : Finset (Fin N)) (c : Fin N → Fin t),
    S.Nonempty ∧
    ∀ (i : Fin t) (j : Fin N),
      P i j = if j ∈ S then i else c j

/--
Erdős Problem 171 (Density Hales-Jewett theorem) [ErGr79, ErGr80]:

For every $\varepsilon > 0$ and integer $t \geq 1$, there exists $N_0$ such that for all
$N \geq N_0$, every subset $A$ of $[t]^N$ with $|A| \geq \varepsilon \cdot t^N$ contains a
combinatorial line.
-/
@[category research solved, AMS 5]
theorem erdos_171 :
    ∀ (t : ℕ), 1 ≤ t →
    ∀ (ε : ℝ), 0 < ε →
    ∃ (N₀ : ℕ), ∀ (N : ℕ), N₀ ≤ N →
    ∀ (A : Finset (Fin N → Fin t)),
    (A.card : ℝ) ≥ ε * (t : ℝ) ^ N →
    ∃ (P : Fin t → (Fin N → Fin t)),
      IsCombLine t N P ∧ ∀ (i : Fin t), P i ∈ A := by
  sorry

end Erdos171
