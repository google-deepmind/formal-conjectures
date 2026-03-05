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
# Erdős Problem 1015

*Reference:* [erdosproblems.com/1015](https://www.erdosproblems.com/1015)

Let $f(t, n)$ be minimal such that, in any two-colouring of the edges of $K_n$,
the vertices can be covered by vertex-disjoint monochromatic copies of $K_t$
(not necessarily the same colour) with at most $f(t, n)$ vertices remaining.

A question of Moon [Mo66b], who proved that $f(3, n) = 4$ for $n \geq 8$.
Erdős notes that $f(t) \ll 4^t$, by comparing to the Ramsey number $R(t)$.

Burr, Erdős, and Spencer [BES75] proved that, for $n$ sufficiently large
depending on $t$,
$$
f(t, n) = R(t, t-1) + x(t, n),
$$
where $0 \leq x(t, n) < t$ is such that $n + 1 \equiv R(t, t-1) + x \pmod{t}$.

[Er71] Erdős, P.

[Mo66b] Moon, J.W.

[BES75] Burr, S.A., Erdős, P., and Spencer, J.H.
-/

open Finset

namespace Erdos1015

/-- A set $S$ of vertices in `Fin n` is a monochromatic clique of colour $b$
under the edge-colouring $c$ if every pair of distinct vertices in $S$
has colour $b$. -/
def IsMonoClique (n : ℕ) (c : Fin n → Fin n → Bool) (S : Finset (Fin n))
    (b : Bool) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c i j = b

/-- The minimum number of leftover vertices $f(t, n)$: the smallest $r$ such
that for every symmetric 2-colouring of the edges of $K_n$, one can find
pairwise disjoint monochromatic $K_t$'s covering all but at most $r$
vertices. -/
noncomputable def minLeftover (t n : ℕ) : ℕ :=
  sInf {r : ℕ | ∀ (c : Fin n → Fin n → Bool), (∀ i j, c i j = c j i) →
    ∃ (cliques : Finset (Finset (Fin n))),
      (∀ S ∈ cliques, S.card = t) ∧
      (∀ S ∈ cliques, ∃ b : Bool, IsMonoClique n c S b) ∧
      (∀ S₁ ∈ cliques, ∀ S₂ ∈ cliques, S₁ ≠ S₂ → Disjoint S₁ S₂) ∧
      (Finset.univ \ cliques.biUnion id).card ≤ r}

/-- The 2-colour Ramsey number $R(s, t)$: the minimum $N$ such that every
symmetric 2-colouring of the edges of $K_N$ contains a monochromatic
clique of size $s$ in one colour or of size $t$ in the other. -/
noncomputable def ramseyNumber₂ (s t : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (c : Fin N → Fin N → Bool), (∀ i j, c i j = c j i) →
    (∃ S : Finset (Fin N), S.card = s ∧ IsMonoClique N c S false) ∨
    (∃ S : Finset (Fin N), S.card = t ∧ IsMonoClique N c S true)}

/--
Erdős Problem 1015 [Er71]:

For all $t \geq 2$, for $n$ sufficiently large depending on $t$, the minimum number
of leftover vertices when partitioning any 2-colouring of $K_n$ into
vertex-disjoint monochromatic $K_t$'s is exactly
$$
f(t, n) = R(t, t-1) + x,
$$
where $x \in \{0, \ldots, t-1\}$ satisfies $n + 1 \equiv R(t, t-1) + x \pmod{t}$.

Proved by Burr, Erdős, and Spencer [BES75].
-/
@[category research solved, AMS 5]
theorem erdos_1015 (t : ℕ) (ht : t ≥ 2) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      minLeftover t n =
        ramseyNumber₂ t (t - 1) + (n + 1 - ramseyNumber₂ t (t - 1)) % t := by
  sorry

end Erdos1015
