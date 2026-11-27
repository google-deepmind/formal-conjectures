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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 1015

*References:*
- [erdosproblems.com/1015](https://www.erdosproblems.com/1015)
- [BES75] Burr, S. A., Erdős, P. and Spencer, J. H., *Ramsey theorems for multiple copies of
  graphs*. Trans. Amer. Math. Soc. (1975), 87-99.
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Mo66b] Moon, J. W., *Disjoint triangles in chromatic graphs*. Math. Mag. (1966), 259-261.
-/

@[expose] public section

open Filter

namespace Erdos1015

local notation "R(" k ", " l ")" => SimpleGraph.classicalRamsey k l

/--
`CanLeave t n b` means that in any two-colouring of the edges of $K_n$ there are vertex disjoint
monochromatic copies of $K_t$ (not necessarily of the same colour) that cover all but at most $b$
vertices.

A two-colouring is given by a graph `G` on `Fin n`: the edges of `G` are red and the edges of
`Gᶜ` are blue.
-/
def CanLeave (t n b : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ∃ P : Finset (Finset (Fin n)),
    (P : Set (Finset (Fin n))).PairwiseDisjoint id ∧
    (∀ K ∈ P, G.IsNClique t K ∨ Gᶜ.IsNClique t K) ∧
    n - (P.biUnion id).card ≤ b

/--
$f(t, n)$ is the minimal $b$ such that, in any two-colouring of the edges of $K_n$, the vertices
can be covered by vertex disjoint monochromatic copies of $K_t$ with at most $b$ vertices
remaining.
-/
noncomputable def f (t n : ℕ) : ℕ :=
  sInf {b | CanLeave t n b}

/--
The value of $f(t, n)$ for large $n$: $R(t,t-1)-1+x$, where $0\leq x<t$ and
$n\equiv R(t,t-1)-1+x\pmod{t}$.
-/
noncomputable def erdos_1015.answer (t n : ℕ) : ℕ :=
  R(t, t - 1) - 1 + (n - (R(t, t - 1) - 1)) % t

/--
Let $f(t)$ be minimal such that, in any two-colouring of the edges of $K_n$, the vertices can be
partitioned into vertex disjoint monochromatic copies of $K_t$ (not necessarily the same colour)
with at most $f(t)$ vertices remaining. Estimate $f(t)$.

A question of Moon [Mo66b]. The answer depends on $n$, and Erdős presumably intended $n$ to be
sufficiently large depending on $t$. Burr, Erdős, and Spencer [BES75] proved that, for $t\geq 3$
and $n$ sufficiently large depending on $t$, the answer is $R(t,t-1)-1+x$, where $0\leq x<t$ is
such that $n\equiv R(t,t-1)-1+x\pmod{t}$.

The number of remaining vertices is always congruent to $n$ modulo $t$. For $t=3$ the value is
at most $4$, which is the result of Moon [Mo66b].
-/
@[category research solved, question value, AMS 5]
theorem erdos_1015 :
    ∀ t ≥ 3, ∀ᶠ n in atTop, f t n = erdos_1015.answer t n := by
  sorry

/--
Is it true that $f(t)\ll t$?

No: $f(t, n)\geq R(t,t-1)-1$ for all large $n$, and $R(t,t-1)$ grows exponentially in $t$.
-/
@[category research solved, question, AMS 5]
theorem erdos_1015.variants.linear :
    ¬ ∃ C : ℝ, ∀ t ≥ 1, ∀ᶠ n in atTop, (f t n : ℝ) ≤ C * t := by
  sorry

/--
Is it true that $f(t)^{1/t}\to 1$?

No: $f(t, n)\geq R(t,t-1)-1$ for all large $n$, and $R(t,t-1)\geq 2^{(t-1)/2}$.
-/
@[category research solved, question, AMS 5]
theorem erdos_1015.variants.root :
    ¬ ∀ ε > (0 : ℝ), ∀ᶠ t : ℕ in atTop, ∀ᶠ n in atTop,
      (f t n : ℝ) ^ (1 / (t : ℝ)) ≤ 1 + ε := by
  sorry

/--
Erdős [Er71] noted that $f(t)\ll 4^t$, by comparing to the Ramsey number $R(t)$.
-/
@[category research solved, AMS 5]
theorem erdos_1015.variants.upper :
    ∃ C : ℝ, ∀ t ≥ 1, ∀ᶠ n in atTop, (f t n : ℝ) ≤ C * 4 ^ t := by
  sorry

end Erdos1015
