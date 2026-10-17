/-
Copyright 2025 The Formal Conjectures Authors.

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
public import FormalConjectures.ErdosProblems.«753»

/-!
# Erdős Problem 799

*References:*
- [erdosproblems.com/799](https://www.erdosproblems.com/799)
- [ERT80] Erdős, Paul and Rubin, Arthur L. and Taylor, Herbert, _Choosability in graphs_. (1980),
  125-157.
- [Al92] Alon, Noga, _Choice numbers of graphs: a probabilistic approach_. Combin. Probab.
  Comput. (1992), 107-114.
- [AKS99] Alon, Noga and Krivelevich, Michael and Sudakov, Benny, _List coloring of random and
  pseudo-random graphs_. Combinatorica (1999), 453-472.
-/

@[expose] public section

open Filter Asymptotics Real Erdos753

namespace Erdos799

open scoped Classical in
/-- The proportion of (labelled) graphs on `n` vertices satisfying `P`. A property holds for
*almost all graphs* if this proportion tends to `1`. -/
noncomputable def proportion (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) (n : ℕ) : ℝ :=
  ((Finset.univ.filter (P n)).card : ℝ) / Fintype.card (SimpleGraph (Fin n))

/--
The list chromatic number $\chi_L(G)$ is defined to be the minimal $k$ such that for any
assignment of a list of $k$ colours to each vertex of $G$ (perhaps different lists for different
vertices) a colouring of each vertex by a colour on its list can be chosen such that adjacent
vertices receive distinct colours.

Is it true that $\chi_L(G)=o(n)$ for almost all graphs on $n$ vertices?

A problem of Erdős, Rubin and Taylor [ERT80]. The answer is yes: Alon [Al92] proved that in fact
the random graph on $n$ vertices with edge probability $1/2$ has
$\chi_L(G) \ll \frac{\log\log n}{\log n}n$ almost surely.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos799.lean#L127"]
theorem erdos_799 : answer(True) ↔
    ∃ b : ℕ → ℕ, ((fun n : ℕ ↦ (b n : ℝ)) =o[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      Tendsto (proportion fun n G ↦ listChromaticNumber G ≤ b n) atTop (nhds 1) := by
  sorry

/-- Alon [Al92] proved that the random graph on $n$ vertices with edge probability $1/2$ has
$\chi_L(G) \ll \frac{\log\log n}{\log n}n$ almost surely. -/
@[category research solved, AMS 5]
theorem erdos_799.variants.alon :
    ∃ C : ℝ, Tendsto (proportion fun n G ↦
      (listChromaticNumber G : ℝ) ≤ C * (log (log n) / log n) * n) atTop (nhds 1) := by
  sorry

/-- Alon, Krivelevich, and Sudakov [AKS99] improved this to $\chi_L(G) \asymp \frac{n}{\log n}$
almost surely. -/
@[category research solved, AMS 5]
theorem erdos_799.variants.alon_krivelevich_sudakov :
    ∃ c C : ℝ, 0 < c ∧ Tendsto (proportion fun n G ↦
      c * (n / log n) ≤ (listChromaticNumber G : ℝ) ∧
        (listChromaticNumber G : ℝ) ≤ C * (n / log n)) atTop (nhds 1) := by
  sorry

end Erdos799
