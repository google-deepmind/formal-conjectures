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
# Erdős Problem 833

Does there exist an absolute constant $c > 0$ such that, for all $r \geq 2$,
every $r$-uniform hypergraph with chromatic number $3$ has a vertex contained
in at least $(1+c)^r$ edges?

*Reference:* [erdosproblems.com/833](https://www.erdosproblems.com/833)

[Er71] Erdős, P., _Topics in combinatorial analysis_. Proc. Second Louisiana Conf. on
Combinatorics, Graph Theory and Computing (1971), 2–20, p. 105.

[Er74d] Erdős, P., _Problems and results on graphs and hypergraphs: similarities and
differences_. Mathematics of Ramsey Theory (1974).

[ErLo75] Erdős, P. and Lovász, L., *Problems and results on 3-chromatic hypergraphs and some
related questions*. Infinite and Finite Sets (Colloq., Keszthely, 1973), Vol. II, Colloq.
Math. Soc. János Bolyai, Vol. 10 (1975), 609–627.
-/

open Finset

namespace Erdos833

/-- A hypergraph on vertex type $V$, represented as a finset of edges,
where each edge is a finset of vertices. -/
structure Hypergraph (V : Type*) [DecidableEq V] where
  edges : Finset (Finset V)

/-- A hypergraph is $r$-uniform if every edge has exactly $r$ vertices. -/
def Hypergraph.IsUniform {V : Type*} [DecidableEq V] (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ e ∈ H.edges, e.card = r

/-- A proper coloring of a hypergraph: no edge with $\geq 2$ vertices is monochromatic. -/
def Hypergraph.IsProperColoring {V : Type*} [DecidableEq V] (H : Hypergraph V)
    {α : Type*} (f : V → α) : Prop :=
  ∀ e ∈ H.edges, e.card ≥ 2 → ∃ u ∈ e, ∃ v ∈ e, f u ≠ f v

/-- A hypergraph has chromatic number exactly $k$ if it can be properly colored
with $k$ colors but not with $k-1$ colors. -/
def Hypergraph.HasChromaticNumber {V : Type*} [DecidableEq V] (H : Hypergraph V)
    (k : ℕ) : Prop :=
  (∃ f : V → Fin k, H.IsProperColoring f) ∧
  ∀ f : V → Fin (k - 1), ¬H.IsProperColoring f

/-- The degree of a vertex $v$ in a hypergraph is the number of edges containing $v$. -/
def Hypergraph.degree {V : Type*} [DecidableEq V] (H : Hypergraph V) (v : V) : ℕ :=
  (H.edges.filter (fun e => v ∈ e)).card

/--
Does there exist an absolute constant $c > 0$ such that, for all $r \geq 2$,
in any $r$-uniform hypergraph with chromatic number $3$ there is a vertex
contained in at least $(1+c)^r$ many edges?

This was proved by Erdős and Lovász [ErLo75], who showed in particular
that there is a vertex contained in at least $2^{r-1}/(4r)$ many edges.
-/
@[category research solved, AMS 5]
theorem erdos_833 :
    answer(True) ↔
      ∃ c : ℝ, 0 < c ∧
        ∀ (r : ℕ), 2 ≤ r →
          ∀ (n : ℕ) (H : Hypergraph (Fin n)),
            H.IsUniform r → H.HasChromaticNumber 3 →
              ∃ v : Fin n, (H.degree v : ℝ) ≥ (1 + c) ^ r := by
  sorry

/--
Determine the largest integer $f(r)$ such that every $r$-uniform hypergraph
with chromatic number $3$ has a vertex contained in at least $f(r)$ edges.

This is a refinement of `erdos_833`: while the main problem asks whether $f(r)$
grows exponentially, this variant asks for the exact value. Known values are
$f(2) = 2$ and $f(3) = 3$. Erdős noted that $f(4)$ was unknown.
-/
@[category research open, AMS 5]
theorem erdos_833_variant :
    ∃ f : ℕ → ℕ,
      (∀ (r : ℕ), 2 ≤ r →
        (∀ (n : ℕ) (H : Hypergraph (Fin n)),
          H.IsUniform r → H.HasChromaticNumber 3 →
            ∃ v : Fin n, H.degree v ≥ f r) ∧
        (∀ m, (∀ (n : ℕ) (H : Hypergraph (Fin n)),
          H.IsUniform r → H.HasChromaticNumber 3 →
            ∃ v : Fin n, H.degree v ≥ m) → m ≤ f r)) ∧
      f 2 = 2 ∧ f 3 = 3 := by
  sorry

end Erdos833
