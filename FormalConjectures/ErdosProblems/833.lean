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

/-!
# Erdős Problem 833

*References:*
- [erdosproblems.com/833](https://www.erdosproblems.com/833)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Er74d] Erdős, Paul, *Unsolved Problems*. (1974), 278-297.
- [ErLo75] Erdős, P. and Lovász, L., *Problems and results on $3$-chromatic hypergraphs and some
  related questions*. (1975), 609-627.
-/

@[expose] public section

namespace Erdos833

variable {V : Type*}

/-- A colouring `c` of the vertices is proper for the hypergraph `H` if no edge is
monochromatic. -/
def IsProperColoring (H : Finset (Finset V)) {κ : Type*} (c : V → κ) : Prop :=
  ∀ e ∈ H, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

/-- The hypergraph `H` has chromatic number `k`: it has a proper colouring with `k` colours but
none with fewer. -/
def HasChromaticNumber (H : Finset (Finset V)) (k : ℕ) : Prop :=
  (∃ c : V → Fin k, IsProperColoring H c) ∧ ∀ q < k, ¬ ∃ c : V → Fin q, IsProperColoring H c

open scoped Classical in
/--
Does there exist an absolute constant $c>0$ such that, for all $r\geq 2$, in any $r$-uniform
hypergraph with chromatic number $3$ there is a vertex contained in at least $(1+c)^r$ many
edges?

In general, determine the largest integer $f(r)$ such that every $r$-uniform hypergraph with
chromatic number $3$ has a vertex contained in at least $f(r)$ many edges. It is easy to see that
$f(2)=2$ and $f(3)=3$. Erdős did not know the value of $f(4)$.

This was solved by Erdős and Lovász [ErLo75], who proved in particular that there is a vertex
contained in at least $\frac{2^{r-1}}{4r}$ many edges.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos833.lean#L671"]
theorem erdos_833 : answer(True) ↔ ∃ c : ℝ, 0 < c ∧
    ∀ (V : Type) [Fintype V] (r : ℕ) (H : Finset (Finset V)), 2 ≤ r →
      (∀ e ∈ H, e.card = r) → HasChromaticNumber H 3 →
        ∃ v : V, (1 + c) ^ r ≤ (H.filter (v ∈ ·)).card := by
  sorry

open scoped Classical in
/--
Erdős and Lovász [ErLo75] proved that in any $r$-uniform hypergraph with chromatic number $3$
there is a vertex contained in at least $\frac{2^{r-1}}{4r}$ many edges.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos833.lean#L555"]
theorem erdos_833.variants.erdos_lovasz :
    ∀ (V : Type) [Fintype V] (r : ℕ) (H : Finset (Finset V)), 2 ≤ r →
      (∀ e ∈ H, e.card = r) → HasChromaticNumber H 3 →
        ∃ v : V, (2 : ℝ) ^ (r - 1) / (4 * r) ≤ (H.filter (v ∈ ·)).card := by
  sorry

open scoped Classical in
/--
`f r` is the largest integer such that every $r$-uniform hypergraph with chromatic number $3$ has
a vertex contained in at least `f r` many edges.
-/
noncomputable def f (r : ℕ) : ℕ :=
  sSup {m | ∀ (V : Type) [Fintype V] (H : Finset (Finset V)), (∀ e ∈ H, e.card = r) →
    HasChromaticNumber H 3 → ∃ v : V, m ≤ (H.filter (v ∈ ·)).card}

/-- It is easy to see that $f(2)=2$ and $f(3)=3$. -/
@[category research solved, AMS 5]
theorem erdos_833.variants.small_values : f 2 = 2 ∧ f 3 = 3 := by
  sorry

/-- Erdős did not know the value of $f(4)$. -/
@[category research open, AMS 5]
theorem erdos_833.variants.four : f 4 = answer(sorry) := by
  sorry

end Erdos833
