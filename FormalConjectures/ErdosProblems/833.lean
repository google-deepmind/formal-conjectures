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
# Erdős Problem 833

*References:*
- [erdosproblems.com/833](https://www.erdosproblems.com/833)
- [ErLo75] Erdős, P. and Lovász, L., Problems and results on {$3$}-chromatic hypergraphs and some
  related questions. (1975), 609--627.
-/

@[expose] public section

namespace Erdos833

open Filter Asymptotics

/--
Does there exist an absolute constant $c>0$ such that, for all $r\geq 2$, in any $r$-uniform
hypergraph with chromatic number $3$ there is a vertex contained in at least $(1+c)^r$ many edges?

This was solved by Erdős and Lovász [ErLo75], who proved in particular that there is a vertex
contained in at least $\frac{2^{r-1}}{4r}$ many edges.
-/
@[category research solved, question, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos833.lean#L671"]
theorem erdos_833 :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 2 ≤ r →
    ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
      H.IsUniform r → H.HasHypergraphChromaticNumber 3 →
        ∃ v : Fin n, (1 + c) ^ r ≤ (H.hypergraphDegree v : ℝ) := by
  sorry

/-- Erdős and Lovász prove that a vertex is contained in at least $2^{r-1}/(4r)$ edges. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos833.lean#L555"]
theorem erdos_833.variants.erdos_lovasz : ∀ r : ℕ, 2 ≤ r →
    ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
      H.IsUniform r → H.HasHypergraphChromaticNumber 3 →
      ∃ v : Fin n, (2 : ℝ) ^ (r - 1) / (4 * r) ≤ H.hypergraphDegree v := by
  sorry

/-- The largest guaranteed degree in an `r`-uniform hypergraph of chromatic number three.
The known values are `f 2 = 2` and `f 3 = 3`; the source asks for the value of `f 4`. -/
noncomputable def f (r : ℕ) : ℕ :=
  sSup {d | ∀ (n : ℕ) (H : Finset (Finset (Fin n))), H.IsUniform r →
    H.HasHypergraphChromaticNumber 3 → ∃ v : Fin n, d ≤ H.hypergraphDegree v}

/-- The first two known values of the largest guaranteed degree. -/
@[category research solved, AMS 5]
theorem erdos_833.variants.small_values : f 2 = 2 ∧ f 3 = 3 := by
  sorry

end Erdos833
