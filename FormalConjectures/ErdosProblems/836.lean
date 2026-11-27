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
# Erdős Problem 836

*References:*
- [erdosproblems.com/836](https://www.erdosproblems.com/836)
- [ErLo75] Erdős, P. and Lovász, L., Problems and results on {$3$}-chromatic hypergraphs and some
  related questions. (1975), 609--627.
- [Pr26] Price, L., *A Linear Intersection Bound*. (2026).
-/

@[expose] public section

namespace Erdos836

open Filter Asymptotics

set_option linter.style.formal_proof_palomar false in
/--
Let $r\geq 2$ and let $G$ be an intersecting $r$-uniform hypergraph with chromatic number
$3$. Must $G$ contain $O(r^2)$ many vertices? Vertices are counted in the union of the edges,
so isolated vertices are excluded.

Alon has provided a counterexample to the first question: this hypergraph is intersecting,
its chromatic number is $3$, and it has $\asymp 4^r/\sqrt{r}$ many vertices.
-/
@[category research solved, question, AMS 5, formal_proof using lean4 at
  "https://github.com/linrock/math-proofs/blob/ad12db51383ed41ec8b6b54e0ffabfa828773d38/erdos-836/Solution.lean#L33"]
theorem erdos_836.parts.i :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
    ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
      H.IsUniform r → H.HasHypergraphChromaticNumber 3 → (H : Set (Finset (Fin n))).Intersecting →
        ((H.biUnion id).card : ℝ) ≤ C * (r : ℝ) ^ 2 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
In an intersecting $r$-uniform hypergraph with chromatic number $3$, must there be two
distinct edges which meet in $\gg r$ many vertices?
-/
@[category research solved, question, AMS 5, formal_proof using lean4 at
  "https://github.com/linrock/math-proofs/blob/ad12db51383ed41ec8b6b54e0ffabfa828773d38/erdos-836/Solution.lean#L41"]
theorem erdos_836.parts.ii :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 2 ≤ r →
    ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
      H.IsUniform r → H.HasHypergraphChromaticNumber 3 → (H : Set (Finset (Fin n))).Intersecting →
        ∃ e ∈ H, ∃ f ∈ H, e ≠ f ∧ c * r ≤ ((e ∩ f).card : ℝ) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
Let $t \geq 2$. If $H$ is a finite $r$-uniform hypergraph which is intersecting and not
$2$-colourable, and any two distinct edges of $H$ share at most $t$ vertices, then $r \leq 2t$.

The problem page notes that in the Fano plane no two edges meet in $r - 1$ vertices, and asks for
other examples. Erdős and Lovász [ErLo75] already gave such examples for every $r = 3^k$. This
variant is a bound around that question, not an answer to it.

Price [Pr26] showed $r \leq 2t + 1$ for every $t$, and the Fano plane ($r = 3$, $t = 1$) attains
it. The variant says that equality needs $t = 1$. Fix an edge $A$ and a proper $2$-colouring of
the other edges in which $A$ is red and the blue class $B$ is as small as possible. For each
$y \in A$ there is an edge $F_y$ with $F_y \cap A = \{y\}$ and $F_y \setminus \{y\} \subseteq B$.
Price's double count shows that if $r = 2t + 1$, then every vertex of $B$ lies in exactly $t + 1$
of the sets $F_y$. So $(t + 1)|B| = r(r - 1) = 2t(2t + 1)$, and $t + 1$ divides $2$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/mnn31/erdos-lean/blob/f21dab0a72b1c833d3dc4a2df41e6ef2c66dcece/ErdosLean/Erdos836.lean"]
theorem erdos_836.variants.r_le_two_mul_of_inter_le {V : Type*} [DecidableEq V] (r t : ℕ)
    (ht : 2 ≤ t) (H : Finset (Finset V)) (hU : H.IsUniform r)
    (hI : (H : Set (Finset V)).Intersecting) (hC : ¬ H.HypergraphColorable 2)
    (hT : (H : Set (Finset V)).Pairwise fun e f ↦ (e ∩ f).card ≤ t) :
    r ≤ 2 * t := by
  sorry

end Erdos836
