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
# Erdős Problem 1079

*References:*
- [erdosproblems.com/1079](https://www.erdosproblems.com/1079)
- [Er75] Erdős, P., *Some recent progress on extremal problems in graph theory*. Congr. Numer.
  (1975), 3-14.
- [BoTh81] Bollobás, Béla and Thomason, Andrew, *Dense neighbourhoods and Turán's theorem*. J.
  Combin. Theory Ser. B (1981), 111--114.
- [Bo83b] Bondy, J. A., *Large dense neighbourhoods and Turán's theorem*. J. Combin. Theory Ser.
  B (1983), 109--111.
-/

@[expose] public section

open SimpleGraph

namespace Erdos1079

open scoped Classical in
/--
Let $r\geq 4$. If $G$ is a graph on $n$ vertices with at least $\mathrm{ex}(n;K_r)$ edges then
must $G$ contain a vertex with degree $d\gg_r n$ whose neighbourhood contains at least
$\mathrm{ex}(d;K_{r-1})$ edges?

As Erdős [Er75] says 'if true this would be a nice generalisation of Turán's theorem'. This is
true (unless $G$ it itself the Turán graph), and was proved by Bollobás and Thomason [BoTh81].
Bondy [Bo83b] showed that if $G$ has $>\mathrm{ex}(n;K_r)$ edges then the corresponding vertex
can be chosen to be of maximum degree in $G$.

The number of edges in the neighbourhood of $v$ is the number of edges of $G$ both of whose
endpoints are adjacent to $v$. Graphs on a single vertex are excluded, since there every degree
is $0$.
-/
@[category research solved, AMS 5]
theorem erdos_1079 : answer(True) ↔ ∀ r : ℕ, 4 ≤ r → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
    ∀ G : SimpleGraph (Fin n), extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard →
      ∃ v : Fin n, c * n ≤ G.degree v ∧
        extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) ≤
          {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard := by
  sorry

/--
Bondy's strengthening [Bo83b]: if $G$ has more than $\mathrm{ex}(n;K_r)$ edges then some vertex
$v$ of maximum degree has $d(v) \geq n/2$ and its neighbourhood contains more than
$\mathrm{ex}(d(v);K_{r-1})$ edges.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1079.lean#L424"]
theorem erdos_1079.variants.bondy (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard := by
  sorry

end Erdos1079
