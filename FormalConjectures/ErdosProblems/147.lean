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
# Erdős Problem 147

*References:*
- [erdosproblems.com/147](https://www.erdosproblems.com/147)
- [ErSi84] Erdős, P. and Simonovits, M., *Cube-supersaturated graphs and related problems*.
  Progress in graph theory (Waterloo, Ont., 1982) (1984), 203-218.
- [Er93] Erdős, Paul, *Some of my favorite solved and unsolved problems in graph theory*.
  Quaestiones Math. (1993), 333-350.
- [Er97c] Erdős, Paul, *Some of my favorite problems and results*. The mathematics of Paul Erdős,
  I (1997), 47-67.
- [Ja23] Janzer, Oliver, *Rainbow Turán number of even cycles, repeated patterns and blow-ups of
  cycles*. Israel J. Math. (2023), 813--840.
- [Ja23b] Janzer, Oliver, *Disproof of a conjecture of Erdős and Simonovits on the Turán number
  of graphs with minimum degree 3*. Int. Math. Res. Not. IMRN (2023), 8478--8494.
-/

@[expose] public section

open Filter Asymptotics SimpleGraph

namespace Erdos147

/--
If $H$ is bipartite with minimum degree $r$ then there exists $\epsilon=\epsilon(H)>0$ such that
$$\mathrm{ex}(n;H) \gg n^{2-\frac{1}{r-1}+\epsilon}.$$

Conjectured by Erdős and Simonovits [ErSi84]. A probabilistic argument shows that there exists
some $\epsilon=\epsilon(H)>0$ such that $\mathrm{ex}(n;H) \gg n^{2-\frac{2}{r}+\epsilon}$.

This conjecture was disproved by Janzer [Ja23] for even $r\geq 4$. The case $r=3$ was disproved
by Janzer [Ja23b], who constructed, for any $\epsilon>0$, a $3$-regular bipartite graph $H$ such
that $\mathrm{ex}(n;H)\ll n^{\frac{4}{3}+\epsilon}$.

In [Ja23] Janzer conjectures that the above lower bound is sharp, in that for any $r\geq 3$ and
$\epsilon>0$ there exists an $r$-regular graph $H$ such that
$\mathrm{ex}(n;H) \ll n^{2-\frac{2}{r}+\epsilon}$. Janzer's result proves this for even
$r\geq 4$.

See also [113](https://www.erdosproblems.com/113), [146](https://www.erdosproblems.com/146), and
[714](https://www.erdosproblems.com/714).

The conjecture is stated for minimum degree $r \geq 2$ (for $r = 1$ the exponent
$2 - \frac{1}{r-1}$ is not meaningful).
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos147.lean#L799"]
theorem erdos_147 : answer(False) ↔
    ∀ (V : Type) [Fintype V] [Nonempty V] (H : SimpleGraph V) [DecidableRel H.Adj],
      H.IsBipartite → 2 ≤ H.minDegree → ∃ ε : ℝ, 0 < ε ∧
        (fun n : ℕ => (n : ℝ) ^ (2 - 1 / ((H.minDegree : ℝ) - 1) + ε)) =O[atTop]
          fun n : ℕ => (extremalNumber n H : ℝ) := by
  sorry

open scoped Classical in
/--
Janzer [Ja23] disproved the conjecture for even $r\geq 4$: for any even $r \geq 4$ and
$\epsilon>0$ there exists a nonempty $r$-regular bipartite graph $H$ such that
$\mathrm{ex}(n;H) \ll n^{2-\frac{2}{r}+\epsilon}$.
-/
@[category research solved, AMS 5]
theorem erdos_147.variants.janzer_even (r : ℕ) (hr : 4 ≤ r) (heven : Even r) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsBipartite ∧ H.IsRegularOfDegree r ∧
      (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (2 - 2 / (r : ℝ) + ε) := by
  sorry

open scoped Classical in
/--
Janzer [Ja23b] constructed, for any $\epsilon>0$, a nonempty $3$-regular bipartite graph $H$
such that $\mathrm{ex}(n;H)\ll n^{\frac{4}{3}+\epsilon}$.
-/
@[category research solved, AMS 5]
theorem erdos_147.variants.cubic (ε : ℝ) (hε : 0 < ε) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsBipartite ∧ H.IsRegularOfDegree 3 ∧
      (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (4 / 3 + ε : ℝ) := by
  sorry

open scoped Classical in
/--
Janzer [Ja23] conjectures that for any $r\geq 3$ and $\epsilon>0$ there exists a nonempty
$r$-regular graph $H$ such that $\mathrm{ex}(n;H) \ll n^{2-\frac{2}{r}+\epsilon}$.
-/
@[category research open, AMS 5]
theorem erdos_147.variants.janzer_conjecture : answer(sorry) ↔ ∀ r : ℕ, 3 ≤ r → ∀ ε : ℝ, 0 < ε →
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsRegularOfDegree r ∧
      (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (2 - 2 / (r : ℝ) + ε) := by
  sorry

end Erdos147
