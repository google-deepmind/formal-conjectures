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
# Erdős Problem 802

*References:*
- [erdosproblems.com/802](https://www.erdosproblems.com/802)
- [AEKS81] Ajtai, M. and Erdős, P. and Komlós, J. and Szemerédi, E., *On Turán's theorem for
  sparse graphs*. Combinatorica (1981), 313-317.
- [AKS80] Ajtai, Miklós and Komlós, János and Szemerédi, Endre, *A note on Ramsey numbers*.
  J. Combin. Theory Ser. A (1980), 354-360.
- [Al96b] Alon, Noga, *Independence numbers of locally sparse graphs and a Ramsey type problem*.
  Random Structures Algorithms (1996), 271-278.
- [Sh95] Shearer, James B., *On the independence number of sparse graphs*. Random Structures
  Algorithms (1995), 269-271.
-/

@[expose] public section

open Real

namespace Erdos802

open scoped Classical in
/--
Is it true that any $K_r$-free graph on $n$ vertices with average degree $t$ contains an
independent set on
$$\gg_r \frac{\log t}{t}n$$
many vertices?

A conjecture of Ajtai, Erdős, Komlós, and Szemerédi [AEKS81].
-/
@[category research solved, question, AMS 5,
  formal_proof using lean4 at
    "https://github.com/AItoBit/formal-conjectures/blob/8cf6eb5d0204f9590118597b40185cc8d19db587/proofs/erdos802/Bridge802.lean#L120"]
theorem erdos_802 : ∀ r : ℕ, ∃ c > (0 : ℝ), ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    G.CliqueFree r →
      c * (log G.averageDegree / G.averageDegree) * n ≤ G.indepNum := by
  sorry

open scoped Classical in
/--
Ajtai, Erdős, Komlós, and Szemerédi [AEKS81] proved that any $K_r$-free graph on $n$ vertices
with average degree $t$ contains an independent set on
$$\gg_r \frac{\log\log(t+1)}{t}n$$
many vertices.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/AItoBit/formal-conjectures/blob/8cf6eb5d0204f9590118597b40185cc8d19db587/proofs/erdos802/Results802.lean#L14"]
theorem erdos_802.variants.aeks : ∀ r : ℕ, ∃ c > (0 : ℝ), ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    G.CliqueFree r →
      c * (log (log (G.averageDegree + 1)) / G.averageDegree) * n ≤ G.indepNum := by
  sorry

open scoped Classical in
/--
Shearer [Sh95] proved that any $K_r$-free graph on $n$ vertices with average degree $t$ contains
an independent set on
$$\gg_r \frac{\log t}{\log\log(t+1)t}n$$
many vertices.

We assume $t \geq 2$. For $t + 1$ slightly larger than $e$ the factor $\log\log(t+1)$ is close
to $0$, so the bound blows up and the statement is false without such a restriction.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/AItoBit/formal-conjectures/blob/8cf6eb5d0204f9590118597b40185cc8d19db587/proofs/erdos802/Results802.lean#L21"]
theorem erdos_802.variants.shearer : ∀ r : ℕ, ∃ c > (0 : ℝ), ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    G.CliqueFree r → 2 ≤ G.averageDegree →
      c * (log G.averageDegree / (log (log (G.averageDegree + 1)) * G.averageDegree)) * n ≤
        G.indepNum := by
  sorry

open scoped Classical in
/--
Ajtai, Komlós, and Szemerédi [AKS80] proved the conjectured bound when $r = 3$: any
triangle-free graph on $n$ vertices with average degree $t$ contains an independent set on
$$\gg \frac{\log t}{t}n$$
many vertices.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/AItoBit/formal-conjectures/blob/8cf6eb5d0204f9590118597b40185cc8d19db587/proofs/erdos802/Results802.lean#L29"]
theorem erdos_802.variants.r_eq_three : ∃ c > (0 : ℝ), ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    G.CliqueFree 3 →
      c * (log G.averageDegree / G.averageDegree) * n ≤ G.indepNum := by
  sorry

open scoped Classical in
/--
Alon [Al96b] proved the conjectured bound under the stronger assumption that the induced graph
on every vertex neighbourhood has chromatic number $\leq r - 2$.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/AItoBit/formal-conjectures/blob/8cf6eb5d0204f9590118597b40185cc8d19db587/proofs/erdos802/Results802.lean#L36"]
theorem erdos_802.variants.alon : ∀ r : ℕ, ∃ c > (0 : ℝ), ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    (∀ v, (G.induce (G.neighborSet v)).Colorable (r - 2)) →
      c * (log G.averageDegree / G.averageDegree) * n ≤ G.indepNum := by
  sorry

end Erdos802
