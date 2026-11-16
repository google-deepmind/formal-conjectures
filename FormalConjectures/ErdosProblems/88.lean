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
# Erdős Problem 88

*References:*
- [erdosproblems.com/88](https://www.erdosproblems.com/88)
- [Er92b] Erdős, Paul, *Some of my favourite problems in various branches of combinatorics*.
  Matematiche (Catania) (1992), 231-240.
- [Er95] Erdős, Paul, *Some of my favourite problems in number theory, combinatorics, and
  geometry*. Resenhas (1995), 165-186.
- [Er97d] Erdős, Paul, *Some recent problems and results in graph theory*. Discrete Math. (1997),
  81-85.
- [KSSS22] Kwan, M. and Sah, A. and Sauermann, L. and Sawhney, M., *Anticoncentration in Ramsey
  graphs and a proof of the Erdős-McKay conjecture*. Forum Math. Pi 11 (2023), e21.
  [arXiv:2208.02874](https://arxiv.org/abs/2208.02874)
-/

@[expose] public section

open Filter

namespace Erdos88

set_option linter.style.formal_proof_palomar false in
/--
For any $\epsilon>0$ there exists $\delta=\delta(\epsilon)>0$ such that if $G$ is a graph on $n$
vertices with no independent set or clique of size $\geq \epsilon\log n$ then $G$ contains an
induced subgraph with $m$ edges for all $m\leq \delta n^2$.

This was conjectured by Erdős and McKay and proved by Kwan, Sah, Sauermann, and Sawhney
[KSSS22]. Erdős' original formulation also assumed that $G$ has $\gg n^2$ edges. By an old result
of Erdős and Szemerédi this follows from the other condition, so it is omitted here.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos88.lean#L127"]
theorem erdos_88 :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      (G.cliqueNum : ℝ) < ε * Real.log n → (G.indepNum : ℝ) < ε * Real.log n →
        ∀ m : ℕ, (m : ℝ) ≤ δ * n ^ 2 →
          ∃ S : Finset (Fin n), (G.induce (S : Set (Fin n))).edgeSet.ncard = m := by
  sorry

/--
Erdős and McKay proved the statement of `erdos_88` with $\delta n^2$ replaced by
$\delta (\log n)^2$. Since $(\log n)^2 \leq n^2$, this weaker bound also follows from
`erdos_88`.
-/
@[category research solved, AMS 5]
theorem erdos_88.variants.erdos_mckay :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      (G.cliqueNum : ℝ) < ε * Real.log n → (G.indepNum : ℝ) < ε * Real.log n →
        ∀ m : ℕ, (m : ℝ) ≤ δ * Real.log n ^ 2 →
          ∃ S : Finset (Fin n), (G.induce (S : Set (Fin n))).edgeSet.ncard = m := by
  sorry

/--
Kwan, Sah, Sauermann, and Sawhney [KSSS22, Theorem 1.1] proved the following stronger statement.
Fix $C > 0$ and $\eta > 0$, and let $G$ be a graph on $n$ vertices with no independent set or
clique of size $\geq C \log_2 n$, where $n$ is sufficiently large with respect to $C$ and $\eta$.
Then for every integer $0 \leq m \leq (1 - \eta) e(G)$ there is an induced subgraph of $G$ with
exactly $m$ edges.
-/
@[category research solved, AMS 5]
theorem erdos_88.variants.kwan_sah_sauermann_sawhney :
    ∀ C > (0 : ℝ), ∀ η > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (G.cliqueNum : ℝ) < C * Real.logb 2 n → (G.indepNum : ℝ) < C * Real.logb 2 n →
        ∀ m : ℕ, (m : ℝ) ≤ (1 - η) * G.edgeSet.ncard →
          ∃ S : Finset (Fin n), (G.induce (S : Set (Fin n))).edgeSet.ncard = m := by
  sorry

end Erdos88
