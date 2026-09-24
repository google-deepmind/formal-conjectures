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
# Erdős Problem 720

*References:*
- [erdosproblems.com/720](https://www.erdosproblems.com/720)
- [Er76c] Erdős, P., _Some recent problems and results in graph theory, combinatorics and number
  theory_. Proceedings of the Seventh Southeastern Conference on Combinatorics, Graph Theory,
  and Computing (Louisiana State Univ., Baton Rouge, La., 1976) (1976), 3-14.
- [EFRS78b] Erdős, P. and Faudree, R. J. and Rousseau, C. C. and Schelp, R. H., _The size Ramsey
  number_. Period. Math. Hungar. (1978), 145-161.
- [Er78] Erdős, Paul, _Problems and results in combinatorial analysis and combinatorial number
  theory_. Proceedings of the Ninth Southeastern Conference on Combinatorics, Graph Theory, and
  Computing (Florida Atlantic Univ., Boca Raton, Fla., 1978) (1978), 29-40.
- [Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_.
  Combinatorica (1981), 25-42.
- [Er82e] Erdős, Paul, _Some of my favourite problems which recently have been solved_. (1982),
  59--79.
- [Be83b] Beck, József, _On size Ramsey number of paths, trees, and circuits. I_. J. Graph
  Theory (1983), 115-129.
-/

@[expose] public section

open Filter SimpleGraph

namespace Erdos720

/-- The size Ramsey number $\hat{R}(G)$ of `G`: the least number of edges of a graph which is
Ramsey for `G`. -/
noncomputable abbrev sizeRamseyNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sizeRamsey G G

/--
Let $\hat{R}(G)$ denote the size Ramsey number, the minimal number of edges $m$ such that there
is a graph $H$ with $m$ edges such that in any $2$-colouring of the edges of $H$ there is a
monochromatic copy of $G$.

Is it true that, if $P_n$ is the path of length $n$, then $\hat{R}(P_n)/n\to \infty$?

The answer is no: Beck [Be83b] proved that in fact $\hat{R}(P_n)\ll n$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos720.lean#L39"]
theorem erdos_720.parts.i : answer(False) ↔
    Tendsto (fun n : ℕ ↦ (sizeRamseyNumber (pathGraph (n + 1)) : ℝ) / n) atTop atTop := by
  sorry

/--
Is it true that, if $P_n$ is the path of length $n$, then $\hat{R}(P_n)/n^2 \to 0$?

The answer is yes: Beck [Be83b] proved that in fact $\hat{R}(P_n)\ll n$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos720.lean#L39"]
theorem erdos_720.parts.ii : answer(True) ↔
    Tendsto (fun n : ℕ ↦ (sizeRamseyNumber (pathGraph (n + 1)) : ℝ) / (n : ℝ) ^ 2) atTop
      (nhds 0) := by
  sorry

/--
Is it true that, if $C_n$ is the cycle with $n$ edges, then $\hat{R}(C_n) =o(n^2)$?

The answer is yes: Beck [Be83b] proved that in fact $\hat{R}(C_n)\ll n$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos720.lean#L39"]
theorem erdos_720.parts.iii : answer(True) ↔
    Tendsto (fun n : ℕ ↦ (sizeRamseyNumber (cycleGraph n) : ℝ) / (n : ℝ) ^ 2) atTop
      (nhds 0) := by
  sorry

/-- Beck [Be83b] proved that $\hat{R}(P_n)\ll n$ and $\hat{R}(C_n)\ll n$. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos720.lean#L39"]
theorem erdos_720.variants.beck :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop,
      sizeRamseyNumber (pathGraph (n + 1)) ≤ C * n ∧
        sizeRamseyNumber (cycleGraph n) ≤ C * n := by
  sorry

end Erdos720
