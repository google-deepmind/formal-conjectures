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
# Erdős Problem 163

*References:*
- [erdosproblems.com/163](https://www.erdosproblems.com/163)
- [BuEr75] Burr, S. A. and Erdős, P., On the Ramsey number of graphs with small degree-ratio.
  Colloq. Math. Soc. János Bolyai (1975).
- [Le17] Lee, C., Ramsey numbers of degenerate graphs. Ann. of Math. (2) 185 (2017), 791-829.
-/

@[expose] public section

namespace Erdos163

/--
The Burr-Erdős conjecture: For any $d\geq 1$ if $H$ is a graph such that every subgraph
contains a vertex of degree at most $d$ then
$$R(H)\ll_d n.$$

Solved by Lee [Le17], who proved that $R(H) \leq 2^{2^{O(d)}}n$.

This problem is #9 in Ramsey Theory in the graphs problem collection.

The linked formal proof (Codex and GPT-5.6 Sol) gives, for graphs `H` on `Fin n`, a natural
constant `C ≥ 1` with `RamseyFor H (C * n)` (every red/blue colouring of `K_{C n}` contains a
monochromatic copy of `H`); transporting along `Fintype.equivFin` gives the statement below.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos163.lean#L53"]
theorem erdos_163 : answer(True) ↔
    ∀ (d : ℕ), 1 ≤ d →
      ∃ C > (0 : ℝ), ∀ (V : Type) [Fintype V] (H : SimpleGraph V),
        H.IsDegenerate d →
        (SimpleGraph.diagonalGraphRamsey H : ℝ) ≤ C * Fintype.card V := by
  sorry

-- TODO: Add variants of the problem.

end Erdos163
