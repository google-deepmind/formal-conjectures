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
# Erdős Problem 136

*References:*
- [erdosproblems.com/136](https://www.erdosproblems.com/136)
- [Er97b] Erdős, Paul, *Some old and new problems in various branches of combinatorics*. Discrete
  Math. (1997), 227-231.
- [BCDP22] Bennett, P. and Cushman, R. and Dudek, A. and Pralat, P., *The Erdős-Gyárfás function
  $f(n,4,5)=\frac{5}{6}n+o(n)$ - so Gyárfás was right*. arXiv:2207.02920 (2022).
- [JoMu22] Joos, F. and Mubayi, D., *Ramsey theory constructions from hypergraph matchings*.
  arXiv:2208.12563 (2022).
-/

@[expose] public section

open Filter
open scoped Topology

namespace Erdos136

/-- An edge colouring of `K_n` with `k` colours is a `(4, 5)`-colouring if the six edges of every
copy of `K_4` receive at least five distinct colours. -/
def Is45Coloring {n k : ℕ} (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)) : Prop :=
  open scoped Classical in
  ∀ v : Fin 4 ↪ Fin n, 5 ≤ (Finset.univ.image (C.pullback v)).card

/-- `K_n` admits a `(4, 5)`-colouring with `k` colours. -/
def Colorable (n k : ℕ) : Prop :=
  ∃ C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k), Is45Coloring C

/-- `f n` is the least number of colours in a `(4, 5)`-colouring of `K_n`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k | Colorable n k}

/--
Let $f(n)$ be the smallest number of colours required to colour the edges of $K_n$ such that every
$K_4$ contains at least $5$ colours. Determine the size of $f(n)$.

Asked by Erdős and Gyárfás [Er97b], who proved $\frac56 (n - 1) < f(n) < n$ and $f(9) = 8$; Erdős
believed that the upper bound is closer to the truth. In fact $f(n) \sim \frac56 n$, as shown by
Bennett, Cushman, Dudek and Pralat [BCDP22]; Joos and Mubayi [JoMu22] found a shorter proof.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos136.lean#L49"]
theorem erdos_136 : Tendsto (fun n : ℕ ↦ (f n : ℝ) / (n : ℝ)) atTop (𝓝 (5 / 6 : ℝ)) := by
  sorry

end Erdos136
