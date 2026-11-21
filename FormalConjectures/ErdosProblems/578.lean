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
# Erdős Problem 578

*References:*
- [erdosproblems.com/578](https://www.erdosproblems.com/578)
- [Ri00] Riordan, Oliver, *Spanning subgraphs of random graphs*.
  Combin. Probab. Comput. (2000), 125-148. [DOI](https://doi.org/10.1017/S0963548399004150)
-/

@[expose] public section

open Filter SimpleGraph

namespace Erdos578

/--
If $G$ is a random graph on $2^d$ vertices, including each edge with probability $1/2$, then $G$
almost surely contains a copy of $Q_d$ (the $d$-dimensional hypercube with $2^d$ vertices and
$d2^{d-1}$ many edges).

A conjecture of Erdős and Bollobás. Solved by Riordan [Ri00], who in fact proved this with any
edge-probability $>1/4$.

Here almost surely means that the probability tends to $1$ as $d\to\infty$.
-/
@[category research solved, AMS 5 60]
theorem erdos_578 :
    Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) ⟨1 / 2, by norm_num⟩
        {G | (hypercube d).IsContained G}) atTop (nhds 1) := by
  sorry

/-- For every fixed edge-probability $p>1/4$, the probability that a random graph on $2^d$
vertices contains a copy of $Q_d$ tends to $1$ as $d\to\infty$. Proved by Riordan [Ri00]. -/
@[category research solved, AMS 5 60]
theorem erdos_578.variants.riordan (p : unitInterval) (hp : (1 : ℝ) / 4 < p) :
    Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1) := by
  sorry

end Erdos578
