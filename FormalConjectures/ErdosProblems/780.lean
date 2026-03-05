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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 780

*Reference:* [erdosproblems.com/780](https://www.erdosproblems.com/780)

Suppose $n \geq kr + (t-1)(k-1)$ and the edges of the complete $r$-uniform hypergraph
on $n$ vertices are $t$-coloured. Prove that some colour class must contain $k$ pairwise
disjoint edges.

In other words, this problem asks to determine the chromatic number of the Kneser
graph. The bound is best possible.

When $k = 2$ this was conjectured by Kneser and proved by Lovász [Lo78].
The general case was proved by Alon, Frankl, and Lovász [AFL86].

[Lo78] Lovász, L., _Kneser's conjecture, chromatic number, and homotopy_. J. Combin.
Theory Ser. A **25** (1978), 319--324.

[AFL86] Alon, N., Frankl, P., and Lovász, L., _The chromatic number of Kneser
hypergraphs_. Trans. Amer. Math. Soc. **298** (1986), 359--370.
-/

namespace Erdos780

/--
**Erdős Problem 780** (PROVED — Alon, Frankl, Lovász [AFL86]):

If $n \geq kr + (t-1)(k-1)$ and the edges of the complete $r$-uniform hypergraph
on $n$ vertices are $t$-coloured, then some colour class contains $k$ pairwise
disjoint edges.

Here an "edge" of the complete $r$-uniform hypergraph on $\text{Fin}\; n$ is an
$r$-element subset of $\text{Fin}\; n$, and "$t$-coloured" means we have a colouring
function from these edges to $\text{Fin}\; t$.
-/
@[category research solved, AMS 5]
theorem erdos_780
    (k r t : ℕ) (hk : k ≥ 1) (hr : r ≥ 1) (ht : t ≥ 1)
    (n : ℕ) (hn : n ≥ k * r + (t - 1) * (k - 1))
    (c : {s : Finset (Fin n) // s.card = r} → Fin t) :
    ∃ (i : Fin t) (edges : Fin k → {s : Finset (Fin n) // s.card = r}),
      (∀ j, c (edges j) = i) ∧
      (∀ j₁ j₂, j₁ ≠ j₂ → Disjoint (edges j₁).val (edges j₂).val) := by
  sorry

end Erdos780
