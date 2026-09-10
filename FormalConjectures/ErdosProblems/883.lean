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

import FormalConjecturesUtil

/-!
# Erdős Problem 883

*References:*
- [erdosproblems.com/883](https://www.erdosproblems.com/883)
- [ErSa97] Erdős, P. and Sárközy, G. N., On cycles in the coprime graph of integers.
  Electron. J. Combin. (1997), Research Paper 8.
- [Sa99] Sárközy, G. N., Complete tripartite subgraphs in the coprime graph of integers.
  Discrete Math. (1999), 227-238.
-/

open Filter

namespace Erdos883

/--
The coprime graph on $\mathbb{N}$: two integers are joined by an edge if they are coprime.
-/
def coprimeGraph : SimpleGraph ℕ :=
  SimpleGraph.fromRel Nat.Coprime

/--
For $A\subseteq \{1,\ldots,n\}$ let $G(A)$ be the graph with vertex set $A$, where two
integers are joined by an edge if they are coprime.

Is it true that if
$$|A| > \lfloor n/2 \rfloor + \lfloor n/3 \rfloor - \lfloor n/6 \rfloor$$
then $G(A)$ contains all odd cycles of length $\leq n/3 + 1$?

A problem of Erdős and Sárközy [ErSa97].
-/
@[category research open, AMS 5 11]
theorem erdos_883.parts.i : answer(sorry) ↔
    ∀ (n : ℕ) (A : Finset ℕ),
      A ⊆ Finset.Icc 1 n →
      n / 2 + n / 3 - n / 6 < A.card →
      ∀ l : ℕ, Odd l → 3 ≤ l → l ≤ n / 3 + 1 →
        l ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  sorry

open scoped Classical in
/--
Is it true that, for every $\ell\geq 1$, if $n$ is sufficiently large and
$$|A| > \lfloor n/2\rfloor + \lfloor n/3\rfloor - \lfloor n/6\rfloor$$
then $G(A)$ must contain a complete $(1,\ell,\ell)$ tripartite graph on $2\ell+1$ vertices?

The second question was solved by Sárközy [Sa99], who proved this with
$\ell \gg \log n/\log\log n$.
-/
@[category research solved, AMS 5 11]
theorem erdos_883.parts.ii : answer(True) ↔
    ∀ l : ℕ, 1 ≤ l → ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 n →
      n / 2 + n / 3 - n / 6 < A.card →
      (SimpleGraph.completeMultipartiteGraph (fun i : Fin 3 ↦ Fin (![1, l, l] i))).IsContained
        (coprimeGraph.induce (A : Set ℕ)) := by
  sorry

end Erdos883
