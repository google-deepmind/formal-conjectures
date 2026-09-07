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
- [ErSa97] Erdős, P. and Sárközy, A., On the number of prime factors of integers.
  Acta Sci. Math. (Szeged) (1997).
- [Sa99] Sárközy, A., On the coprime graph. Discrete Math. (1999).
-/

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
theorem erdos_883 : answer(sorry) ↔
    ∀ (n : ℕ) (A : Finset ℕ),
      A ⊆ Finset.Icc 1 n →
      n / 2 + n / 3 - n / 6 < A.card →
      ∀ l : ℕ, Odd l → 3 ≤ l → l ≤ n / 3 + 1 →
        l ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  sorry

-- TODO: Add variants of the problem.

end Erdos883
