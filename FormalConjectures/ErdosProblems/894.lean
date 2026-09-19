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
# Erdős Problem 894

*References:*
- [erdosproblems.com/894](https://www.erdosproblems.com/894)
- [Ka01] Katznelson, Y., *Chromatic numbers of Cayley graphs on $\mathbb{Z}$ and recurrence*.
  Combinatorica (2001), 211--219.
- [PeSc10] Peres, Yuval and Schlag, Wilhelm, *Two Erdős problems on lacunary sequences: chromatic
  number and Diophantine approximation*. Bull. Lond. Math. Soc. (2010), 295--300.
-/

@[expose] public section

namespace Erdos894

/- Formalization note: as in `erdos_464`, the lacunarity hypothesis is rendered by the house
predicate `IsLacunary` ($\exists c > 1$ with $c \cdot n_k < n_{k+1}$ for all sufficiently large
$k$); for a strictly increasing sequence of positive integers this is equivalent to the problem's
condition $n_{k+1} \geq (1+\epsilon) n_k$ for all $k$. -/

/--
Let $A=\{n_1<n_2<\cdots\}\subset \mathbb{N}$ be a lacunary sequence (so there exists some
$\epsilon>0$ with $n_{k+1}\geq (1+\epsilon)n_k$ for all $k$). Is it true that there must exist a
finite colouring of $\mathbb{N}$ with no monochromatic solutions to $a-b\in A$?

Asked by Erdős in 1987, according to Katznelson [Ka01]. In other words, does the Cayley graph
defined on $\mathbb{Z}$ by a lacunary sequence have a finite chromatic number?

Katznelson observed that a positive solution to the problem follows from the answer to
[464](https://www.erdosproblems.com/464), which yields an irrational $\theta$ and $\delta>0$
such that $\inf_k \| \theta n_k\|>\delta$. In particular, the solution to
[464](https://www.erdosproblems.com/464) implies the answer to this question is yes, with the
best known quantitative bound, due to Peres and Schlag [PeSc10], being that there is a colouring
with no solutions using at most $\ll \epsilon^{-1}\log(1/\epsilon)$ colours.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos894.lean#L310"]
theorem erdos_894 : answer(True) ↔
    ∀ n : ℕ → ℕ, StrictMono n → (∀ k, 0 < n k) → IsLacunary n →
      ∃ (r : ℕ) (c : ℕ → Fin r), ∀ b k, c (b + n k) ≠ c b := by
  sorry

end Erdos894
