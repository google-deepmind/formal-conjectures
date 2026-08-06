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
# Erdős Problem 45

*References:*
- [erdosproblems.com/45](https://www.erdosproblems.com/45)
- [Er95] Erdős, Paul, *Some of my favourite problems in number theory, combinatorics, and geometry*.
  Resenhas (1995), 165-186.
- [Er96b] Erdős, Paul, *Some problems I presented or planned to present in my short talk*. Analytic
  number theory, Vol. 1 (Allerton Park, IL, 1995) (1996), 333-335.
- [Cr03] Croot, III, Ernest S., *On a coloring conjecture about unit fractions*. Ann. of Math. (2)
  (2003), 545-556.
- [Gu04] Guy, Richard K., *Unsolved problems in number theory*. (2004), xviii+437.
-/

namespace Erdos45

/--
Let $k\geq 2$. Is there an integer $n_k$ such that, if $D=\{ 1<d<n_k : d\mid n_k\}$, then for any
$k$-colouring of $D$ there is a monochromatic subset $D'\subseteq D$ such that
$\sum_{d\in D'}\frac{1}{d}=1$?

This follows from the colouring result of Croot [Cr03]. Croot's result allows for
$n_k \leq e^{C^k}$ for some constant $C>1$ (simply taking $n_k$ to be the lowest common multiple of
some interval $[1,C^k]$). Sawhney has observed that there is also a doubly exponential lower bound,
and hence this bound is essentially sharp.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos45.lean"]
theorem erdos_45 : answer(True) ↔
    ∀ k : ℕ, 2 ≤ k → ∃ n : ℕ, ∀ colouring : ℕ → Fin k,
      ∃ colour : Fin k, ∃ D' ⊆ {d ∈ n.divisors | 1 < d ∧ d < n},
        (∀ d ∈ D', colouring d = colour) ∧ D'.reciprocalSum = 1 := by
  sorry

end Erdos45
