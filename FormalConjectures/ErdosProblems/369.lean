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
# Erdős Problem 369

*References:*
- [erdosproblems.com/369](https://www.erdosproblems.com/369)
- [BaWo98] Balog, Antal and Wooley, Trevor D., *On strings of consecutive integers with no large
  prime factors*. J. Austral. Math. Soc. Ser. A (1998), 266-276.
-/

open Filter

namespace Erdos369

/--
Let $\epsilon>0$ and $k\geq 2$. Is it true that, for all sufficiently large $n$, there is a
sequence of $k$ consecutive integers in $\{1,\ldots,n\}$ all of which are $n^\epsilon$-smooth?

The problem is trivially true as written (simply taking $\{1,\ldots,k\}$ and $n>k^{1/\epsilon}$).
There are (at least) two possible variants which are non-trivial, and it is not clear which
Erdős and Graham meant. We formalize the second: each $m\in P$ (where $P$ is the sequence of $k$
consecutive integers sought for) must be in $[n/2,n]$. In this case a positive answer also
follows directly from the result of Balog and Wooley [BaWo98] for infinitely many $n$. Proving
this is true for all large $n$ does not follow immediately from [BaWo98], but can be deduced
using a similar construction, as shown by SkyYang.

The statement below takes the $k$ consecutive integers as $a+1,\ldots,a+k$ with
$\lfloor n/2\rfloor\leq a+1$ and $a+k\leq n$, and renders "$n^\epsilon$-smooth" as: every prime
factor is at most $n^\epsilon$.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos369.lean"]
theorem erdos_369 : answer(True) ↔
    ∀ (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k),
      ∀ᶠ (n : ℕ) in atTop, ∃ a : ℕ, n / 2 ≤ a + 1 ∧ a + k ≤ n ∧
        ∀ j < k, ∀ p ∈ (a + 1 + j).primeFactors, (p : ℝ) ≤ (n : ℝ) ^ ε := by
  sorry

end Erdos369
