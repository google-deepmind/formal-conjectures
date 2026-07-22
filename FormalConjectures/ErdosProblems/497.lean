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

import FormalConjectures.Wikipedia.DedekindNumber
import FormalConjecturesUtil

/-!
# Erdős Problem 497

*References:*
- [erdosproblems.com/497](https://www.erdosproblems.com/497)
- [Er61] Erdős, Paul, *Some unsolved problems*. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221-254.
- [Kl69] Kleitman, Daniel, *On Dedekind's problem: The number of monotone Boolean functions*.
  Proc. Amer. Math. Soc. (1969), 677-682.
-/

open Filter

namespace Erdos497

/--
How many antichains in $[n]$ are there? That is, how many families of subsets of $[n]$ are
there such that, if $\mathcal{F}$ is such a family and $A,B\in \mathcal{F}$, then
$A\not\subseteq B$?

Sperner's theorem states that $\lvert \mathcal{F}\rvert \leq \binom{n}{\lfloor n/2\rfloor}$.
This is also known as Dedekind's problem. Resolved by Kleitman [Kl69], who proved that the
number of such families is
\[2^{(1+o(1))\binom{n}{\lfloor n/2\rfloor}}.\]
-/
@[category research solved, AMS 5 6,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos497.lean"]
theorem erdos_497 :
    ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
      ∀ n : ℕ, (DedekindNumber.M' n : ℝ) = 2 ^ ((1 + o n) * (n.choose (n / 2) : ℝ)) := by
  sorry

end Erdos497
