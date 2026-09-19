/-
Copyright 2025 The Formal Conjectures Authors.

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
public import FormalConjectures.ErdosProblems.«54»

/-!
# Erdős Problem 843

*References:*
- [erdosproblems.com/843](https://www.erdosproblems.com/843)
- [BuEr85] Burr, S. A. and Erdős, P., _A Ramsey-type property in additive number theory_. Glasgow
  Math. J. (1985), 5--10.
- [Er92b] Erdős, Paul, _Some of my favourite problems in various branches of combinatorics_.
  Matematiche (Catania) (1992), 231-240.
- [Er95] Erdős, Paul, _Some of my favourite problems in number theory, combinatorics, and
  geometry_. Resenhas (1995), 165-186.
- [CFP21] Conlon, D. and Fox, J. and Pham, H. T., _Subset sums, completeness and colorings_.
  arXiv:2104.14766 (2021).
-/

@[expose] public section

open Erdos54

namespace Erdos843

/--
Are the squares Ramsey $2$-complete?

That is, is it true that, in any 2-colouring of the square numbers, every sufficiently large
$n\in \mathbb{N}$ can be written as a monochromatic sum of distinct squares?

A problem of Burr and Erdős. In [Er95] Erdős reported that Burr had proved that the set of
$k$th powers is Ramsey $r$ complete for all $r,k\geq 2$, but this result was never published.
A stronger version was proved by Conlon, Fox, and Pham [CFP21].

See also [54](https://www.erdosproblems.com/54) and [55](https://www.erdosproblems.com/55).
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos843.lean#L2338"]
theorem erdos_843 : answer(True) ↔ IsRamseyComplete 2 {n : ℕ | ∃ m, 0 < m ∧ n = m ^ 2} := by
  sorry

/--
A similar question can be asked for the set of $k$th powers for any $k\geq 3$. Burr proved
(unpublished, see [Er95]) that the set of $k$th powers is Ramsey $r$-complete for all
$r,k\geq 2$; this also follows from Conlon, Fox, and Pham [CFP21].
-/
@[category research solved, AMS 5 11]
theorem erdos_843.variants.powers (r k : ℕ) (hr : 2 ≤ r) (hk : 2 ≤ k) :
    IsRamseyComplete r {n : ℕ | ∃ m, 0 < m ∧ n = m ^ k} := by
  sorry

end Erdos843
