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
# Randomized Exponential Time Hypothesis

*References:*
* Liu and Chen, *Sub-Exponential Time Lower Bounds for #VC and #Matching on
  3-Regular Graphs*, STACS 2024, Conjecture 5, p. 49:5,
  https://doi.org/10.4230/LIPIcs.STACS.2024.49.
-/

namespace LiuChen2024

open FineGrained

/-- **Randomized ETH** (Liu–Chen, Conjecture 5), in the logarithmic-input-width
word-RAM model: some integer $b>0$ excludes a bounded-error 3-SAT solver with time
$C(L+1)^d2^{\lfloor n/b\rfloor}$ for any fixed $C,d$. Input is a binary-encoded
signed CNF formula of length $L$, every clause has at most three literals, and $n$
is the number of distinct variables occurring. Repeated literals and empty clauses
are retained. One fixed program must halt within the bound on every random tape
and be correct with probability at least $2/3$ on each input. Word width is
$O(\log(L+2))$, hence addressable memory is polynomial in $L$. -/
@[category research open, AMS 68]
theorem randomized_ETH :
    ∃ b : ℕ, 0 < b ∧ ¬ HasSatTime 3 1 b := by sorry

end LiuChen2024
