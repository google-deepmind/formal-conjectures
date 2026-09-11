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
# Logarithmic-seed pseudorandom generators

*References:*
* Vadhan, *Pseudorandomness*, §7.1.1–§7.1.2, pp. 214–219,
  Definitions 7.1, 7.3, 7.4, 7.7 and regime (3),
  https://people.seas.harvard.edu/~salil/pseudorandomness/pseudorandomness-published-Dec12.pdf.
-/

namespace VadhanPseudorandomness

/-- **Logarithmic-seed generators** (Vadhan, §7.1.2, regime (3), p. 218) exist
against general Boolean circuits. One uniform polynomial-time generator and
seed-length algorithm, given output length $m$ in unary, produce $m$ output bits.
For some $c$ and all sufficiently large $m\ge2$, the seed length is at most
$c\log_2m$ and less than $m$, and every circuit with at most $m$ AND/OR gates has
distinguishing advantage at most $1/8$. NOT gates are free; depth and fan-out are
unrestricted. Polynomial time is in output length, not seed length. The finite
exceptional prefix avoids impossible small-length stretch. Such generators imply
$BPP=P$. -/
@[category research open, AMS 3 68]
theorem logarithmic_seed_prg : ComplexityTheory.LogSeedPRGExists := by
  sorry

end VadhanPseudorandomness
