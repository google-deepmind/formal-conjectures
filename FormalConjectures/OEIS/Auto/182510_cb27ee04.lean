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

open Int

/--
A182510: $a(0)=0, a(1)=1, a(n)=(a(n-1) \text{ XOR } n) - a(n-2)$, where $\text{XOR}$ is the bitwise exclusive-or operator.
-/
def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 => Int.xor (a (n + 1)) (n + 2 : ℤ) - a n

open Filter Set

/-- oeis_182510_conjecture_0: A182510 Conjectures: the sequence contains 8 zeros.
This is formalized as the set of indices $n$ where $a(n)=0$ having cardinality 8.
Note that `Set.ncard` is the cardinality of a set assuming it is finite.
-/
theorem oeis_a182510_conjecture_zeros :
  Set.ncard {n : ℕ | a n = 0} = 8 :=
by sorry

/-- oeis_182510_conjecture_1: A182510 Conjectures: more positive terms than negative.
This is formalized as the asymptotic (natural) density of positive terms being strictly greater
than the asymptotic density of negative terms, assuming both densities exist.
The set of positive indices is $P = \{n \mid a(n) > 0\}$, and the set of negative indices is $N_{neg} = \{n \mid a(n) < 0\}$.
The natural density of a set $S \subseteq \mathbb{N}$ is defined in Mathlib as `S.HasDensity d`.
-/
theorem oeis_a182510_conjecture_density :
  ∃ d_pos d_neg : ℝ,
    ({n : ℕ | a n > 0}).HasDensity d_pos ∧
    ({n : ℕ | a n < 0}).HasDensity d_neg ∧
    d_pos > d_neg :=
by sorry
