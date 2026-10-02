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
# Normal and rich numbers and the sequence $(b^n \xi)$ modulo one

Let $b \ge 2$ be an integer. A real number $\xi$ is normal in base $b$ if and only if the
sequence $(b^n \xi)_{n \ge 0}$ is uniformly distributed modulo one. This was proved by Wall
[Wal49]; see also [Bug12, Theorem 4.14] and [EvdPSW03, p. 127].

A real number $\xi$ is rich (or disjunctive) in base $b$ if every finite block of digits occurs in
its base-$b$ expansion. By the same argument, $\xi$ is rich in base $b$ if and only if the
sequence $(b^n \xi)_{n \ge 0}$ is dense modulo one [Bug12, Section 4.4].

The two easy implications, normal implies rich and uniformly distributed implies dense, are
`NormalNumber.IsNormalInBase.isRichInBase` and `IsEquidistributedModuloOne.dense_range`.

*References:*
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Cambridge Tracts in Mathematics 193. Cambridge University Press, 2012. Chapter 4.
  - [Wal49] Wall, Donald Dines. "Normal numbers." Ph.D. thesis, University of California,
    Berkeley, 1949.
  - [EvdPSW03] Everest, Graham, Alf van der Poorten, Igor Shparlinski, and Thomas Ward.
    "Recurrence sequences." Mathematical Surveys and Monographs 104. American Mathematical
    Society, Providence, RI, 2003.
-/

@[expose] public section

open NormalNumber

namespace BugeaudNormalAndRich

/-- A real number $\xi$ is normal in base $b$ if and only if $(b^n \xi)_{n \ge 0}$ is uniformly
distributed modulo $1$ [Wal49], [Bug12, Theorem 4.14]. -/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/rwst/formal-conjectures/blob/a522a5352dd28df0b5ef08c213c368b5f6a5df6e/FormalConjectures/Books/BugeaudDistributionModuloOne/NormalAndRich.lean#L459"]
theorem isNormalInBase_iff_isEquidistributedModuloOne (b : ℕ) (hb : 2 ≤ b) (ξ : ℝ) :
    IsNormalInBase b ξ ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * ξ := by
  sorry

/-- A real number $\xi$ is rich in base $b$ if and only if $(b^n \xi)_{n \ge 0}$ is dense
modulo $1$ [Bug12, Section 4.4]. -/
@[category textbook, AMS 11, formal_proof using formal_conjectures at
"https://github.com/rwst/formal-conjectures/blob/a522a5352dd28df0b5ef08c213c368b5f6a5df6e/FormalConjectures/Books/BugeaudDistributionModuloOne/NormalAndRich.lean#L466"]
theorem isRichInBase_iff_dense (b : ℕ) (hb : 2 ≤ b) (ξ : ℝ) :
    IsRichInBase b ξ ↔ Dense (Set.range fun n => (↑((b : ℝ) ^ n * ξ) : AddCircle (1 : ℝ))) := by
  sorry

end BugeaudNormalAndRich
