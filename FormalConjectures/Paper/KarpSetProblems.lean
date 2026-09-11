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
# Karp's NP-complete finite-set problems

*References:*
* [Ka72] Karp, R. M., *Reducibility among Combinatorial Problems*.
  In *Complexity of Computer Computations*, Plenum (1972), pp. 85–103.
  §4, Theorem 3 and Main Theorem items 4, 6, 14, 15, 17, pp. 93–95.
  https://doi.org/10.1007/978-1-4684-2001-2_9.
-/

namespace Karp1972

open ComplexityTheory Computability.FiniteSetProblems

/-- **SET PACKING** ([Ka72], item 4, p. 94). No deterministic polynomial-time algorithm decides
whether an explicitly listed, indexed family of finite sets contains $k$ pairwise disjoint
members. Element names and the positive requested count $k$ are binary natural numbers.
Set packing is NP-complete, so this conjecture is equivalent to $P \ne NP$ (`P_ne_NP`). -/
@[category research open, AMS 5 68]
theorem setPacking_not_polytime : ¬ HasPolyTimeDecider SetPacking := by
  sorry

/-- **SET COVERING** ([Ka72], item 6, p. 94). No deterministic polynomial-time algorithm decides
whether at most $k$ members of an explicitly listed finite-set family cover the union of the
whole family. Element names and the positive bound $k$ are binary natural numbers.
Set covering is NP-complete, so this conjecture is equivalent to $P \ne NP$ (`P_ne_NP`). -/
@[category research open, AMS 5 68]
theorem setCovering_not_polytime : ¬ HasPolyTimeDecider SetCovering := by
  sorry

/-- **EXACT COVER** ([Ka72], item 14, p. 95). No deterministic polynomial-time algorithm
decides whether an explicitly listed family of subsets of a finite universe has pairwise
disjoint members covering that universe. The universe is explicit and element names are binary.
Exact cover is NP-complete, so this conjecture is equivalent to $P \ne NP$ (`P_ne_NP`). -/
@[category research open, AMS 5 68]
theorem exactCover_not_polytime : ¬ HasPolyTimeDecider ExactCover := by
  sorry

/-- **HITTING SET** in Karp's exact sense ([Ka72], item 15, p. 95). No deterministic
polynomial-time algorithm decides whether a finite set meets every member of an explicitly
listed family in exactly one element. Element names are binary. There is no witness-size
budget. A witness may be restricted to the family's union, since outside elements hit no row.
This problem is NP-complete, so the conjecture is equivalent to $P \ne NP$ (`P_ne_NP`). -/
@[category research open, AMS 5 68]
theorem exactHitting_not_polytime : ¬ HasPolyTimeDecider ExactHitting := by
  sorry

/-- **3-DIMENSIONAL MATCHING** ([Ka72], item 17, p. 95). No deterministic polynomial-time
algorithm decides whether an explicitly listed relation $U \subseteq T^3$, with $T$ also
explicit and all element names binary, has $|T|$ triples no two of which agree in a coordinate.
This problem is NP-complete, so the conjecture is equivalent to $P \ne NP$ (`P_ne_NP`). -/
@[category research open, AMS 5 68]
theorem threeDimensionalMatching_not_polytime :
    ¬ HasPolyTimeDecider ThreeDimensionalMatching := by
  sorry

end Karp1972
