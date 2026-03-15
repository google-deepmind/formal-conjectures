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
# Erdős Problem 53

*Reference:* [erdosproblems.com/53](https://www.erdosproblems.com/53)

For every $k$, if $|A|$ is sufficiently large, then there are at least $|A|^k$ distinct integers
that are either a sum or product of distinct elements of $A$. Solved by Chang [Ch03].

[ErSz83] Erdős, P. and Szemerédi, E., _On sums and products of integers_. Studies in Pure
Mathematics, Birkhäuser, Basel (1983), 213–218.

[Ch03] Chang, M.-C., _The Erdős-Szemerédi problem on sum set and product set_. Annals of
Mathematics **157** (2003), 939–957.
-/

open Finset BigOperators

namespace Erdos53

/--
The set of all subset sums of a finite set of integers:
$\{ \sum_{i \in S} i \mid S \subseteq A \}$.
-/
def subsetSums (A : Finset ℤ) : Finset ℤ :=
  A.powerset.image (fun S => ∑ i ∈ S, i)

/--
The set of all subset products of a finite set of integers:
$\{ \prod_{i \in S} i \mid S \subseteq A \}$.
-/
def subsetProducts (A : Finset ℤ) : Finset ℤ :=
  A.powerset.image (fun S => ∏ i ∈ S, i)

/--
**Erdős Problem 53** [ErSz83]:

Is it true that, for every $k$, if $|A|$ is sufficiently large depending on $k$, then there are
at least $|A|^k$ many integers which are either the sum or product of distinct elements of $A$?

Solved in this form by Chang [Ch03].
-/
@[category research solved, AMS 5 11]
theorem erdos_53 : answer(True) ↔
    ∀ k : ℕ, ∃ N : ℕ, ∀ A : Finset ℤ,
    A.card ≥ N →
    (subsetSums A ∪ subsetProducts A).card ≥ A.card ^ k := by
  sorry

end Erdos53
