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
# Erdős Problem 474: the continuum-aleph-two consistency question

*References:*
- [erdosproblems.com/474](https://www.erdosproblems.com/474)
- [Va99] Various, Some of Paul's favorite problems. Booklet produced for the conference
  "Paul Erdős and his mathematics", Budapest, July 1999 (1999), 7.81.
-/

@[expose] public section

namespace Erdos474

/--
It remains open whether it is consistent to have a negative answer assuming
$\mathfrak{c}=\aleph_2$. (This specific question is asked in [Va99].)

Here consistency is represented by existence of a set-sized membership model of ZFC
with continuum $\aleph_2$ in which no symmetric three-coloring of distinct pairs
realizes every color on every internally uncountable subset of the continuum.
The continuum is represented internally by the power set of $\omega$.
This is a semantic model-existence question; no equivalence to syntactic or
relative consistency is asserted.
-/
@[category research open, AMS 3]
theorem erdos_474.variants.aleph_two_model :
    answer(sorry) ↔ Erdos474Model.SemanticConsistencyQuestion := by
  sorry

end Erdos474
