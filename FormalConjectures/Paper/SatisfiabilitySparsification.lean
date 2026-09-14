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
# Nondeterministic polynomial advice and complements of NP

*References:*
* Dell and van Melkebeek, *Satisfiability Allows No Nontrivial Sparsification
  unless the Polynomial-Time Hierarchy Collapses*, JACM 61(4), Article 23 (2014),
  abstract and §2, p. 23:8, https://doi.org/10.1145/2629620;
  https://pages.cs.wisc.edu/~dieter/Papers/sparsification-jacm.pdf.
-/

namespace DellVanMelkebeek2014

open ComplexityTheory

/-- **No nondeterministic polynomial advice for all of coNP** (Dell–van Melkebeek,
abstract and §2): $coNP\not\subseteq NP/poly$. Some bit-string language in $coNP$
cannot be decided by an $NP$ verifier given polynomial-length advice depending
only on input length. A single verifier and advice sequence must work on every
input; the advice may be uncomputable but cannot depend on the input's contents.
The verifier receives the binary encoding of the input/advice pair. This
noncontainment implies $NP\ne coNP$ and hence $P\ne NP$. -/
@[category research open, AMS 68]
theorem coNP_not_subset_NPpoly : ¬ coNP ⊆ NPpoly := by sorry

end DellVanMelkebeek2014
