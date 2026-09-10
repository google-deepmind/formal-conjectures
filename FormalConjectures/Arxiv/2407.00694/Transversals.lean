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
# Output-polynomial hypergraph-transversal enumeration

*References:*
* Mary, *Enumeration of minimal transversals of hypergraphs of bounded
  VC-dimension*, §1, Trans-Enum, https://arxiv.org/html/2407.00694v3.
-/

namespace Mary2024

/-- **Unrestricted transversal enumeration** (Mary, §1, Trans-Enum): can one
uniform deterministic algorithm enumerate every inclusion-minimal hitting set of
an explicit finite hypergraph exactly once in time polynomial in combined input
and complete output length? Edges are binary lists of natural-number vertex names;
answers are canonically encoded finite sets of occurring vertices. Repeated names
or redundant edges do not create extra answers. An empty edge yields no answers;
the empty hypergraph has the empty set as its sole minimal transversal. This is
a two-sided output-sensitive question, with no VC-dimension restriction and no
polynomial-delay or incremental-time requirement. -/
@[category research open, AMS 5 68]
theorem output_poly_transversals : answer(sorry) ↔
    ComplexityTheory.HasOutputPolyEnumerator HypergraphEnumeration.MinimalTransversal := by
  sorry

end Mary2024
