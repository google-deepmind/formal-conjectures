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

Mary, *Enumeration of minimal transversals of hypergraphs of bounded
VC-dimension*, §1, Trans-Enum, https://arxiv.org/html/2407.00694v3.

The unrestricted problem remains distinct from the solved bounded-VC-dimension
case. Output-polynomial means a bound on total time in input and output length,
not polynomial delay or an incremental bound.
-/

namespace Mary2024

/-- Can every inclusion-minimal transversal of an explicit finite hypergraph be
enumerated without duplication in total time polynomial in the combined
encoded input and output lengths? -/
@[category research open, AMS 5 68]
theorem output_poly_transversals : answer(sorry) ↔
    ComplexityTheory.HasOutputPolyEnumerator HypergraphEnumeration.MinimalTransversal := by
  sorry

end Mary2024
