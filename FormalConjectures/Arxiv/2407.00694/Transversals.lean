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
* Eiter–Gottlob, *Identifying the Minimal Transversals of a Hypergraph and Related
  Problems* (1995), §1, pp. 1278–1279; Definition 2.3, p. 1280,
  https://doi.org/10.1137/S0097539793250299.
* Fredman–Khachiyan, *On the Complexity of Dualization of Monotone Disjunctive
  Normal Forms* (1996), https://doi.org/10.1006/jagm.1996.0062.
* Mary, *Enumeration of minimal transversals of hypergraphs of bounded
  VC-dimension*, §1, Trans-Enum, https://arxiv.org/html/2407.00694v3.
-/

namespace Arxiv.«2407.00694»

/-- **Unrestricted transversal enumeration** (Eiter–Gottlob, §1, p. 1279;
Mary, §1, Trans-Enum): can one
uniform deterministic algorithm enumerate every inclusion-minimal hitting set of
an explicit finite hypergraph exactly once in time polynomial in combined input
and complete output length? Edges are binary lists of natural-number vertex names;
answers are canonically encoded finite sets of occurring vertices. Repeated names
or redundant edges do not create extra answers. An empty edge yields no answers;
the empty hypergraph has the empty set as its sole minimal transversal. This is
a two-sided output-sensitive question, with no VC-dimension restriction and no
polynomial-delay or incremental-time requirement. Fredman–Khachiyan study the
dualization problem; Mary's result concerns the bounded-VC-dimension special case. -/
@[category research open, AMS 5 68]
theorem output_poly_transversals : answer(sorry) ↔
    ComplexityTheory.HasOutputPolyEnumerator HypergraphEnumeration.MinimalTransversal := by
  sorry

end Arxiv.«2407.00694»
