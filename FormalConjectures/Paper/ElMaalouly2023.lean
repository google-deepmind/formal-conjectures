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
# Exact matching in general graphs

El Maalouly, *Exact Matching: Algorithms and Related Problems*, STACS 2023,
§1, pp. 29:1–29:3: https://doi.org/10.4230/LIPIcs.STACS.2023.29.

The input is a finite undirected graph, a red/blue coloring of its edges,
and an integer $k$. The question asks for a perfect matching with exactly
$k$ red edges. Both adjacency and red-edge matrices are explicit; malformed
matrices are rejected, and $k$ is binary. There is no bipartiteness, planarity,
density or bounded-independence-number restriction.

This is the two-color problem, not exact matching with arbitrary binary
edge weights. Its randomized polynomial-time algorithm is literature
background, not a theorem proved in this file.
-/

namespace ElMaalouly2023

/-- Does general-graph Exact Matching admit a deterministic polynomial-time decider? -/
@[category research open, AMS 5 68]
theorem exactMatching_polytime : answer(sorry) ↔
    ComplexityTheory.HasPolyTimeDecider Computability.MatrixGraph.ExactMatching := by
  sorry

end ElMaalouly2023
