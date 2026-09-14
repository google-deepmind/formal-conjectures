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
# Unique Games and perfect-completeness 2-to-1 Games

*References:*
* Subhash Khot, *On the power of unique 2-prover 1-round games*, STOC 2002,
  pp. 767–775, §1 (Unique Games and d-to-1 conjectures) and §2.2,
  https://doi.org/10.1145/509907.510017;
  https://cs.nyu.edu/~khot/papers/khot-csp.ps.
* Guruswami, Khot, O'Donnell, Popat, Tulsiani and Wu, *SDP gaps for 2-to-1
  and other Label-Cover variants*, ICALP 2010, Definitions 1–2 and
  Conjectures 1–2, pp. 2–3, https://www.cs.cmu.edu/~odonnell/papers/2-to-1-gaps.pdf.
-/

namespace Khot2002

open ComplexityTheory Computability.LabelCover

/-- **Unique Games** (Khot 2002, §1; Guruswami et al., Conjecture 1):
for all rational $\varepsilon,\delta>0$
with $\varepsilon+\delta<1$, some fixed alphabet size $q>0$ makes distinguishing
value at least $1-\varepsilon$ from value at most $\delta$ NP-hard under deterministic
polynomial-time many-one reductions. Inputs are binary lists of unweighted bipartite
edges with total projection tables on equal alphabets; every fiber has size at most
one. Value is the maximum satisfied fraction of edges. Empty or malformed games
are outside both promises. The alphabet is fixed before input and reduction.
Together with $P\ne NP$, this excludes polynomial-time separation. -/
@[category research open, AMS 5 68]
theorem unique_games :
    ∀ ε δ : ℚ, 0 < ε → 0 < δ → ε + δ < 1 →
      ∃ q : ℕ, 0 < q ∧ PromiseNPHard (Yes 1 q (1 - ε)) (No 1 q δ) := by sorry

/-- **Perfect-completeness 2-to-1 Games** (Khot 2002, §1, $d=2$;
Guruswami et al., Conjecture 2): for every rational
$0<\delta<1$, some fixed alphabet size $q>0$ makes distinguishing value exactly
one from value at most $\delta$ NP-hard under deterministic polynomial-time
many-one reductions. Inputs are nonempty, well-formed binary bipartite edge lists
with total projection tables on equal alphabets and fibers of size at most two,
using the Label-Cover convention of Guruswami et al., Definitions 1–2.
Value maximizes the uniformly weighted satisfied-edge fraction. All edges must be
satisfied in the yes case; near-perfect completeness is a different assertion.
Together with $P\ne NP$, this excludes polynomial-time separation. -/
@[category research open, AMS 5 68]
theorem two_to_one_perfect :
    ∀ δ : ℚ, 0 < δ → δ < 1 →
      ∃ q : ℕ, 0 < q ∧ PromiseNPHard (Yes 2 q 1) (No 2 q δ) := by sorry

end Khot2002
