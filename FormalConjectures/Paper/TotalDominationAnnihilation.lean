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
# Total domination and the annihilation number

*References:*
- [Cs. Bujtás and M. Jakovac, Relating the total domination number and the annihilation number of cactus graphs and block graphs, Conjecture 1 (2019)](https://doi.org/10.26493/1855-3974.1378.11d)
- [M. Jakovac, Conjecture 1, version 2](https://arxiv.org/abs/2609.10795v2)
- [J. J. Gebendorfer, A mixed transversal bound and the total-domination–annihilation conjecture, 11 October 2026; manuscript archive](https://github.com/user-attachments/files/33357596/Total_Domination_Annihilation_Intake_2026-10-12.zip)

The reformulation is credited to Desormeaux–Haynes–Henning in the cited sources.
This is the original +1 conjecture, including graphs with pendant vertices,
adjacent supports and strong supports, not the stronger four-cycle-indicator
variant. The existing annihilation-number equivalence proof_wanted is unaffected.
-/

@[expose] public section
namespace DesormeauxHaynesHenning
open SimpleGraph

/-- Every connected finite simple graph of order at least two satisfies
$\gamma_t(G)\le a(G)+1$. The annihilation number maximizes the cardinality
of a degree submultiset whose sum is at most the number of edges. -/
@[category research solved, AMS 5]
theorem total_domination_annihilation {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (horder : 2 ≤ Fintype.card V) :
    G.totalDominationNumber ≤ G.annihilationNumber + 1 := by
  sorry

end DesormeauxHaynesHenning
