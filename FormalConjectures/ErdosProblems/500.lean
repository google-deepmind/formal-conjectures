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
import Mathlib.Data.Nat.Choose
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Erdős Problem 500

*Reference:* [erdosproblems.com/500](https://www.erdosproblems.com/500)

What is $\mathrm{ex}_3(n,K_4^3)$? That is, the largest number of $3$-edges which can
placed on $n$ vertices so that there exists no $K_4^3$, a set of 4 vertices which is
covered by all 4 possible $3$-edges.
-/

namespace Erdos500

open Finset

/--
A 3-uniform hypergraph on a finite type `V` is a set of 3-element subsets of `V`.
-/
abbrev Hypergraph (V : Type*) := Finset (Finset V)

/--
A hypergraph contains a `K_4^3` if there exists a 4-element set of vertices
all of whose 3-element subsets are edges.
-/
def containsK4 {V : Type*} (H : Hypergraph V) : Prop :=
  ∃ T : Finset V, T.card = 4 ∧ ∀ E : Finset V, E ⊆ T ∧ E.card = 3 → E ∈ H

/--
A hypergraph is `K_4^3`‑free if all its edges have size 3 and it contains no `K_4^3`.
-/
def isK4Free {V : Type*} (H : Hypergraph V) : Prop :=
  (∀ E ∈ H, E.card = 3) ∧ ¬ containsK4 H

/--
The extremal number `ex_3(n,K_4^3)`:
the maximum number of edges in a 3‑uniform hypergraph on `n` vertices
(with vertex set `Fin n`) that is `K_4^3`‑free.
-/
noncomputable def ex3 (n : ℕ) : ℕ :=
  sSup { H.card | (H : Hypergraph (Fin n)) | isK4Free H }

/--
A simple upper bound: every `K_4^3`‑free 3‑uniform hypergraph on `n` vertices
has at most `3/4 * binom(n,3)` edges.

This follows by counting 4‑sets: each 4‑set contains at most 3 edges, and each edge
is contained in exactly `n-3` such 4‑sets.
-/
@[category research, AMS 52]
theorem erdos_500 (n : ℕ) : (ex3 n : ℝ) ≤ (3 / 4) * (n.choose 3 : ℝ) := by
  sorry

-- TODO(firsching): improve bounds; the exact value remains open.

end Erdos500
