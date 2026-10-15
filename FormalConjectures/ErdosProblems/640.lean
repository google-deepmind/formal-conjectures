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
# Erdős Problem 640

*References:*
- [erdosproblems.com/640](https://www.erdosproblems.com/640)
- [Er97d] Erdős, Paul, *Some recent problems and results in graph theory*. Discrete Math.
  (1997), 81–85, p.84.
- [Er97d] Erdős, Paul, *Some recent problems and results in graph theory*. Discrete Math.
  (1997), 81–85.
-/

@[expose] public section

open SimpleGraph

namespace Erdos640

/-- An odd cycle whose vertices induce a graph of chromatic number at least `k`. -/
def HasHighChromaticOddCycle {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ v, ∃ p : G.Walk v v, p.IsCycle ∧ Odd p.length ∧
    (k : ℕ∞) ≤ (G.induce {x | x ∈ p.support}).chromaticNumber

/--
For every $k \geq 3$, does there exist $f(k)$ such that every finite graph of chromatic
number at least $f(k)$ has an odd cycle whose vertices induce a graph of chromatic
number at least $k$? The cycle may have chords in the ambient graph.
-/
@[category research open, question, AMS 5]
theorem erdos_640 :
    ∀ k : ℕ, 3 ≤ k → ∃ N : ℕ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      (N : ℕ∞) ≤ G.chromaticNumber → HasHighChromaticOddCycle G k := by
  sorry

/-- Every finite graph of chromatic number at least $3$ has an odd cycle whose vertices
induce a graph of chromatic number at least $3$. -/
@[category textbook, AMS 5, formal_proof using lean4 at
  "https://github.com/AItoBit/formal-conjectures/blob/0e6191e205ebdc112d8d5c8ec8ff9a3f7f1b0616/proofs/erdos640/Erdos640.lean"]
theorem erdos_640.variants.three (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : (3 : ℕ∞) ≤ G.chromaticNumber) : HasHighChromaticOddCycle G 3 := by
  sorry

end Erdos640
