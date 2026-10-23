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
# Erdős Problem 758: the twelve-vertex case

*Reference:* [erdosproblems.com/758](https://www.erdosproblems.com/758)

[ErGi93] Erdős, P. and Gimbel, J., *Some problems and results in cochromatic
theory*, Annals of Discrete Mathematics 55 (1993), 261–264.

A cochromatic colouring partitions the vertices into classes, each inducing
either a complete graph or an empty graph. The page asks for small values of
the maximum cochromatic number, and specifically whether $z(12)=4$.
This statement expresses that specific equality by its uniform upper bound
and an explicit existence lower bound. The page credits Bhavik Mehta's computation.
The broader table of small values is not asserted here.
-/

@[expose] public section

namespace Erdos758

/-- A graph admits a colouring with at most `k` homogeneous colour classes. -/
def CochromaticColorable {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ c : Fin n → Fin k, ∀ i : Fin k,
    (∀ u v, c u = i → c v = i → u ≠ v → G.Adj u v) ∨
    (∀ u v, c u = i → c v = i → u ≠ v → ¬ G.Adj u v)

/-- Every twelve-vertex graph has cochromatic number at most four, and some
twelve-vertex graph has cochromatic number greater than three: $z(12)=4$. -/
@[category research solved, question, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos758.lean"]
theorem erdos_758 :
    (∀ G : SimpleGraph (Fin 12), CochromaticColorable G 4) ∧
      (∃ G : SimpleGraph (Fin 12), ¬ CochromaticColorable G 3) := by
  sorry

end Erdos758
