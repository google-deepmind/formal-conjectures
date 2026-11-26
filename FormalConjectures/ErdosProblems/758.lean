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
-/

@[expose] public section

namespace Erdos758

/-- A graph admits a colouring with at most `k` homogeneous colour classes. -/
def CochromaticColorable {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ c : Fin n → Fin k, ∀ i : Fin k,
    (∀ u v, c u = i → c v = i → u ≠ v → G.Adj u v) ∨
    (∀ u v, c u = i → c v = i → u ≠ v → ¬ G.Adj u v)

/--
In particular is it true that $z(12)=4$?

Here $z(n)$ is the maximum cochromatic number of an $n$-vertex graph. A colour
class may induce either a complete graph or an empty graph. The source credits
Bhavik Mehta's computation for the affirmative resolution.
-/
@[category research solved, question, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos758.lean"]
theorem erdos_758 :
    (∀ G : SimpleGraph (Fin 12), CochromaticColorable G 4) ∧
      (∃ G : SimpleGraph (Fin 12), ¬ CochromaticColorable G 3) := by
  sorry

end Erdos758
