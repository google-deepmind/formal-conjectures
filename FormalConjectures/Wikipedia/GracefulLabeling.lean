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

import FormalConjectures.Util.ProblemImports

/-!
# Graceful Tree Conjecture (Ringel–Kotzig conjecture)

*Reference:* [Wikipedia/Graceful_labeling](https://en.wikipedia.org/wiki/Graceful_labeling)

Conjectured by Ringel (1963) and Kotzig; formalized by Rosa (1967).
-/

namespace GracefulLabeling

open SimpleGraph

example :
    let T : SimpleGraph Unit := ⊥
    let m := T.edgeFinset.card
    ∃ f : Unit → ℕ,
      Function.Injective f ∧
      (∀ v, f v ≤ m) ∧
      T.edgeFinset.image (fun e =>
        e.lift ⟨fun u v => Int.natAbs ((f u : ℤ) - (f v : ℤ)),
                fun u v => by
                  show ((f u : ℤ) - f v).natAbs = ((f v : ℤ) - f u).natAbs
                  rw [← Int.natAbs_neg, neg_sub]⟩) = Finset.Icc 1 m := by
  intro T m
  use fun _ => 0
  refine ⟨fun _ _ _ => rfl, fun _ => Nat.zero_le _, ?_⟩
  simp [m, T]

example :
    let T : SimpleGraph (Fin 2) := ⊤
    let m := T.edgeFinset.card
    ∃ f : Fin 2 → ℕ,
      Function.Injective f ∧
      (∀ v, f v ≤ m) ∧
      T.edgeFinset.image (fun e =>
        e.lift ⟨fun u v => Int.natAbs ((f u : ℤ) - (f v : ℤ)),
                fun u v => by
                  show ((f u : ℤ) - f v).natAbs = ((f v : ℤ) - f u).natAbs
                  rw [← Int.natAbs_neg, neg_sub]⟩) = Finset.Icc 1 m := by
  intro T m
  use Fin.val
  refine ⟨Fin.val_injective, by decide, ?_⟩
  revert m T
  decide

/--
Every tree admits a graceful labeling.

A graceful labeling of a tree $T$ with $m$ edges is an injective map $f : V \to \{0, \dots, m\}$
such that the multiset of absolute differences $|f(u) - f(v)|$ over edges $\{u,v\}$ of $T$
equals $\{1, \dots, m\}$.
-/
@[category research open, AMS 5]
theorem graceful_tree_conjecture {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) :
    let m := T.edgeFinset.card
    ∃ f : V → ℕ,
      Function.Injective f ∧
      (∀ v, f v ≤ m) ∧
      T.edgeFinset.image (fun e =>
        e.lift ⟨fun u v => Int.natAbs ((f u : ℤ) - (f v : ℤ)),
                fun u v => by
                  show ((f u : ℤ) - f v).natAbs = ((f v : ℤ) - f u).natAbs
                  rw [← Int.natAbs_neg, neg_sub]⟩) = Finset.Icc 1 m := by
  sorry

end GracefulLabeling
