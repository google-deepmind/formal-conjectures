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
# Conjectures associated with A28859

A028859 (OEIS): $a(n+2) = 2 \cdot a(n+1) + 2 \cdot a(n)$; $a(0) = 1$, $a(1) = 3$.

*References:*
- [A28859](https://oeis.org/A28859)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA28859


/--
A028859 (OEIS): $a(n+2) = 2 \cdot a(n+1) + 2 \cdot a(n)$; $a(0) = 1$, $a(1) = 3$.
-/
def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 3
  | (n + 2) => 2 * a (n + 1) + 2 * a n
termination_by n

set_option linter.unusedVariables false


@[category test, AMS 11]
lemma a_two : a 2 = 8 := by native_decide

@[category test, AMS 11]
lemma a_three : a 3 = 22 := by native_decide

@[category test, AMS 11]
lemma a_four : a 4 = 60 := by native_decide


/--
A028859 (OEIS): $a(n+2) = 2 \cdot a(n+1) + 2 \cdot a(n)$; $a(0) = 1$, $a(1) = 3$.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/28859.wip.lean#L402"]
theorem target_theorem_0
  (n : ℕ) :
    let L := n + 1
    let Sequence := Fin L → ℕ
    let S : Set Sequence :=
      {σ : Sequence |
        L > 0 ∧
          (∀ i : Fin L, σ i > 0) ∧
            let max_val := Finset.sup Finset.univ σ
            (∀ k : ℕ, 1 ≤ k ∧ k ≤ max_val → ∃ i : Fin L, σ i = k) ∧
            (∀ i j : Fin L, i < j → j.val ≠ i.val + 1 → σ i ≥ σ j)}
    ∃ (F : Finset Sequence), (F : Set Sequence) = S ∧ F.card = a n := by
    sorry

end OeisA28859
