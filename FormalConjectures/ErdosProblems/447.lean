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
# Erdős Problem 447

*References:*
- [erdosproblems.com/447](https://www.erdosproblems.com/447)
- [Er65b] Erdős, Paul, *Some recent advances and current problems in number theory*. Lectures on
  Modern Mathematics, Vol. III (1965), 196-244.
- [Kl71] Kleitman, Daniel, *Collections of subsets containing no two sets and their union*.
  Proceedings of the LA Meeting AMS (1971), 153-155.
-/

open Filter

namespace Erdos447

/-- A collection $\mathcal{F}$ of sets is *union-free* if there are no solutions to
$A\cup B=C$ with distinct $A,B,C\in \mathcal{F}$. -/
def UnionFree {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, ∀ C ∈ F, A ≠ B → A ≠ C → B ≠ C → A ∪ B ≠ C

/-- The largest size of a union-free collection $\mathcal{F}$ of subsets of $[n]$. -/
noncomputable def maxUnionFree (n : ℕ) : ℕ :=
  sSup { k | ∃ F : Finset (Finset (Fin n)), UnionFree F ∧ F.card = k }

/--
How large can a union-free collection $\mathcal{F}$ of subsets of $[n]$ be? By union-free we mean
there are no solutions to $A\cup B=C$ with distinct $A,B,C\in \mathcal{F}$. Must
$\lvert \mathcal{F}\rvert =o(2^n)$?

In [Er65b] Erdős reported that the estimate $\lvert \mathcal{F}\rvert=o(2^n)$ was proved in
unpublished work by Sárközy and Szemerédi.
-/
@[category research solved, AMS 5]
theorem erdos_447.parts.i : answer(True) ↔
    (fun n : ℕ => (maxUnionFree n : ℝ)) =o[atTop] (fun n : ℕ => (2 : ℝ) ^ n) := by
  sorry

/--
How large can a union-free collection $\mathcal{F}$ of subsets of $[n]$ be? By union-free we mean
there are no solutions to $A\cup B=C$ with distinct $A,B,C\in \mathcal{F}$. Perhaps even
\[\lvert \mathcal{F}\rvert <(1+o(1))\binom{n}{\lfloor n/2\rfloor}?\]

Solved by Kleitman [Kl71], who proved
\[\lvert \mathcal{F}\rvert <(1+o(1))\binom{n}{\lfloor n/2\rfloor}.\]
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos447.lean"]
theorem erdos_447.parts.ii : answer(True) ↔
    ∃ c : ℕ → ℝ, (c =o[atTop] (1 : ℕ → ℝ)) ∧ ∀ᶠ n : ℕ in atTop,
      (maxUnionFree n : ℝ) < (1 + c n) * (n.choose (n / 2) : ℝ) := by
  sorry

end Erdos447
