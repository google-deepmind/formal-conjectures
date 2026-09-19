/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 1027

*References:*
- [erdosproblems.com/1027](https://www.erdosproblems.com/1027)
- [Er64e] Erdős, P., *On a combinatorial problem. II*. Acta Math. Acad. Sci. Hungar. (1964),
  445-447.
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
-/

@[expose] public section

open Filter

namespace Erdos1027

variable {α : Type*} [DecidableEq α]

/-- The ground set $X=\bigcup_{A\in\mathcal{F}}A$ of a finite family of finite sets. -/
def groundSet (F : Finset (Finset α)) : Finset α := F.biUnion id

open scoped Classical in
/-- The sets $B\subseteq X$ which intersect every set in $\mathcal{F}$, yet contain none of them. -/
def goodSets (F : Finset (Finset α)) : Finset (Finset α) :=
  (groundSet F).powerset.filter fun B ↦ ∀ A ∈ F, (A ∩ B).Nonempty ∧ ¬ A ⊆ B

/--
Let $c>0$, and let $n$ be sufficiently large depending on $c$. Suppose that $\mathcal{F}$ is a
family of at most $c2^n$ many finite sets of size $n$. Let $X=\cup_{A\in \mathcal{F}}A$.

Must there exist $\gg_c 2^{\lvert X\rvert}$ many sets $B\subset X$ which intersect every set in
$\mathcal{F}$, yet contain none of them?

The existence of a single such $B$ is equivalent to $\mathcal{F}$ being $2$-chromatic (or having
property B), see [901](https://www.erdosproblems.com/901).

This is true, and a proof was given in the comment section by Koishi Chan.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1027.lean#L209"]
theorem erdos_1027 : answer(True) ↔ ∀ c : ℝ, 0 < c → ∃ δ : ℝ, 0 < δ ∧
    ∀ᶠ n : ℕ in atTop, ∀ (α : Type) [DecidableEq α] (F : Finset (Finset α)),
      (∀ A ∈ F, A.card = n) → (F.card : ℝ) ≤ c * 2 ^ n →
        δ * 2 ^ (groundSet F).card ≤ (goodSets F).card := by
  sorry

end Erdos1027
