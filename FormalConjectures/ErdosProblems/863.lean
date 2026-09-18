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
public import FormalConjectures.ErdosProblems.«158»

/-!
# Erdős Problem 863

*References:*
- [erdosproblems.com/863](https://www.erdosproblems.com/863)
- [Er92c] Erdős, P., *Some of my forgotten problems in number theory*. Hardy-Ramanujan J. (1992),
  34-50.
- [CRT02] Cilleruelo, J., Ruzsa, I. and Trujillo, C., *Upper and lower bounds for finite
  $B_h[g]$ sequences*. J. Number Theory 97 (2002), 26-34.
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace Erdos863

/-- Every positive `n` has at most `r` representations as a difference `a - b` with
`a, b ∈ A` (the difference analogue of `Erdos158.B2`). -/
def IsDiffB2 (r : ℕ) (A : Set ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → {x : ℕ × ℕ | x.1 - x.2 = n ∧ x.1 ∈ A ∧ x.2 ∈ A}.encard ≤ r

/-- The maximum size of a `B₂[r]` subset of `{1, …, N}`. -/
noncomputable def sumMax (r N : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ Erdos158.B2 r A ∧ A.card = m}

/-- The maximum size of a subset of `{1, …, N}` in which every positive difference has at most
`r` representations. -/
noncomputable def diffMax (r N : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsDiffB2 r A ∧ A.card = m}

/--
Let $r \geq 2$ and let $A \subseteq \{1, \ldots, N\}$ be a set of maximal size such that there are
at most $r$ solutions to $n = a + b$ with $a \leq b$ for any $n$ (that is, $A$ is a $B_2[r]$ set).
Similarly, let $B \subseteq \{1, \ldots, N\}$ be a set of maximal size such that there are at most
$r$ solutions to $n = a - b$ for any $n$. If $|A| \sim c_r N^{1/2}$ and $|B| \sim c_r' N^{1/2}$ as
$N \to \infty$, then is it true that $c_r \neq c_r'$ for $r \geq 2$?

A question of Erdős, Berend and Freud [Er92c, p.39]. The answer is yes: an adaptation of the
Erdős–Turán argument gives $|B| \leq (\sqrt r + o(1)) N^{1/2}$, while Cilleruelo, Ruzsa and
Trujillo [CRT02] constructed $B_2[r]$ sets with
$|A| \geq \frac{r + \lfloor r/2 \rfloor}{\sqrt{r + 2 \lfloor r/2 \rfloor}} N^{1/2}$, so that
$c_r' \le \sqrt r < c_r$. See also `erdos_863.parts.ii`.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos863.lean#L1214"]
theorem erdos_863.parts.i : answer(True) ↔
    ∀ (r : ℕ), 2 ≤ r → ∀ (c c' : ℝ),
      ((fun N : ℕ => (sumMax r N : ℝ)) ~[atTop] fun N : ℕ => c * √N) →
      ((fun N : ℕ => (diffMax r N : ℝ)) ~[atTop] fun N : ℕ => c' * √N) → c ≠ c' := by
  sorry

/--
In the setting of `erdos_863.parts.i`, is it true that $c_r' < c_r$?

The answer is yes, by the bounds $c_r' \le \sqrt r < c_r$ described there.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos863.lean#L1207"]
theorem erdos_863.parts.ii : answer(True) ↔
    ∀ (r : ℕ), 2 ≤ r → ∀ (c c' : ℝ),
      ((fun N : ℕ => (sumMax r N : ℝ)) ~[atTop] fun N : ℕ => c * √N) →
      ((fun N : ℕ => (diffMax r N : ℝ)) ~[atTop] fun N : ℕ => c' * √N) → c' < c := by
  sorry

end Erdos863
