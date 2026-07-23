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
# Erdős Problem 1023

*References:*
- [erdosproblems.com/1023](https://www.erdosproblems.com/1023)
- [Er71, p.105] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
-/

open Filter

open scoped Asymptotics

namespace Erdos1023

/--
A family `S` of finite sets is union-free when no set in `S` is the union of other
members of `S`.
-/
def IsUnionFree {α : Type*} [DecidableEq α] (S : Finset (Finset α)) : Prop :=
  ∀ A ∈ S, ∀ T ⊆ S.erase A, T.Nonempty → T.sup id ≠ A

/--
`F n` is the maximal size of a family of subsets of $\{1,\ldots,n\}$ such that no set in this
family is the union of other members of the family.
-/
noncomputable def F (n : ℕ) : ℕ :=
  sSup {m | ∃ S ⊆ (Finset.Icc 1 n).powerset, IsUnionFree S ∧ S.card = m}

/--
Let $F(n)$ be the maximal size of a family of subsets of $\{1,\ldots,n\}$ such that no set in
this family is the union of other members of the family. Is it true that there is a constant
$c>0$ such that
\[F(n)\sim c \frac{2^n}{n^{1/2}}?\]

Hunter observes in the comments that this follows from the solution to [447], which implies
$F(n)\sim \binom{n}{n/2}$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1023.lean"]
theorem erdos_1023 : answer(True) ↔
    ∃ c : ℝ, 0 < c ∧
      ((fun n : ℕ => (F n : ℝ)) ~[atTop]
        (fun n : ℕ => c * 2 ^ n / (n : ℝ) ^ (1 / 2 : ℝ))) := by
  sorry

/--
Erdős and Kleitman proved in unpublished work that
\[F(n)\asymp \frac{2^n}{n^{1/2}}.\]
([Er71] has an exponent of $3/2$, but this is presumably a typo.)
-/
@[category research solved, AMS 5]
theorem erdos_1023.variants.erdos_kleitman :
    (fun n : ℕ => (F n : ℝ)) =Θ[atTop] (fun n : ℕ => (2 : ℝ) ^ n / (n : ℝ) ^ (1 / 2 : ℝ)) := by
  sorry

/--
Hunter observes in the comments that this follows from the solution to [447], which implies
$F(n)\sim \binom{n}{n/2}$.
-/
@[category research solved, AMS 5]
theorem erdos_1023.variants.hunter :
    (fun n : ℕ => (F n : ℝ)) ~[atTop] (fun n : ℕ => (n.choose (n / 2) : ℝ)) := by
  sorry

end Erdos1023
