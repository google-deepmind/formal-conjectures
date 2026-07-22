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
# Erdős Problem 867

*References:*
- [erdosproblems.com/867](https://www.erdosproblems.com/867)
- [CoPh96] Coppersmith, Don and Phillips, Steven, *On a question of Erdős on subsequence sums*.
  SIAM J. Discrete Math. (1996), 173-177.
- [Fr93] Freud, R., *Adding numbers - on a problem of P. Erdős*. James Cook Mathematical
  Notes (1993), 6199-6202.
-/

open Filter

namespace Erdos867

/-- A finite set of naturals $A=\{a_1<\cdots<a_t\}$ is *consecutive-sum-free* if it has no
solutions to $a_i+a_{i+1}+\cdots+a_j\in A$ with $i<j$; equivalently, whenever an interval
$[m,n]$ contains at least two elements of $A$, the sum of the elements of $A$ lying in
$[m,n]$ is not itself an element of $A$. -/
def ConsecutiveSumFree (A : Finset ℕ) : Prop :=
  ∀ m n : ℕ, 2 ≤ (Finset.Icc m n ∩ A).card → (∑ a ∈ Finset.Icc m n ∩ A, a) ∉ A

/--
Is it true that if $A=\{a_1<\cdots <a_t\}\subseteq \{1,\ldots,N\}$ has no solutions to
\[a_i+a_{i+1}+\cdots+a_j\in A\]
then
\[\lvert A\rvert \leq \frac{N}{2}+O(1)?\]

In fact this problem is false. Freud [Fr93] constructed a sequence with density $\geq 19/36$.
The current best bounds are due to Coppersmith and Phillips [CoPh96], who prove that the
maximal size of such an $A$ satisfies
\[\frac{13}{24}N -O(1)\leq \lvert A\rvert \leq \left(\frac{2}{3}-\frac{1}{512}\right)N+\log N.\]
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos867.lean"]
theorem erdos_867 : answer(False) ↔
    ∃ C : ℝ, ∀ N : ℕ, ∀ A ⊆ Finset.Icc 1 N, ConsecutiveSumFree A →
      (A.card : ℝ) ≤ (N : ℝ) / 2 + C := by
  sorry

/--
Taking $A=(N/2,N]\cap \mathbb{N}$ shows $\lvert A\rvert \geq N/2-O(1)$ is possible.
-/
@[category research solved, AMS 5 11]
theorem erdos_867.variants.lower_bound :
    ∃ C : ℝ, ∀ N : ℕ, ∃ A ⊆ Finset.Icc 1 N, ConsecutiveSumFree A ∧
      ((N : ℝ) / 2 - C ≤ (A.card : ℝ)) := by
  sorry

/--
Adenwalla has observed that
\[\lvert A\rvert \leq (\tfrac{2}{3}+o(1))N.\]
-/
@[category research solved, AMS 5 11]
theorem erdos_867.variants.adenwalla (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Finset.Icc 1 N, ConsecutiveSumFree A →
      (A.card : ℝ) ≤ (2 / 3 + ε) * (N : ℝ) := by
  sorry

/--
Freud [Fr93] constructed a sequence with density $\geq 19/36$.
-/
@[category research solved, AMS 5 11]
theorem erdos_867.variants.freud :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∃ A ⊆ Finset.Icc 1 N, ConsecutiveSumFree A ∧
      (((19 / 36 : ℝ) - ε) * (N : ℝ) ≤ (A.card : ℝ)) := by
  sorry

/--
The current best bounds are due to Coppersmith and Phillips [CoPh96], who prove that the
maximal size of such an $A$ satisfies
\[\frac{13}{24}N -O(1)\leq \lvert A\rvert.\]
-/
@[category research solved, AMS 5 11]
theorem erdos_867.variants.coppersmith_phillips_lower_bound :
    ∃ C : ℝ, ∀ N : ℕ, ∃ A ⊆ Finset.Icc 1 N, ConsecutiveSumFree A ∧
      ((13 / 24 : ℝ) * (N : ℝ) - C ≤ (A.card : ℝ)) := by
  sorry

/--
The current best bounds are due to Coppersmith and Phillips [CoPh96], who prove that the
maximal size of such an $A$ satisfies
\[\lvert A\rvert \leq \left(\frac{2}{3}-\frac{1}{512}\right)N+\log N.\]
-/
@[category research solved, AMS 5 11]
theorem erdos_867.variants.coppersmith_phillips_upper_bound :
    ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Finset.Icc 1 N, ConsecutiveSumFree A →
      (A.card : ℝ) ≤ (2 / 3 - 1 / 512) * (N : ℝ) + Real.log (N : ℝ) := by
  sorry

end Erdos867
