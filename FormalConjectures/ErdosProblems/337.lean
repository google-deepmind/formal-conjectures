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
# Erdős Problem 337

*Reference:* [erdosproblems.com/337](https://www.erdosproblems.com/337)

Is it true that for an additive basis $A$ of density $o(N)$, the ratio
$|(A+A) \cap \{1,\ldots,N\}| / |A \cap \{1,\ldots,N\}|$ tends to infinity?
The answer is no, as shown by Turjányi.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[ErGr80b] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory II*. (1980).

[Tu84] Turjányi, S., *On a question of Erdős and Graham*. (1984).

[RT85] Ruzsa, I.Z. and Turjányi, S., *A note on additive bases*. (1985).
-/

open Filter

open scoped Topology BigOperators

namespace Erdos337

/-- The sumset $A + A = \{a + b : a, b \in A\}$. -/
def sumset (A : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ a ∈ A, ∃ b ∈ A, n = a + b}

/-- The set of all sums of exactly $k$ elements from $A$ (with repetition). -/
def exactSumset (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n : ℕ | ∃ (f : Fin k → ℕ), (∀ i, f i ∈ A) ∧ n = ∑ i, f i}

/-- $A \subseteq \mathbb{N}$ is an additive basis of order $r$ if every sufficiently large
natural number is the sum of at most $r$ elements from $A$. -/
def IsAdditiveBasis (A : Set ℕ) (r : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ k ≤ r, n ∈ exactSumset A k

/-- Count of elements of $A$ in $\{0, 1, \ldots, N\}$. -/
noncomputable def countInRange (A : Set ℕ) (N : ℕ) : ℕ :=
  haveI : DecidablePred (· ∈ A) := Classical.decPred _
  ((Finset.range (N + 1)).filter (· ∈ A)).card

/--
Erdős Problem 337 [ErGr80] [ErGr80b]:

Let $A \subseteq \mathbb{N}$ be an additive basis (of any finite order) such that
$|A \cap \{1, \ldots, N\}| = o(N)$. Is it true that
$$\lim_{N \to \infty} \frac{|(A+A) \cap \{1, \ldots, N\}|}{|A \cap \{1, \ldots, N\}|} = \infty?$$

The answer is no. A counterexample was provided by Turjányi [Tu84].
This was generalised (replacing $A+A$ by the $h$-fold sumset $hA$ for any
$h \geq 2$) by Ruzsa and Turjányi [RT85].
-/
@[category research solved, AMS 11]
theorem erdos_337 : answer(False) ↔
    ∀ (A : Set ℕ),
      (∃ r : ℕ, IsAdditiveBasis A r) →
      Tendsto (fun N => (countInRange A N : ℝ) / (N : ℝ)) atTop (nhds 0) →
      Tendsto (fun N => (countInRange (sumset A) N : ℝ) /
          (countInRange A N : ℝ)) atTop atTop := by
  sorry

end Erdos337
