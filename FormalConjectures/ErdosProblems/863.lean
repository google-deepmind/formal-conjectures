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
# Erdős Problem 863

*References:*
- [erdosproblems.com/863](https://www.erdosproblems.com/863)
- [erdosproblems.com/30](https://www.erdosproblems.com/30)
-/

open Filter

namespace Erdos863

/-- A set `A ⊆ ℕ` is said to be a `B₂[g]` set if for all `n`, the equation
`a + a' = n, a ≤ a', a, a' ∈ A` has at most `g` solutions. -/
def B2 (g : ℕ) (A : Set ℕ) : Prop :=
  ∀ n, {x : ℕ × ℕ | x.1 + x.2 = n ∧ x.1 ≤ x.2 ∧ x.1 ∈ A ∧ x.2 ∈ A}.encard ≤ g

/-- A set `A ⊆ ℕ` has at most `r` solutions to `n = a - b` for any `n`. -/
def Diff (r : ℕ) (A : Set ℕ) : Prop :=
  ∀ n ≥ 1, {x : ℕ × ℕ | x.1 = x.2 + n ∧ x.1 ∈ A ∧ x.2 ∈ A}.encard ≤ r

/-- The maximum size of a `B₂[r]` subset of `{1, …, N}`. -/
noncomputable def maxA (r N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ B2 r A ∧ A.card = k}

/-- The maximum size of a subset of `{1, …, N}` with at most `r` solutions to `n = a - b`
for any `n`. -/
noncomputable def maxB (r N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ Diff r A ∧ A.card = k}

/--
Let $r\geq 2$ and let $A\subseteq \{1,\ldots,N\}$ be a set of maximal size such that there are at most $r$ solutions to $n=a+b$ with $a\leq b$ for any $n$. (That is, $A$ is a $B_2[r]$ set.)

Similarly, let $B\subseteq \{1,\ldots,N\}$ be a set of maximal size such that there are at most $r$ solutions to $n=a-b$ for any $n$.

If $\lvert A\rvert\sim c_r N^{1/2}$ as $N\to \infty$ and $\lvert B\rvert \sim c_r' N^{1/2}$ as $N\to \infty$ then is it true that $c_r\neq c_r'$ for $r\geq 2$?
-/
@[category research open, AMS 5 11]
theorem erdos_863.parts.i : answer(sorry) ↔
    ∀ r ≥ 2, ∀ c c' : ℝ,
      Tendsto (fun N => (maxA r N : ℝ) / (N : ℝ) ^ (1 / 2 : ℝ)) atTop (nhds c) →
      Tendsto (fun N => (maxB r N : ℝ) / (N : ℝ) ^ (1 / 2 : ℝ)) atTop (nhds c') →
      c ≠ c' := by
  sorry

/--
Let $r\geq 2$ and let $A\subseteq \{1,\ldots,N\}$ be a set of maximal size such that there are at most $r$ solutions to $n=a+b$ with $a\leq b$ for any $n$. (That is, $A$ is a $B_2[r]$ set.)

Similarly, let $B\subseteq \{1,\ldots,N\}$ be a set of maximal size such that there are at most $r$ solutions to $n=a-b$ for any $n$.

If $\lvert A\rvert\sim c_r N^{1/2}$ as $N\to \infty$ and $\lvert B\rvert \sim c_r' N^{1/2}$ as $N\to \infty$ then is it true that $c_r'<c_r$?
-/
@[category research open, AMS 5 11]
theorem erdos_863.parts.ii : answer(sorry) ↔
    ∀ r ≥ 2, ∀ c c' : ℝ,
      Tendsto (fun N => (maxA r N : ℝ) / (N : ℝ) ^ (1 / 2 : ℝ)) atTop (nhds c) →
      Tendsto (fun N => (maxB r N : ℝ) / (N : ℝ) ^ (1 / 2 : ℝ)) atTop (nhds c') →
      c' < c := by
  sorry

/--
It is true that $c_1=c_1'$, and the classical bound on the size of Sidon sets (see [30]) implies $c_1=c_1'=1$.
-/
@[category research solved, AMS 5 11]
theorem erdos_863.variants.r_one :
    Tendsto (fun N => (Finset.maxSidonSubsetCard (Finset.Icc 1 N) : ℝ) /
      (N : ℝ) ^ (1 / 2 : ℝ)) atTop (nhds 1) ∧
    Tendsto (fun N => (maxB 1 N : ℝ) / (N : ℝ) ^ (1 / 2 : ℝ)) atTop (nhds 1) := by
  sorry

end Erdos863
