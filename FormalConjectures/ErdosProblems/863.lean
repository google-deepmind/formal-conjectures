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

open Asymptotics Filter Finset

open scoped Topology

namespace Erdos863

/--
A set `A` is a $B_2[r]$ set if for every `n` there are at most `r` solutions of `n = a + b`
with `a ≤ b` and `a, b ∈ A`.
-/
def IsB2 (r : ℕ) (A : Set ℕ) : Prop :=
  ∀ n, {x : ℕ × ℕ | x.1 + x.2 = n ∧ x.1 ≤ x.2 ∧ x.1 ∈ A ∧ x.2 ∈ A}.encard ≤ r

/--
A set `A` has at most `r` difference representations of every positive `n`, i.e. at most `r`
solutions of `n = a - b` with `a, b ∈ A`.
-/
def IsDiffBounded (r : ℕ) (A : Set ℕ) : Prop :=
  ∀ n > 0, {x : ℕ × ℕ | x.1 ∈ A ∧ x.2 ∈ A ∧ x.1 = x.2 + n}.encard ≤ r

/-- Maximum size of a $B_2[r]$ subset of `{1, …, N}`. -/
noncomputable def maxB2 (r N : ℕ) : ℕ :=
  sSup ((·.card) '' {A : Finset ℕ | A ⊆ Icc 1 N ∧ IsB2 r (A : Set ℕ)})

/-- Maximum size of a subset of `{1, …, N}` with at most `r` difference representations. -/
noncomputable def maxDiff (r N : ℕ) : ℕ :=
  sSup ((·.card) '' {A : Finset ℕ | A ⊆ Icc 1 N ∧ IsDiffBounded r (A : Set ℕ)})

/-- Normalised size `max / N^{1/2}`. -/
noncomputable def normalised (f : ℕ → ℕ) (N : ℕ) : ℝ :=
  (f N : ℝ) / (N : ℝ) ^ (1 / 2 : ℝ)

/--
Let $r\geq 2$ and let $A\subseteq \{1,\ldots,N\}$ be a set of maximal size such that there are at
most $r$ solutions to $n=a+b$ with $a\leq b$ for any $n$. (That is, $A$ is a $B_2[r]$ set.)

Similarly, let $B\subseteq \{1,\ldots,N\}$ be a set of maximal size such that there are at most
$r$ solutions to $n=a-b$ for any $n$.

If $\lvert A\rvert\sim c_rN^{1/2}$ as $N\to \infty$ and $\lvert B\rvert \sim c_r'N^{1/2}$ as
$N\to \infty$ then is it true that $c_r\neq c_r'$ for $r\geq 2$?
-/
@[category research open, AMS 5 11]
theorem erdos_863.parts.i : answer(sorry) ↔
    ∀ r ≥ 2, ∀ c c' : ℝ,
      Tendsto (normalised (maxB2 r)) atTop (nhds c) →
      Tendsto (normalised (maxDiff r)) atTop (nhds c') →
      c ≠ c' := by
  sorry

/--
Is it true that $c_r'<c_r$?
-/
@[category research open, AMS 5 11]
theorem erdos_863.parts.ii : answer(sorry) ↔
    ∀ r ≥ 2, ∀ c c' : ℝ,
      Tendsto (normalised (maxB2 r)) atTop (nhds c) →
      Tendsto (normalised (maxDiff r)) atTop (nhds c') →
      c' < c := by
  sorry

/--
It is true that $c_1=c_1'$, and the classical bound on the size of Sidon sets implies
$c_1=c_1'=1$.
-/
@[category research solved, AMS 5 11]
theorem erdos_863.variants.r_one :
    Tendsto (normalised (maxB2 1)) atTop (nhds 1) ∧
      Tendsto (normalised (maxDiff 1)) atTop (nhds 1) := by
  sorry

end Erdos863
