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
# Erdős Problem 863

*Reference:* [erdosproblems.com/863](https://www.erdosproblems.com/863)

A problem of Erdős [Er92c], first formulated in conversation with Berend, and later
independently reformulated with Freud. It is known that $c_1 = c_1' = 1$ (the classical
bound on Sidon sets).

[Er92c] Erdős, P., *Some of my favourite problems in various branches of combinatorics*,
Matematiche (Catania) 47 (1992), no. 2, 231–240.
-/

open Classical Finset Filter

open scoped Topology

namespace Erdos863

/-- The number of representations of $n$ as $a + b$ with $a \leq b$ and $a, b \in S$. -/
noncomputable def sumRepCount (S : Finset ℕ) (n : ℕ) : ℕ :=
  S.sum (fun a => (S.filter (fun b => a ≤ b ∧ a + b = n)).card)

/-- $S$ is a $B_2[r]$ set if every $n$ has at most $r$ representations
    as $a + b$ with $a \leq b$, $a, b \in S$. -/
def IsB2r (r : ℕ) (S : Finset ℕ) : Prop :=
  ∀ n : ℕ, sumRepCount S n ≤ r

/-- The maximum cardinality of a $B_2[r]$ subset of $\{1, \ldots, N\}$. -/
noncomputable def maxB2rSize (r : ℕ) (N : ℕ) : ℕ :=
  ((Icc 1 N).powerset.filter (fun S => IsB2r r S)).sup Finset.card

/-- The number of representations of a positive integer $n$ as a difference $a - b = n$
    (equivalently, $a = b + n$) with $a, b \in S$. -/
noncomputable def diffRepCount (S : Finset ℕ) (n : ℕ) : ℕ :=
  S.sum (fun b => (S.filter (fun a => a = b + n)).card)

/-- $S$ is difference-$r$-bounded if every nonzero difference has at most $r$
    representations as $a - b$ with $a, b \in S$. -/
def IsDiffBounded (r : ℕ) (S : Finset ℕ) : Prop :=
  ∀ n : ℕ, n > 0 → diffRepCount S n ≤ r

/-- The maximum cardinality of a difference-$r$-bounded subset of $\{1, \ldots, N\}$. -/
noncomputable def maxDiffBoundedSize (r : ℕ) (N : ℕ) : ℕ :=
  ((Icc 1 N).powerset.filter (fun S => IsDiffBounded r S)).sup Finset.card

/--
Erdős Problem 863, weak form [Er92c]:

If the limits $c_r = \lim_{N \to \infty} f_r^+(N) / \sqrt{N}$ (maximum $B_2[r]$ set size)
and $c_r' = \lim_{N \to \infty} f_r^-(N) / \sqrt{N}$ (maximum difference-$r$-bounded set
size) both exist, then $c_r \neq c_r'$ for $r \geq 2$.
-/
@[category research open, AMS 5 11]
theorem erdos_863 : answer(sorry) ↔
    ∀ (r : ℕ), r ≥ 2 → ∀ (c c' : ℝ),
    Tendsto (fun N => (maxB2rSize r N : ℝ) / Real.sqrt (N : ℝ)) atTop (nhds c) →
    Tendsto (fun N => (maxDiffBoundedSize r N : ℝ) / Real.sqrt (N : ℝ)) atTop (nhds c') →
    c ≠ c' := by
  sorry

/--
Erdős Problem 863, strong form [Er92c]:

If the limits $c_r = \lim_{N \to \infty} f_r^+(N) / \sqrt{N}$ (maximum $B_2[r]$ set size)
and $c_r' = \lim_{N \to \infty} f_r^-(N) / \sqrt{N}$ (maximum difference-$r$-bounded set
size) both exist, then $c_r' < c_r$ for $r \geq 2$.
-/
@[category research open, AMS 5 11]
theorem erdos_863.variants.strong : answer(sorry) ↔
    ∀ (r : ℕ), r ≥ 2 → ∀ (c c' : ℝ),
    Tendsto (fun N => (maxB2rSize r N : ℝ) / Real.sqrt (N : ℝ)) atTop (nhds c) →
    Tendsto (fun N => (maxDiffBoundedSize r N : ℝ) / Real.sqrt (N : ℝ)) atTop (nhds c') →
    c' < c := by
  sorry

end Erdos863
