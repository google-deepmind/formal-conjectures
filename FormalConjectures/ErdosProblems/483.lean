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

/-!
# Erdős Problem 483

*References:*
- [erdosproblems.com/483](https://www.erdosproblems.com/483)
- [Er61] Erdős, Paul, *Some unsolved problems*. Magyar Tud. Akad. Mat. Kutató Int. Közl.
  (1961), 221-254, p.233, Problem 20.
-/

@[expose] public section

namespace Erdos483

/-- A monochromatic solution to $a+b=c$ in $\{1,\ldots,N\}$.
Index $i$ represents $i+1$, and equal summands are allowed. -/
def HasTriple {k N : ℕ} (χ : Fin N → Fin k) : Prop :=
  ∃ a b c : Fin N, (a.val + 1) + (b.val + 1) = c.val + 1 ∧
    χ a = χ b ∧ χ b = χ c

/-- Every colouring of $\{1,\ldots,N\}$ with at most $k$ colours has a Schur triple. -/
def Forces (k N : ℕ) : Prop := ∀ χ : Fin N → Fin k, HasTriple χ

/-- The first one-colour forcing interval is $\{1,2\}$, using $1+1=2$. -/
@[category test, AMS 5 11]
theorem forces_one_two : Forces 1 2 := by
  unfold Forces HasTriple
  decide

/-- The interval $\{1\}$ has no Schur triple. -/
@[category test, AMS 5 11]
theorem not_forces_one_one : ¬ Forces 1 1 := by
  unfold Forces HasTriple
  decide

/--
Let $f(k)$ be the minimal $N$ such that if $\{1,\ldots,N\}$ is $k$-coloured then
there is a monochromatic solution to $a+b=c$. Estimate $f(k)$. In particular, is it true
that $f(k) < c^k$ for some constant $c>0$?

The exponential bound is stated directly: for every positive number of colours, there is
a forcing interval of length strictly below $c^k$. This is equivalent to the bound on the
least forcing threshold and avoids choosing a default value for that threshold.
-/
@[category research open, AMS 5 11]
theorem erdos_483 : answer(sorry) ↔
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
      ∃ N : ℕ, (N : ℝ) < C ^ k ∧ Forces k N := by
  sorry

end Erdos483
