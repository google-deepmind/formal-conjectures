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

import FormalConjectures.Util.ProblemImports

/-!
# The curling Number Conjecture

*Reference:* [arxiv/0912.2382](https://arxiv.org/abs/0912.2382) **The Curling Number Conjecture** by *Benjamin Chaffin and N. J. A. Sloane*
-/

/--
The curling number

Let $S$ be a finite nonempty sequence of integers. By grouping adjacent terms, it is always possible
to write it as $S = X Y Y . . . Y = X Y^k$, where $X$ and $Y$ are sequences of integers and $Y$ is nonempty
($X$ is allowed to be the empty sequence $∅$). There may be several ways to do this: choose the one
that maximizes the value of $k$: this $k$ is the curling number of $S$, denoted by $k S$.
-/
private noncomputable def k (S : List ℤ) : ℕ :=
  sSup {k : ℕ | ∃ X Y  : List ℤ, Y ≠ [] ∧ S = X  ++ (List.replicate k Y).flatten}


/--
One starts with any initial
sequence of integers $S₀$, and extends it by repeatedly appending the curling number of the current
sequence.
-/
private noncomputable def S (S₀ : List ℤ) (n : ℕ) : List ℤ :=
  match n with
  | 0 => S₀
  | n + 1 => (S S₀ n) ++ [Int.ofNat (k (S S₀ n))]

/--
The sequence will eventually reach $1$.
-/
@[category research open, AMS 11]
theorem curling_number_conjecture (S₀ : List ℤ) (h : S₀ ≠ []) : ∃ m, k (S S₀ m) = 1 := by
  sorry
