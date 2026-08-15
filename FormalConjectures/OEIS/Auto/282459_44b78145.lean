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

open Nat

/--
A282459: Number of composite numbers of the form $2n - 2^k + 1$ ($k > 0, 2^k < 2n + 1$).
-/
def A282459 (n : ℕ) : ℕ :=
  -- The upper bound for k is $\lfloor \log_2(2n+1) \rfloor$.
  let upper_k : ℕ := log 2 (2 * n + 1)
  -- The set of $k$ values is $1 \le k \le \lfloor \log_2(2n+1) \rfloor$.
  let s := Finset.Icc 1 upper_k

  -- A natural number $m$ is composite if $m > 1$ and $m$ is not a prime.
  -- We must use Nat.Prime explicitly in this context.
  let is_composite (m : ℕ) : Prop := 1 < m ∧ ¬ Nat.Prime m

  -- The value we are checking for compositeness. The subtraction is safe since $2^k \le 2n+1$.
  -- The subtraction is safe because $k \le \log_2(2n+1)$, which implies $2^k \le 2n+1$.
  let seq_val (k : ℕ) : ℕ := 2 * n + 1 - 2 ^ k

  -- We count how many $k$ in the set $s$ make `seq_val k` composite.
  Finset.card (Finset.filter (fun k : ℕ => is_composite (seq_val k)) s)

/--
It is conjectured that `A282459 n > 0` for all `n > 52`.
-/
theorem oeis_282459_conjecture_0 : ∀ n : ℕ, n > 52 → A282459 n > 0 :=
  by sorry
