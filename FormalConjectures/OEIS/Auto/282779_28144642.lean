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

open Nat Set Classical

/--
A282779: Period of cubes mod $n$.
The $n$-th term $a(n)$ is the smallest positive integer $T$ such that $\forall k \in \mathbb{N}$, $(k+T)^3 \equiv k^3 \pmod n$.
-/
noncomputable def A282779 (n : ℕ) : ℕ :=
  if n = 0 then 0 -- Handle the non-sequence index n=0
  else
    -- sInf computes the infimum of the set, which is the minimum since ℕ is well-ordered.
    sInf { T : ℕ | 0 < T ∧ ∀ k : ℕ, (k + T) ^ 3 % n = k ^ 3 % n }

/--
The length of the minimal positive period of the sequence $k^p \pmod n$.
$a_p(n) = \min \{ T \in \mathbb{N}^+ \mid \forall k \in \mathbb{N}, (k+T)^p \equiv k^p \pmod n \}$.
-/
noncomputable def period_of_power_mod (p n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    sInf { T : ℕ | 0 < T ∧ ∀ k : ℕ, (k + T) ^ p % n = k ^ p % n }

/--
oeis_282779_conjecture_0: Conjecture: let a_p(n) be the length of the period of the sequence k^p mod n where p is a prime,
then a_p(n) = n/p if n == 0 (mod p^2) else a_p(n) = n.
-/
theorem oeis_282779_conjecture_0 (p n : ℕ) (hp : Nat.Prime p) (hn : n > 0) :
    period_of_power_mod p n = if p ^ 2 ∣ n then n / p else n := by
  sorry
