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
# Erdős Problem 364

*Reference:* [erdosproblems.com/364](https://www.erdosproblems.com/364)
-/

open Nat

/-- There is no consecutive triple of powerful numbers. -/
@[category research open, AMS 11]
theorem erdos_364 :
    ¬ ∃ (n : ℕ), Powerful n ∧ Powerful (n + 1) ∧ Powerful (n + 2) := by
  sorry

/--
Erdős [Er76d] conjectured a stronger statement: if $n_k$ is the $k$th powerful number,
then $n_{k+2} - n_k > n_k^c$ for some constant $c > 0$.

[Er76d] Erdős, P., Problems and results on number theoretic properties of consecutive integers and related questions. Proceedings of the Fifth Manitoba Conference on Numerical Mathematics (Univ. Manitoba, Winnipeg, Man., 1975) (1976), 25-44.
-/
@[category research open, AMS 11]
theorem erdos_364.variants.strong :
    ∃ (c : ℝ) (h : c > 0), ∀ (k : ℕ),
    Nat.nth Powerful (k + 2) - Nat.nth Powerful k > (Nat.nth Powerful k : ℝ) ^ c := by
  sorry

/--
There is no quadruple of powerful numbers, since at least one of the four numbers must be
$2 \pmod{4}$, which cannot be powerful (since $2$ divides it, but $2^2$ does not).
-/
@[category undergraduate, AMS 11]
theorem erdos_364.variants.weak :
    ¬ ∃ (n : ℕ), Powerful n ∧ Powerful (n + 1) ∧ Powerful (n + 2) ∧ Powerful (n + 3) := by
  intro h
  obtain ⟨n, hn⟩ := h
  have h2mod4 : n % 4 = 2 ∨ (n + 1) % 4 = 2 ∨ (n + 2) % 4 = 2 ∨ (n + 3) % 4 = 2 := by omega
  rcases h2mod4 with (_|_|_|_) <;>
  simp_all [not_full_of_prime_mod_prime_sq _ 1 (Nat.prime_two)]
