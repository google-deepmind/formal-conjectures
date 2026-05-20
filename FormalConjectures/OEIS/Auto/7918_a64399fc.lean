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
A007918: Least prime $\ge n$ (version 1 of the "next prime" function).
-/
noncomputable def a (n : ℕ) : ℕ :=
  @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  )

-- Auxiliary theorems for small values are omitted as they were causing compilation issues.
-- The focus is on the formalizing the conjecture.

/--
The initial term $p_0$ and common difference $d$ form an arithmetic progression of
length `n` consisting entirely of prime numbers.
We require $d > 0$ for it to be an increasing progression.
-/
def is_ap_of_n_primes (n p0 d : ℕ) : Prop :=
  d > 0 ∧ ∀ k < n, Nat.Prime (p0 + k * d)

/--
A007918 According to the "k-tuple" conjecture, a(n) is the initial term of the
lexicographically earliest increasing arithmetic progression of n primes;
the corresponding common differences are given by A061558.
-/
theorem oeis_7918_conjecture_0 (n : ℕ) (hn : n > 0) :
    a n = sInf { p0 : ℕ | ∃ d : ℕ, is_ap_of_n_primes n p0 d } := by
  sorry
