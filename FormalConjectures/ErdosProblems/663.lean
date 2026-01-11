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
# Erdős Problem 663
*Reference:* [erdosproblems.com/663](https://www.erdosproblems.com/663)
-/


namespace Erdos663

/--
Let $q(n,k)$ denote the least number coprime to all numbers in $[n+1, n+k]$.
-/

def q (n k : ℕ) : ℕ :=
    if hpos : n > 0 ∧ k > 0 then
    have h : ∃ q > 1, (∀ i ∈ Finset.Icc (n+1) (n+k), q.Coprime i) := by
        use (Nat.exists_infinite_primes (n+k+1)).choose
        have hspec := (Nat.exists_infinite_primes (n+k+1)).choose_spec
        simp only [Finset.mem_Icc]
        constructor
        linarith
        intros
        exact Nat.coprime_of_lt_prime (by linarith) (by linarith) hspec.right
    Nat.find h
    else 0

/--
Is it true that, if $k>1$ is fixed and $n$ is sufficiently large, we have
$q(n,k) < (1 + o(1)) \log n$?
-/
@[category research open, AMS 11]
theorem erdos_663 :
    answer(sorry) ↔ ∀ k > 1, ∀ b : ℕ, q (k := k) ≤ᶠ[.atTop] Nat.log b := by
    sorry

/--
The bound $q(n,k) < (1 + o(1)) k \log n$ is easy.
-/
@[category research solved, AMS 11]
theorem erdos_663.easy :
    answer(sorry) ↔ ∀ k > 1, ∀ b : ℕ, q (k := k) ≤ᶠ[.atTop] k * Nat.log b := by
    sorry

end Erdos663
