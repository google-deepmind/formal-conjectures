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

open Nat Int Rat Finset

/-- The $n$-th harmonic number $\sum_{k=1}^n 1/k$, as a rational number. -/
noncomputable def harmonic_number (n : ℕ) : ℚ :=
  (Finset.range n).sum fun k => (1 : ℚ) / (((k + 1) : ℕ) : ℚ)

/--
A309391: $a(n) = \gcd(n, A064169(n-2))$ for $n > 2$.
$A064169(m)$ is the numerator minus the denominator of the $m$-th harmonic number $H_m$.
The formula used is $a(n) = \gcd(n, |\text{num}(H_{n-2}) - \text{den}(H_{n-2})|)$.
-/
noncomputable def A309391 (n : ℕ) : ℕ :=
  -- The sequence is usually indexed starting from n=3, but we define it for n:ℕ.
  -- For the terms n=0,1,2, we can assign a default value of 0, as they are not part of the sequence.
  -- The OEIS listing starts at index 3.
  if n < 3 then 0 else
  let m : ℕ := n - 2
  let r : ℚ := harmonic_number m
  -- r.num is ℤ, r.den is ℕ. We compute the absolute difference of the numerator and denominator.
  let num_minus_den : ℤ := r.num - (r.den : ℤ)
  Nat.gcd n num_minus_den.natAbs


theorem a_three : A309391 3 = 3 := by
  push_cast [A309391]
  norm_num[harmonic_number]

theorem a_four : A309391 4 = 1 := by
  delta A309391
  norm_num[harmonic_number]

theorem a_five : A309391 5 = 5 := by
  norm_num [A309391]
  norm_num only[harmonic_number,id]

theorem a_six : A309391 6 = 1 := by
  push_cast[A309391]
  norm_num only[harmonic_number]


/--
A309391 Conjecture: for n > 2, if a(n) = n, then n is a prime.
-/
theorem A309391_conjecture (n : ℕ) (h_n : n > 2) :
  A309391 n = n → Nat.Prime n := by sorry
