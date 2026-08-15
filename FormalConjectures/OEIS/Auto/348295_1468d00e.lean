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

/--
A348295: The sequence $a(n) = \sum_{k=1}^n (-1)^{\lfloor k(\sqrt{2}-1) \rfloor}.$
-/
noncomputable def a (n : ℕ) : ℤ :=
  Finset.sum (Finset.Ioc 0 n) fun k : ℕ =>
    let k_real : ℝ := k
    let exponent_real : ℝ := k_real * (Real.sqrt 2 - 1)
    let exponent_int : ℤ := Int.floor exponent_real
    -- The exponent $\lfloor k(\sqrt{2}-1) \rfloor$ is non-negative for $k \ge 1$.
    (-1 : ℤ) ^ exponent_int.toNat

theorem a_zero : a 0 = 0 := by
  rfl

/--
Conjecture (1) for A348295: The sequence is unbounded from above.
Moreover, it seems that the earliest occurrence of m is A000129(m) for even m
and A001333(m) for odd m (this has been confirmed for m <= 32 by Chai Wah Wu,
Oct 21 2021). See A084068 for the conjectured indices of records.
-/
theorem oeis_348295_conjecture_0 : ∀ (M : ℤ), ∃ (n : ℕ), a n > M := by sorry
