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

import FormalConjecturesUtil

/-!
# Partial sums of $(-1)^{k - \Omega(k)}$

The sequence $a(n) = \sum_{k=1}^n (-1)^{k - \Omega(k)}$, where $\Omega(k)$ is the total number of
prime factors of $k$ counted with multiplicity.

*References:*
- [A212496](https://oeis.org/A212496)
-/

namespace OeisA212496

/-- Total number of prime factors of $k$ counted with multiplicity, $\Omega(k)$. -/
def bigOmega (k : ℕ) : ℕ :=
  k.primeFactorsList.length

/-- $a(n) = \sum_{k=1}^n (-1)^{k - \Omega(k)}$. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 n, if (k + bigOmega k) % 2 = 0 then 1 else -1

/-- Auxiliary sequence $b(n) = \sum_{k=1}^n \frac{(-1)^{k - \Omega(k)}}{k}$. -/
noncomputable def b (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (if (k + bigOmega k) % 2 = 0 then (1 : ℝ) else -1) / (k : ℝ)

@[category test, AMS 11]
theorem a_1 : a 1 = -1 := by native_decide

@[category test, AMS 11]
theorem a_2 : a 2 = -2 := by native_decide

@[category test, AMS 11]
theorem a_3 : a 3 = -1 := by native_decide

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by native_decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by native_decide

/--
"On May 16 2012, Zhi-Wei Sun conjectured that $a(n)$ is positive for each $n > 4$."
- _Zhi-Wei Sun_, May 19 2012
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 4 < n) : 0 < a n := by
  sorry

/--
"Moreover, he guessed that $a(n) > \sqrt{n}$ for any $n > 324$ (and also
$a(n) < \sqrt{n}\log(\log(n))$ for $n > 5892$)."
- _Zhi-Wei Sun_, May 19 2012
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) :
    (324 < n → Real.sqrt (n : ℝ) < (a n : ℝ)) ∧
    (5892 < n → (a n : ℝ) < Real.sqrt (n : ℝ) * Real.log (Real.log (n : ℝ))) := by
  sorry

/--
"Sun also conjectured that $b(n) = \sum_{k=1}^n (-1)^{k-\Omega(k)}/k < 0$ for all $n=1,2,3,\dots$"
- _Zhi-Wei Sun_, May 19 2012
-/
@[category research open, AMS 11]
theorem conjecture3 (n : ℕ) (hn : 0 < n) : b n < 0 := by
  sorry

/--
"Moreover, he guessed that $b(n) < -1/\sqrt{n}$ for all $n > 1$, and
$b(n) > -\log(\log(n))/\sqrt{n}$ for $n > 2008$."
- _Zhi-Wei Sun_, May 19 2012
-/
@[category research open, AMS 11]
theorem conjecture4 (n : ℕ) :
    (1 < n → b n < -1 / Real.sqrt (n : ℝ)) ∧
    (2008 < n → -Real.log (Real.log (n : ℝ)) / Real.sqrt (n : ℝ) < b n) := by
  sorry

end OeisA212496
