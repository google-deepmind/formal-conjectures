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
# Numerator - denominator in $n$-th harmonic number

$a(n) = \text{numerator}(H_n) - \text{denominator}(H_n)$, where
$H_n = 1 + 1/2 + \dots + 1/n$.

*References:*
- [A064169](https://oeis.org/A064169)-/

namespace OeisA64169

/-- The $n$-th harmonic number $H_n = \sum_{k=1}^n \frac{1}{k}$ as a rational number. -/
def H (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℚ)

/-- $a(n) = \text{numerator}(H_n) - \text{denominator}(H_n)$. -/
def a (n : ℕ) : ℤ :=
  (H n).num - (H n).den

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  decide +native

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  decide +native

@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by
  decide +native

@[category test, AMS 11]
theorem a_4 : a 4 = 13 := by
  decide +native

@[category test, AMS 11]
theorem a_5 : a 5 = 77 := by
  decide +native

/--
"Conjecture: for $n > 2$, $n$ divides $a(n-2)$ if and only if $n$ is a prime.
Checked up to 20000. - _Amiram Eldar_ and _Thomas Ordowski_, Jul 27 2019"-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 2 < n) : (n : ℤ) ∣ a (n - 2) ↔ n.Prime := by
  sorry

end OeisA64169
