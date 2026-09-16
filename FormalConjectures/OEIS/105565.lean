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
# Indicator sequence for 5 Fibonacci numbers with n digits

$a(n) = 1$ if exactly 5 Fibonacci numbers exist with exactly $n$ digits, otherwise $0$.
For the partial sums $S(n) = \sum_{k=1}^n a(k)$, it is conjectured that
$\beta-2 < S(n)-\alpha n < \beta-1$, where $\alpha = \log(10)/\log(\phi) - 4$
and $\beta = \log(5)/(2\log(\phi)) - 1$.

*References:*
- [A105565](https://oeis.org/A105565)
-/

namespace OeisA105565

open Nat Finset Real

/--
The primary defining sequence `a`.
$a(n) = 1$ if exactly 5 Fibonacci numbers exist with exactly $n$ digits, otherwise $0$.
That is, $a(n) = 1$ if the number of indices $k \in \mathbb{N}$ such that
$10^{n-1} \le \mathrm{fib}(k) < 10^n$ is 5.
-/
def a (n : ℕ) : ℕ :=
  if n > 0 then
    -- $n$ is the number of digits, so $n \ge 1$.
    let lowerBound : ℕ := 10 ^ (n - 1)
    let upperBound : ℕ := 10 ^ n

    -- A safe upper bound for the index $k$.
    let maxK : ℕ := 5 * n + 10

    -- Count indices $k$ in range $[0, maxK)$ such that $\mathrm{fib}(k)$ has $n$ digits.
    let count : ℕ :=
      (filter (fun k => lowerBound ≤ Nat.fib k ∧ Nat.fib k < upperBound) (range maxK)).card

    if count = 5 then 1 else 0
  else
    0

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by decide

/-- The golden ratio $\phi = (1 + \sqrt{5})/2$. -/
noncomputable def phi : Real := goldenRatio

/-- The constant $\alpha = \log(10)/\log(\phi) - 4$. -/
noncomputable def alphaConst : Real := Real.log 10 / Real.log phi - 4

/-- The constant $\beta = \log(5)/(2\log(\phi)) - 1$. -/
noncomputable def betaConst : Real := Real.log 5 / (2 * Real.log phi) - 1

/-- The partial sum $S(n) = \sum_{k=1}^n a(k)$. -/
noncomputable def s (n : ℕ) : Real :=
  (Finset.Icc 1 n).sum (fun k => (a k : Real))

/--
Conjecture: $\beta-2 < S(n)-\alpha n < \beta-1$.
The constants $\alpha$ and $\beta$ are as defined in the formula section.

Solved by OpenAI Codex, prompted by Adam Haig. A complete Lean 4 proof is
linked by the `formal_proof` attribute below.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/HaigAd/formal-conjectures/blob/327b99914ce787ab41c67ba645626982e15b0124/FormalConjectures/OEIS/105565.lean#L595"]
theorem conjecture (n : ℕ) (hn : 1 ≤ n) :
    betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1 := by
  sorry

end OeisA105565
