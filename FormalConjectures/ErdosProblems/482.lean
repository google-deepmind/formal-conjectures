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
# Erdős Problem 482

*Reference:* [erdosproblems.com/482](https://www.erdosproblems.com/482)

Define a sequence by $a_1 = 1$ and $a_{n+1} = \lfloor \sqrt{2} \cdot (a_n + 1/2) \rfloor$ for
$n \geq 1$. Graham and Pollak [GrPo70] showed that the difference $a_{2n+1} - 2 \cdot a_{2n-1}$
equals the $n$th digit in the binary expansion of $\sqrt{2}$.

Erdős and Graham [ErGr80, p.96] asked for similar results for $\theta = \sqrt{m}$ and other
algebraic numbers. This was addressed by the generalisations of Stoll [St05, St06].

[GrPo70] Graham, R.L. and Pollak, H.O., _Note on a nonlinear recurrence related to $\sqrt{2}$_,
Mathematics Magazine 43 (1970), 143–145.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathématique (1980).

[St05] Stoll, T., _On families of nonlinear recurrences related to digits_, J. Integer Seq. 8
(2005).

[St06] Stoll, T., _A fancy way to obtain the binary digits of certain irrational numbers_,
Amer. Math. Monthly 113 (2006), 323–328.
-/

namespace Erdos482

/-- The Graham–Pollak sequence: $a(1) = 1$, $a(n+1) = \lfloor \sqrt{2} \cdot (a(n) + 1/2) \rfloor$.
This sequence is 1-indexed; $a(0)$ is a dummy value. -/
noncomputable def grahamPollakSeq : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => ⌊Real.sqrt 2 * ((grahamPollakSeq (n + 1) : ℝ) + 1 / 2)⌋

/-- The $n$th binary digit (0-indexed) of a nonnegative real number $x$.
Position 0 is the integer-part bit. Equals $\lfloor x \cdot 2^n \rfloor \bmod 2$. -/
noncomputable def binaryDigit (x : ℝ) (n : ℕ) : ℤ :=
  ⌊x * (2 : ℝ) ^ n⌋ % 2

/--
Erdős Problem 482 (Graham–Pollak theorem) [ErGr80, p.96]:

Define a sequence by $a_1 = 1$ and $a_{n+1} = \lfloor \sqrt{2} \cdot (a_n + 1/2) \rfloor$ for
$n \geq 1$. Then the difference $a_{2n+1} - 2 \cdot a_{2n-1}$ equals the $n$th digit in the
binary expansion of $\sqrt{2}$ ($n \geq 1$, 1-indexed).

The result for $\sqrt{2}$ was proved by Graham and Pollak [GrPo70]. Erdős and Graham asked for
similar results for $\theta = \sqrt{m}$ and other algebraic numbers; this was addressed by the
generalisations of Stoll [St05, St06].

Formalised using 0-indexed binary digits (position 0 = integer part) and shifting the index to
avoid natural-number subtraction: for all $n$,
$a(2n+3) - 2 \cdot a(2n+1) = \mathrm{binaryDigit}(\sqrt{2}, n)$.
-/
@[category research solved, AMS 11]
theorem erdos_482 :
    ∀ n : ℕ,
      grahamPollakSeq (2 * n + 3) - 2 * grahamPollakSeq (2 * n + 1) =
        binaryDigit (Real.sqrt 2) n := by
  sorry

end Erdos482
