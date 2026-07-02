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
# Erdős Problem 401

*References:*
- [erdosproblems.com/401](https://www.erdosproblems.com/401)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
-/

open Filter

namespace Erdos401

/--
Is there some function $f(r)$ such that $f(r)\to \infty$ as $r\to\infty$, such that, for
infinitely many $n$, there exist $a_1,a_2$ with
\[a_1+a_2> n+f(r)\log n\]
such that $a_1!a_2! \mid n!2^n3^n\cdots p_r^n$?

It is ambiguous in [ErGr80] what the intended quantifiers are on the variables (they write 'is
it true that we can find $a_1+a_2>n+f(r)\log n$...'). Comparing to previous problems such as
[728] and [729] it seems most likely that they intended to ask the formulation in the problem
statement.

The answer is yes: Barreto and Leeham have used ChatGPT to provide a proof of the stated problem
(in fact essentially the same construction as their solution to [729]).

The statement below writes $p_i$ for the $i$-th prime, so that
$2^n3^n\cdots p_r^n=(p_1p_2\cdots p_r)^n$, and takes $a_1,a_2$ to be positive integers.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos401.lean"]
theorem erdos_401 : answer(True) ↔
    ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ (r : ℕ) (hr : 1 ≤ r),
        {n : ℕ | ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧
          (a₁ : ℝ) + a₂ > n + f r * Real.log n ∧
          a₁.factorial * a₂.factorial ∣
            n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n}.Infinite := by
  sorry

end Erdos401
