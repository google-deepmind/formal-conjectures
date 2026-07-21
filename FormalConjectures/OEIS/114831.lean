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
# Each term is previous term plus floor of harmonic mean of two previous terms.

Each term is previous term plus floor of harmonic mean of two previous terms.
$a(1) = 1, a(2) = 2$
$a(n) = a(n-1) + \lfloor \frac{2 a(n-1) a(n-2)}{a(n-1) + a(n-2)} \rfloor$ for $n \ge 3$

*References:*
- [A114831](https://oeis.org/A114831)
-/

namespace OeisA114831

open Filter Real Topology

/--
The primary defining sequence `a`.
Each term is previous term plus floor of harmonic mean of two previous terms.
-/
noncomputable def a : ℕ → ℕ
| 0 => 0 -- Dummy value, sequence starts at index 1
| 1 => 1
| 2 => 2
| n + 3 =>
  let an_1 : ℕ := a (n + 2)
  let an_2 : ℕ := a (n + 1)
  let num : ℚ := (2 * an_1 * an_2 : ℕ).cast
  let den : ℚ := (an_1 + an_2 : ℕ).cast
  let harmonic_term_floor : ℕ := Int.toNat (num / den).floor
  an_1 + harmonic_term_floor

@[category test, AMS 11]
lemma test_a_1 : a 1 = 1 := by norm_num [a]

@[category test, AMS 11]
lemma test_a_2 : a 2 = 2 := by rw [a]

@[category test, AMS 11]
lemma test_a_3 : a 3 = 3 := by
  norm_num [a, Rat.floor, Int.toNat]

@[category test, AMS 11]
lemma test_a_4 : a 4 = 5 := by
  norm_num [a, Rat.floor, Int.toNat]

/--
Conjecture based on OEIS A114831: What is this sequence, asymptotically?
If the limit exists, the ratio of consecutive terms must tend to $\sqrt{3}$:
$$ \lim_{n \to \infty} \frac{a(n+1)}{a(n)} = \sqrt{3}. $$
That's because a(n) is positive, monotonically increasing ($a(n) > a(n-1)$)
and $a(n+2) \geq a(n+1) + a(n)$. So $a(n)$ grows exponentially, at least as fast as the Fibonnaci numbers.
Assuming $\frac{a(n+1)}{a(n)}$ tend to a limit L, solving for L in the definition of $a(n)$
gives $L=\sqrt{3}$.
-/
@[category research open, AMS 11]
theorem conjecture3 :
    Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ)) atTop (nhds (Real.sqrt 3)) := by
  sorry

end OeisA114831
