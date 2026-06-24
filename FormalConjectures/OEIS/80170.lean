/-
Copyright 2025 The Formal Conjectures Authors.

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
import Mathlib.Algebra.IsPrimePow

/-!
# Conjecture relating two characterizations of a set of integers.

Informal Statement:
For an integer $k ≥ 2$, the following are equivalent:

1. The greatest common divisor of the binomial coefficients
    $\binom{2k}{k}, \binom{3k}{k}, \dots, \binom{(k+1)k}{k} = 1$.

2. Writing prime factorization of k as
    $k = \prod p_i^{e_i}$, and let
    $P = \max_i p_i^{e_i}$,
    one has $k / P > P$.

This conjecture asserts that the sequence defined by 1. is obtained by
taking 1 off each number in the sequence defined by 2.

*Reference:*
- [A80170](https://oeis.org/A80170)
- [A51283](https://oeis.org/A51283)
-/

namespace OeisA80170

/--
The gcd of the binomial coefficients
$\binom{2k}{k}, \binom{3k}{k}, \dots, \binom{(k+1)k}{k} = 1$.
-/
def GCDCondition (k : ℕ) : Prop :=
  (Finset.range k).gcd (fun i => Nat.choose ((i + 2) * k) k) = 1

/--
Let P be the largest prime power dividing `k`.
Then $k / P > P$.
-/
def PrimePowerCondition (k : ℕ) : Prop :=
  let P := ((Nat.divisors k).filter IsPrimePow).max.getD 0
  k / P > P

/--
Conjecture: The gcd condition is equivalent to the prime power condition.
This has been conjectured by Ralf Stephan.

Both the natural-language proof and its Lean 4 formalization were carried out
by the KLMM MechMath Agent Team; see the `formal_proof` attribute.

*References:*
- [Ralf Stephan, *Prove or Disprove. 100 Conjectures from the OEIS*, 2004, Conjecture 17 (arXiv:math/0409509)](https://arxiv.org/abs/math/0409509)
- [Dakai Guo et al., *A Greatest Common Divisor Criterion of Certain Binomial Coefficients*, 2026 (arXiv:2606.22997)](https://arxiv.org/abs/2606.22997)
-/
@[category research solved, AMS 11,
formal_proof using formal_conjectures at
"https://github.com/guodk/formal-conjectures/blob/0720658844d76a50d48e4baa152eef14d4462907/FormalConjectures/OEIS/80170.lean#L1823"]
theorem gcdCondition_iff_primePowerCondition (k : ℕ) (hk : 2 ≤ k) :
    GCDCondition k ↔ PrimePowerCondition (k + 1) := by
  sorry

end OeisA80170
