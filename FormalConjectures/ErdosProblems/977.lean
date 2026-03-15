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
import FormalConjecturesForMathlib.Data.Nat.MaxPrimeFac

/-!
# Erdős Problem 977

Erdős asked whether the greatest prime factor of $2^n - 1$ grows faster than
linearly in $n$, i.e., whether $P(2^n - 1)/n \to \infty$.

Erdős also asked the analogous question for $P(n! + 1)$: does $P(n! + 1)/n \to \infty$?

*Reference:* [erdosproblems.com/977](https://www.erdosproblems.com/977)

[Er65b] Erdős, P., *Some recent advances and current problems in number theory*.
Lectures on Modern Mathematics **III** (1965), 196–244.

[Sc62] Schinzel, A., *On primitive prime factors of $a^n - b^n$*.
Proceedings of the Cambridge Philosophical Society (1962), 555–562.

[St74b] Stewart, C. L., *The greatest prime factor of $a^n - b^n$*.
Acta Arithmetica (1974/75), 427–433.

[MuWo02] Murty, R. and Wong, S., *The ABC conjecture and prime divisors of the Lucas and
Lehmer sequences* (2002), 43–54.

[St13] Stewart, C. L., *On divisors of Lucas and Lehmer numbers*.
Acta Mathematica (2013), 291–314.

[La21] Lai, L., *On the largest prime divisor of $n! + 1$*. arXiv:2103.14894 (2021).

OEIS sequences: A005420, A002583.
-/

open Filter Nat

namespace Erdos977

/--
Erdős Problem #977 [Er65b]:
If $P(m)$ denotes the greatest prime divisor of $m$, is it true that
$P(2^n - 1) / n \to \infty$ as $n \to \infty$?

This was proved by Stewart [St13], who showed that
$P(2^n - 1) \gg n^{1 + 1/(104 \log \log n)}$ for all sufficiently large $n$.
Only the qualitative consequence (divergence to $\infty$) is formalized here.
-/
@[category research solved, AMS 11]
theorem erdos_977 :
    answer(True) ↔
      Tendsto (fun n : ℕ => (maxPrimeFac (2 ^ n - 1) : ℝ) / (n : ℝ))
        atTop atTop := by
  sorry

/--
Variant of Erdős Problem #977: does $P(n! + 1) / n \to \infty$?

Murty and Wong [MuWo02] proved $P(n! + 1) > (1 + o(1)) n \log n$ assuming the abc conjecture.
Lai [La21] proved unconditionally that $\limsup P(n! + 1) / n \geq 1 + 9 \log 2$.
-/
@[category research open, AMS 11]
theorem erdos_977_variant_factorial :
    answer(sorry) ↔
      Tendsto (fun n : ℕ => (maxPrimeFac (n.factorial + 1) : ℝ) / (n : ℝ))
        atTop atTop := by
  sorry

end Erdos977
