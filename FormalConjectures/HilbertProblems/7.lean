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
module

public import FormalConjecturesUtil

/-!
# Hilbert's seventh problem

One of the problems on Hilbert's list of 1900.

Hilbert asks whether the power $\alpha^\beta$ is transcendental for an algebraic base $\alpha$ and
an algebraic irrational exponent $\beta$. He names $2^{\sqrt{2}}$ and $e^{\pi} = i^{-2i}$ as
examples.

The problem was solved independently by Aleksandr Gelfond and Theodor Schneider in 1934.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Hilbert%27s_seventh_problem)
- [Gelfond 1934](https://zbmath.org/?format=complete&q=an:0009.05302)
- [Schneider 1934](https://zbmath.org/?format=complete&q=an:0010.10501)
- [Wikipedia: Gelfond–Schneider theorem](https://en.wikipedia.org/wiki/Gelfond%E2%80%93Schneider_theorem)
-/

@[expose] public section

namespace Hilbert7

/--
Hilbert's seventh problem, also known as the Gelfond–Schneider theorem: If $a$ is algebraic with
$a \neq 0, 1$ and if $b$ is algebraic and irrational, then every value of the complex power $a^b$
is transcendental.
-/
@[category research solved, question, AMS 11]
theorem hilbert_7th_problem
  (a b : ℂ)
  (ha : IsAlgebraic ℚ a) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
  (hb : IsAlgebraic ℚ b) (hb' : ∀ q : ℚ, (q : ℂ) ≠ b) :
  ∀ z ∈ {z : ℂ | ∃ w : ℂ, Complex.exp w = a ∧ z = Complex.exp (b * w)}, Transcendental ℚ z := by
  sorry

/--
Real form of Hilbert's seventh problem: If $a$ is algebraic with $0 < a$, $a \neq 1$ and $b$
algebraic and irrational, then the real power $a^b$ is transcendental.

For irrational $b$, a negative $a$ has no real power $a^b$, so the real statement needs $0 < a$.
-/
@[category research solved, AMS 11]
theorem hilbert_7th_problem_real
  (a b : ℝ)
  (ha : IsAlgebraic ℚ a) (ha0 : 0 < a) (ha1 : a ≠ 1)
  (hb : IsAlgebraic ℚ b) (hb' : Irrational b) :
  Transcendental ℚ (a ^ b) := by
  sorry

end Hilbert7
