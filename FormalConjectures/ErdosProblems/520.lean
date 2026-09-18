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

import FormalConjecturesUtil

/-!
# Erdős Problem 520

*References:*
- [erdosproblems.com/520](https://www.erdosproblems.com/520)
- [Hø26] Høystad, S. W. R., *A self-contained Lean 4 proof that Erdős Problem #520 has a
  negative answer* (2026), https://github.com/saasom/Erdos520/blob/v1.1.0/paper/erdos520_note.pdf
- [Ha13] Harper, A. J., *Bounds on the suprema of Gaussian processes, and omega results for the
  sum of a random multiplicative function*. Ann. Appl. Probab. 23 (2013), 584–616.
-/

open MeasureTheory ProbabilityTheory Nat Real Filter

namespace Erdos520

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/--
A random function $f$ is Rademacher multiplicative if $f(1) = 1$,
for each prime $p$, we independently choose $f(p) \in \{-1, 1\}$ uniformly at random (so each
$f(p)$ is a measurable function of the sample point),
for each square-free integer $n = p_1 \cdots p_r$, $f(n) = f(p_1) \cdots f(p_r)$, and
for each non-squarefree integer $n$, $f(n) = 0$.
-/
structure IsRademacherMultiplicative (f : ℕ → Ω → ℝ) : Prop where
  /-- Prime entries are random variables. -/
  measurable_of_prime p : p.Prime → Measurable (f p)
  /-- Prime entries are independent. -/
  iIndepFun_primes : iIndepFun (fun p : Primes ↦ f p) ℙ
  /-- Primes entries are uniformly distributed on `{-1, 1}`. -/
  prob_of_prime p : p.Prime → ℙ {ω | f p ω = 1} = 1 / 2 ∧ ℙ {ω | f p ω = -1} = 1 / 2
  map_one ω : f 1 ω = 1
  map_mul_of_coprime a b ω : a.Coprime b → f (a * b) ω = f a ω * f b ω
  map_of_not_squarefree n ω : ¬ Squarefree n → f n ω = 0

/--
Let $f$ be a Rademacher multiplicative function.
Does there exist some constant $c > 0$ such that, almost surely,
$$
  \limsup_{N \to \infty} \frac{\sum_{m \leq N} f(m)}{\sqrt{N \log \log N}} = c?
$$

The answer is no: Høystad [Hø26] (with GPT-5.6 Pro and Claude) proved, following the
Halász–Lau–Tenenbaum–Wu–Caich martingale approach with Harper's low-moment estimates [Ha13],
that almost surely $\sum_{m \le N} f(m) \ll \sqrt{N} (\log \log N)^{1/4 + \eta}$ for every
$\eta > 0$, so the $\limsup$ is $0$ almost surely. The linked formal
proof works with the concrete model `ℕ → Bool` with the product of fair coins, whose
squarefree-supported Rademacher function is `IsRademacherMultiplicative`; this refutes the
statement below.
-/
@[category research solved, AMS 11 60, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos520.lean#L24"]
theorem erdos_520 :
    answer(False) ↔ ∃ c > 0, ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (f : ℕ → Ω → ℝ), IsRademacherMultiplicative f →
      ∀ᵐ ω, limsup (fun N ↦ ∑ m ≤ N, f m ω / sqrt (N * log (log N))) atTop = c := by
  sorry

end Erdos520
