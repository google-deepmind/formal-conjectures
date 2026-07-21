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
# Erdős Problem 729

*References:*
- [erdosproblems.com/729](https://www.erdosproblems.com/729)
- [EGRS75] Erdős, P. and Graham, R. L. and Ruzsa, I. Z. and Straus, E. G., *On the prime factors of $\binom{2n}{n}$*. Math. Comp. (1975), 83-92.
- [Er68c] Erdős, P., *Aufgabe 557*. Elemente Math. (1968), 111-113.
-/

namespace Erdos729

/--
Let $C>0$ be a constant. Are there infinitely many integers $a,b,n$ with $a+b> n+C\log n$ such
that the denominator of\[\frac{n!}{a!b!}\]contains only primes $\ll_C 1$?

Erdős [Er68c] proved that if $a!b!\mid n!$ then $a+b\leq n+O(\log n)$. This has been proved in the affirmative by Barreto and Leeham, using ChatGPT and Aristotle, with a modification of the argument used for [728].
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos729.lean"]
theorem erdos_729 :
    answer(True) ↔ ∀ (C : ℝ) (hC : C > 0),
      ∃ K ≥ 3, Set.Infinite { T : ℕ × ℕ × ℕ |
        let (a, b, n) := T
        a > 0 ∧ b > 0 ∧ n > 0 ∧
        (a : ℝ) + b > n + C * Real.log n ∧
        ∀ p, p.Prime → p > K →
          padicValNat p ((n.factorial / (a.factorial * b.factorial) : ℚ).den) = 0 } := by
  sorry

end Erdos729
