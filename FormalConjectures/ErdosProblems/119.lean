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
# Erdős Problem 119

*References:*
- [erdosproblems.com/119](https://www.erdosproblems.com/119)
- [Be91] Beck, J., The modulus of polynomials with zeros on the unit circle: A problem of Erdős.
  Annals of Math. (1991), 609-651.
- [Er57] Erdős, Paul, Some unsolved problems. Michigan Math. J. (1957), 291-300.
- [Er61] Erdős, Paul, Some unsolved problems. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221-254.
- [Er64b] Erdős, P., Problems and results on diophantine approximations. Compositio Math. (1964),
  52-65.
- [Er82e] Erdős, Paul, Some of my favourite problems which recently have been solved. (1982), 59--79.
- [Er90] Erdős, Paul, Some of my favourite unsolved problems. A tribute to Paul Erdős (1990),
  467-478.
- [Er97f] Erdős, Paul, Some unsolved problems. Combinatorics, geometry and probability (Cambridge,
  1993) (1997), 1-10.
- [Ha74] Hayman, W. K., Research problems in function theory: new problems. (1974), 155--180.
- [Li77] Linden, C. N., The modulus of polynomials with zeros on the unit circle. Bull. London Math.
  Soc. (1977), 65--69.
- [Va99] Various, Some of Paul's favorite problems. Booklet produced for the conference "Paul Erdős
  and his mathematics", Budapest, July 1999 (1999).
- [Wa80] Wagner, Gerold, On a problem of Erdős in {D}iophantine approximation. Bull. London Math.
  Soc. (1980), 81--88.
-/

open Filter Finset Set

namespace Erdos119

/-
Here we use 0-indexing for generality and convenience, while in the original problem
formulation 1-indexing was used. This change does not affect the meaning of the problem.
In the description of the problem below we remain faithful to the original one.
-/

/-- Let $z_i$ be an infinite sequence of complex numbers such that $|z_i| = 1$ for all $i \geq 1$.
For $n \geq 1$ let $p_n(z) = \prod_{i \leq n} (z - z_i)$. -/
noncomputable def p (z : ℕ → ℂ) (n : ℕ) : ℂ → ℂ :=
    fun w => ∏ i ∈ range n, (w - z i)

/-- Let $M_n = \max_{|z| = 1} |p_n(z)|$. -/
noncomputable def M (z : ℕ → ℂ) (n : ℕ) : ℝ :=
    sSup { (‖p z n w‖) | (w : ℂ) (_ : ‖w‖ = 1) }

/--
Is it true that $\limsup M_n = \infty$?

This is Problem 4.1 in [Ha74] where it is attributed to Erdős.

The weaker conjecture that $\limsup M_n=\infty$ was proved by Wagner [Wa80], who show that there is
some $c>0$ with $M_n>(\log n)^c$ infinitely often.
-/
@[category research solved, AMS 30]
theorem erdos_119.parts.i :
    answer(True) ↔ ∀ (z : ℕ → ℂ) (hz : ∀ i : ℕ, ‖z i‖ = 1),
      atTop.limsup (fun n => (M z n : EReal)) = ⊤ := by
  sorry

/--
Is it true that there exists $c > 0$ such that for infinitely many $n$ we have $M_n > n^c$?

The second question was answered by Beck [Be91], who proved that there exists some $c>0$ such that
$\max_{n\leq N} M_n > N^c$.
-/
@[category research solved, AMS 30]
theorem erdos_119.parts.ii :
    answer(True) ↔ ∀ (z : ℕ → ℂ) (hz : ∀ i : ℕ, ‖z i‖ = 1),
      ∃ (c : ℝ) (hc : c > 0), Infinite {n : ℕ | M z n > n ^ c} := by
  sorry

/--
Is it true that there exists $c > 0$ such that, for all large $n$, $\sum_{k \leq n} M_k > n^{1 + c}$?

The \$100 prize was offered for the third question in [Er97f]. This was resolved by GPT 5.6 and
Korsky (see the proof claims), who proved that $\sum_{k\leq n}M_k \gg \frac{n^{5/4}}{\sqrt{\log n}}$
(and hence for infinitely many $n$ we have $M_n> n^{1/4-o(1)}$).
-/
@[category research solved, AMS 30]
theorem erdos_119.parts.iii :
    answer(True) ↔ ∀ (z : ℕ → ℂ) (hz : ∀ i : ℕ, ‖z i‖ = 1),
      ∃ (c : ℝ) (hc : c > 0), ∀ᶠ n in atTop,
        ∑ k ∈ range n, M z k > n ^ (1 + c) := by
  sorry

end Erdos119
