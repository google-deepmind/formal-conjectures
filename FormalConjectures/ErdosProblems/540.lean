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
# Erdős Problem 540

Is it true that if $A \subseteq \mathbb{Z}/N\mathbb{Z}$ has size $\gg N^{1/2}$ then there exists
some non-empty $S \subseteq A$ such that $\sum_{n \in S} n \equiv 0 \pmod{N}$?

*Reference:* [erdosproblems.com/540](https://www.erdosproblems.com/540)

[ErHe64] Erdős, P., Heilbronn, H., _On the addition of residue classes mod p_,
Acta Arith. **9** (1964), 149–159.

[Ol68] Olson, J. E., _An addition theorem modulo p_, J. Combinatorial Theory **5** (1968), 45–52.

[Sz70] Szemerédi, E., _On a conjecture of Erdős and Heilbronn_, Acta Arith. **17** (1970), 227–229.

[HaZe96] Hamidoune, Y. O., Zémor, G., _On zero-free subset sums_,
Acta Arith. **78** (1996), 143–152.

[Ba12] Balandraud, É., _An addition theorem and maximal zero-sum free sets in ℤ/pℤ_,
Israel J. Math. **188** (2012), 405–429.
-/

open Finset BigOperators

namespace Erdos540

/--
Erdős Problem 540:

Is it true that if $A \subseteq \mathbb{Z}/N\mathbb{Z}$ has size $\gg N^{1/2}$ then there exists
some non-empty $S \subseteq A$ such that $\sum_{n \in S} n \equiv 0 \pmod{N}$?

The answer is yes. This was originally posed by Erdős and Heilbronn [ErHe64].
It was proved for $N$ prime by Olson [Ol68], and for all $N$ by
Szemerédi [Sz70] (in fact for arbitrary finite abelian groups).

Erdős speculated that the correct threshold is $(2N)^{1/2}$; this was proved for $N$ prime
by Balandraud [Ba12]. Hamidoune and Zémor [HaZe96] established a bound of
$(1+o(1))\sqrt{2N}$ for arbitrary abelian groups of order $N$.
-/
@[category research solved, AMS 5 11]
theorem erdos_540 : answer(True) ↔
    ∃ C : ℝ, C > 0 ∧
    ∀ (N : ℕ), 0 < N →
    ∀ (A : Finset (ZMod N)),
      (A.card : ℝ) ≥ C * Real.sqrt (N : ℝ) →
      ∃ S : Finset (ZMod N), S.Nonempty ∧ S ⊆ A ∧ (∑ n ∈ S, n) = 0 := by
  sorry

/--
Erdős Problem 540 — sharp constant for prime modulus (Balandraud [Ba12]):

For $p$ prime, if $A \subseteq \mathbb{Z}/p\mathbb{Z}$ has size at least $\sqrt{2p}$,
then there exists a non-empty $S \subseteq A$ such that $\sum_{n \in S} n = 0$.

This gives the sharp threshold conjectured by Erdős and Selfridge.
-/
@[category research solved, AMS 5 11]
theorem erdos_540_prime_sharp (p : ℕ) (hp : p.Prime) (A : Finset (ZMod p))
    (hA : (A.card : ℝ) ≥ Real.sqrt (2 * p)) :
    ∃ S : Finset (ZMod p), S.Nonempty ∧ S ⊆ A ∧ (∑ n ∈ S, n) = 0 := by
  sorry

end Erdos540
