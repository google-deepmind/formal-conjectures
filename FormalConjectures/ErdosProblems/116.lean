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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 116

*References:*
- [erdosproblems.com/116](https://www.erdosproblems.com/116)
- [EHP58] Erdős, P. and Herzog, F. and Piranian, G., *Metric properties of polynomials*. J.
  Analyse Math. (1958), 125-148.
- [Er61] Erdős, Paul, *Some unsolved problems*. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221-254.
- [Er82e] Erdős, Paul, *Some of my favourite problems which recently have been solved*. (1982),
  59--79.
- [Er90] Erdős, Paul, *Some of my favourite unsolved problems*. A tribute to Paul Erdős (1990),
  467-478.
- [Er97c] Erdős, Paul, *Some of my favorite problems and results*. The mathematics of Paul Erdős,
  I (1997), 47-67.
- [Po61] Pommerenke, Ch., *On metric properties of complex polynomials*. Michigan Math. J. (1961),
  97-115.
- [KLR25] M. Krishnapur, E. Lundberg, and K. Ramachandran, *On the area of polynomial
  lemniscates*. arXiv:2503.18270 (2025).
- [Wa88] Wagner, Gerold, *On the area of lemniscate domains*. J. Analyse Math. (1988), 159-167.
- [Po28] G. Pólya, *Beitrag zue Verallgemeinerung des Verzerrungssatzes auf mehrfach
  zusammenhängende Gebiete*. S-B. Akad. Wiss. (1928), 228-232 and 280-282.
-/

@[expose] public section

open MeasureTheory

namespace Erdos116

/--
Let $p(z)=\prod_{i=1}^n (z-z_i)$ for $\lvert z_i\rvert \leq 1$. Is it true that
$$\lvert\{ z: \lvert p(z)\rvert <1\}\rvert>n^{-O(1)}$$
(or perhaps even $>(\log n)^{-O(1)}$)?

Conjectured by Erdős, Herzog, and Piranian [EHP58]. The lower bound $\gg n^{-4}$ follows from a
result of Pommerenke [Po61]. The lower bound $\gg (\log n)^{-1}$ was proved by Krishnapur,
Lundberg, and Ramachandran [KLR25].

Wagner [Wa88] proves, for $n\geq 3$, the existence of such polynomials with
$$\lvert\{ z: \lvert p(z)\rvert <1\}\rvert \ll_\epsilon (\log\log n)^{-1/2+\epsilon}$$
for all $\epsilon>0$. Krishnapur, Lundberg, and Ramachandran [KLR25] improved this upper bound to
$\ll (\log\log n)^{-1}$.

Pólya [Po28] showed the upper bound $\lvert\{ z: \lvert p(z)\rvert <1\}\rvert \leq \pi$ always
holds, and this is achieved only when the $z_i$ are identical.
-/
@[category research solved, AMS 30, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos116.lean#L918"]
theorem erdos_116 : answer(True) ↔ ∃ c : ℝ, 0 < c ∧ ∃ C : ℕ, ∀ n : ℕ, 0 < n →
    ∀ z : Fin n → ℂ, (∀ i, ‖z i‖ ≤ 1) →
      ENNReal.ofReal (c / n ^ C) ≤ volume {w : ℂ | ‖∏ i, (w - z i)‖ < 1} := by
  sorry

/--
The lower bound $\lvert\{ z: \lvert p(z)\rvert <1\}\rvert \gg (\log n)^{-1}$ was proved by
Krishnapur, Lundberg, and Ramachandran [KLR25]; in particular the answer to the $(\log n)^{-O(1)}$
form of the question is also yes.
-/
@[category research solved, AMS 30]
theorem erdos_116.variants.log : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
    ∀ z : Fin n → ℂ, (∀ i, ‖z i‖ ≤ 1) →
      ENNReal.ofReal (c / Real.log n) ≤ volume {w : ℂ | ‖∏ i, (w - z i)‖ < 1} := by
  sorry

/--
Krishnapur, Lundberg, and Ramachandran [KLR25] proved that there are polynomials with
$\lvert\{ z: \lvert p(z)\rvert <1\}\rvert \ll (\log\log n)^{-1}$, improving a result of Wagner
[Wa88].
-/
@[category research solved, AMS 30]
theorem erdos_116.variants.upper : ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
    ∃ z : Fin n → ℂ, (∀ i, ‖z i‖ ≤ 1) ∧
      volume {w : ℂ | ‖∏ i, (w - z i)‖ < 1} ≤ ENNReal.ofReal (C / Real.log (Real.log n)) := by
  sorry

/-- Pólya [Po28]: $\lvert\{ z: \lvert p(z)\rvert <1\}\rvert \leq \pi$ always holds. -/
@[category research solved, AMS 30]
theorem erdos_116.variants.polya (n : ℕ) (z : Fin n → ℂ) :
    volume {w : ℂ | ‖∏ i, (w - z i)‖ < 1} ≤ ENNReal.ofReal Real.pi := by
  sorry

end Erdos116
