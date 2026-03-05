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
# Erdős Problem 440

*Reference:* [erdosproblems.com/440](https://www.erdosproblems.com/440)

Let $A = \{a_1 < a_2 < \cdots\} \subseteq \mathbb{N}$ be infinite and let $A(x)$ count the
number of indices $i$ for which $\mathrm{lcm}(a_i, a_{i+1}) \leq x$. Is it true that
$A(x) \ll x^{1/2}$?

How large can $\liminf A(x)/x^{1/2}$ be?

Taking $A = \mathbb{N}$ shows that $\liminf A(x)/x^{1/2} = 1$ is possible. Erdős and
Szemerédi [ErSz80] proved that it is always $\leq 1$.

Tao proved that $A(x) \ll x^{1/2}$. van Doorn proved that
$A(x) \leq (c + o(1))x^{1/2}$ where $c = \sum_{n \geq 1} 1/(n^{1/2}(n+1)) \approx 1.86$.
This was already proved by Erdős and Szemerédi, who showed this constant
is best possible.

[ErSz80] Erdős, P. and Szemerédi, E.
-/

open Filter

namespace Erdos440

/-- For a strictly increasing sequence $a : \mathbb{N} \to \mathbb{N}$ and a bound $x$, count the
number of indices $i$ such that $\mathrm{lcm}(a(i), a(i+1)) \leq x$. -/
def lcmPairCount (a : ℕ → ℕ) (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun i => Nat.lcm (a i) (a (i + 1)) ≤ x)).card

/-- Erdős Problem 440, part 1 (PROVED):
Is it true that for any strictly increasing sequence $a : \mathbb{N} \to \mathbb{N}$, the counting
function $A(x) = \#\{i : \mathrm{lcm}(a(i), a(i+1)) \leq x\}$ satisfies $A(x) = O(\sqrt{x})$?

Yes — proved by Tao; the sharp constant was determined by Erdős–Szemerédi [ErSz80]. -/
@[category research solved, AMS 11]
theorem erdos_440 : answer(True) ↔
    ∀ (a : ℕ → ℕ), StrictMono a →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x in atTop,
    (lcmPairCount a x : ℝ) ≤ C * Real.sqrt (x : ℝ) := by
  sorry

/-- Erdős Problem 440, liminf bound (PROVED):
How large can $\liminf_{x \to \infty} A(x)/\sqrt{x}$ be, over all strictly increasing sequences
$a : \mathbb{N} \to \mathbb{N}$? The answer is $1$: the liminf is always $\leq 1$
(Erdős–Szemerédi [ErSz80]) and $A = \mathbb{N}$ achieves equality. -/
@[category research solved, AMS 11]
theorem erdos_440.variants.liminf :
    sSup {L : ℝ | ∃ (a : ℕ → ℕ), StrictMono a ∧
      liminf (fun x => (lcmPairCount a x : ℝ) / Real.sqrt (x : ℝ)) atTop = L}
    = answer((1 : ℝ)) := by
  sorry

end Erdos440
