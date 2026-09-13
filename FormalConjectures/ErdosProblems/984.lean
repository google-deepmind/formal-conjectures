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
# Erdős Problem 984

*References:*
- [erdosproblems.com/984](https://www.erdosproblems.com/984)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
-/

open Asymptotics Filter

namespace Erdos984

/--
`MonoAPBound c bound` means that if
$\{a, a+d, \ldots, a+(k-1)d\}$ is a monochromatic arithmetic progression under `c`, then
$k \le \operatorname{bound}(a)$.

The first term $a$ and common difference $d$ are taken to be positive integers, so that the
progression has $k$ distinct terms and $a^\varepsilon$ is positive.
-/
def MonoAPBound {r : ℕ} (c : ℕ → Fin r) (bound : ℕ → ℝ) : Prop :=
  ∀ (a d k : ℕ), 0 < a → 0 < d → (∀ i < k, c (a + i * d) = c a) → (k : ℝ) ≤ bound a

/--
Can $\mathbb{N}$ be $2$-coloured such that if
$$\{a,a+d,\ldots,a+(k-1)d\}$$
is a $k$-term monochromatic arithmetic progression then $k\ll_\epsilon a^\epsilon$ for all
$\epsilon>0$?

A question of Spencer, who proved that this is possible with $3$ colours, with $a^\epsilon$
replaced by a very slowly growing function $h(a)$ (the inverse of the van der Waerden function).
Erdős reports that he can construct such a colouring with the bound $k\ll a^{1-c}$ for some
absolute constant $c>0$. He knew no non-trivial lower bound.

Zach Hunter has proved the answer is yes.
-/
@[category research solved, AMS 5 11]
theorem erdos_984 : answer(True) ↔
    ∃ c : ℕ → Fin 2, ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ),
      MonoAPBound c (fun a => C * (a : ℝ) ^ ε) := by
  sorry

/--
Spencer proved that a $3$-colouring exists such that every monochromatic $k$-term arithmetic
progression satisfies $k \le h(a)$ for a function $h$ growing more slowly than every positive
power of $a$ (the inverse of the van der Waerden function).
-/
@[category research solved, AMS 5 11]
theorem erdos_984.variants.spencer :
    ∃ (c : ℕ → Fin 3) (h : ℕ → ℝ),
      (∀ ε > (0 : ℝ), h =o[atTop] fun n : ℕ => (n : ℝ) ^ ε) ∧
      MonoAPBound c h := by
  sorry

/--
Erdős reports that he can construct a $2$-colouring with the bound $k \ll a^{1-c}$ for some
absolute constant $c>0$.
-/
@[category research solved, AMS 5 11]
theorem erdos_984.variants.erdos :
    ∃ (c : ℕ → Fin 2) (γ : ℝ), 0 < γ ∧ γ < 1 ∧ ∃ C > (0 : ℝ),
      MonoAPBound c (fun a => C * (a : ℝ) ^ (1 - γ)) := by
  sorry

end Erdos984
