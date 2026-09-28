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
# Erdős Problem 984

*References:*
- [erdosproblems.com/984](https://www.erdosproblems.com/984)
- [Er80] Erdős, Paul, _A survey of problems in combinatorial number theory_. Ann. Discrete Math.
  (1980), 89-115.
-/

@[expose] public section

namespace Erdos984

/-- The $k$-term arithmetic progression $\{a,a+d,\ldots,a+(k-1)d\}$ is monochromatic under the
colouring `c`. -/
def IsMonochromaticAP (c : ℕ → Fin 2) (a d k : ℕ) : Prop :=
  ∃ i, ∀ j < k, c (a + j * d) = i

/--
Can $\mathbb{N}$ be $2$-coloured such that if
$$\{a,a+d,\ldots,a+(k-1)d\}$$
is a $k$-term monochromatic arithmetic progression then $k\ll_\epsilon a^\epsilon$ for all
$\epsilon>0$?

A question of Spencer, who proved that this is possible with $3$ colours, with $a^\epsilon$
replaced by a very slowly growing function $h(a)$. Erdős reports that he can construct such a
colouring with the bound $k\ll a^{1-c}$ for some absolute constant $c>0$. Zach Hunter has proved
the answer is yes.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos984.lean#L39"]
theorem erdos_984 : answer(True) ↔
    ∃ c : ℕ → Fin 2, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ a d k : ℕ, 0 < a → 0 < d → IsMonochromaticAP c a d k →
        (k : ℝ) ≤ C * (a : ℝ) ^ ε := by
  sorry

/-- Erdős reports that he can construct such a colouring with the bound $k\ll a^{1-c}$ for some
absolute constant $c>0$. -/
@[category research solved, AMS 5 11]
theorem erdos_984.variants.erdos :
    ∃ c : ℕ → Fin 2, ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ a d k : ℕ, 0 < a → 0 < d → IsMonochromaticAP c a d k →
        (k : ℝ) ≤ C * (a : ℝ) ^ (1 - δ) := by
  sorry

end Erdos984
