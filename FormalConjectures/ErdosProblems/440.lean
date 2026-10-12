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
# Erdős Problem 440

*References:*
- [erdosproblems.com/440](https://www.erdosproblems.com/440)
- [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980).
- [ErSz80] Erdős, Pál and Szemerédi, Endre, _Remarks on a problem of the American Mathematical
  Monthly_. Mat. Lapok (1980), 121-124.
-/

@[expose] public section

open Filter Real

namespace Erdos440

/-- For a strictly increasing sequence `a` of positive integers, `count a x` is the number of
indices `i` with `lcm(aᵢ, aᵢ₊₁) ≤ x`. -/
noncomputable def count (a : ℕ → ℕ) (x : ℕ) : ℕ :=
  {i | Nat.lcm (a i) (a (i + 1)) ≤ x}.ncard

/--
Let $A=\{a_1<a_2<\cdots\}\subseteq \mathbb{N}$ be infinite and let $A(x)$ count the number of
indices for which $\mathrm{lcm}(a_i,a_{i+1})\leq x$. Is it true that $A(x) \ll x^{1/2}$?

The answer is yes: Tao has given a simple proof, and Erdős and Szemerédi [ErSz80] proved the
sharp bound $A(x)\leq (c+o(1))x^{1/2}$ (see `erdos_440.variants.erdos_szemeredi`).
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos440.lean#L602"]
theorem erdos_440.parts.i : answer(True) ↔
    ∀ a : ℕ → ℕ, StrictMono a → (∀ i, 0 < a i) →
      (fun x : ℕ ↦ (count a x : ℝ)) =O[atTop] fun x : ℕ ↦ √x := by
  sorry

/--
How large can
$$\liminf \frac{A(x)}{x^{1/2}}$$
be?

Taking $A=\mathbb{N}$ shows that $\liminf A(x)/x^{1/2}=1$ is possible. Erdős and Szemerédi
[ErSz80] proved that it is always $\leq 1$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos440.lean#L602"]
theorem erdos_440.parts.ii :
    IsGreatest {l : ℝ | ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧
      l = liminf (fun x : ℕ ↦ (count a x : ℝ) / √x) atTop} answer(1) := by
  sorry

/-- The Erdős–Szemerédi constant $c=\sum_{n\geq 1}\frac{1}{n^{1/2}(n+1)}\approx 1.86$
(summed here over $n = m + 1$, $m \geq 0$). -/
noncomputable def erdosSzemerediConstant : ℝ := ∑' m : ℕ, 1 / (√(m + 1 : ℝ) * (m + 2))

/--
Erdős and Szemerédi [ErSz80] proved that $A(x)\leq (c+o(1))x^{1/2}$ where
$$c=\sum_{n\geq 1}\frac{1}{n^{1/2}(n+1)}\approx 1.86,$$
and that this constant is best possible (this was later rediscovered by van Doorn).
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos440.lean#L602"]
theorem erdos_440.variants.erdos_szemeredi :
    IsGreatest {l : ℝ | ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧
      l = limsup (fun x : ℕ ↦ (count a x : ℝ) / √x) atTop} erdosSzemerediConstant := by
  sorry

end Erdos440
