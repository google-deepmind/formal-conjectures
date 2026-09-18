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
# Erdős Problem 190

*References:*
- [erdosproblems.com/190](https://www.erdosproblems.com/190)
- [ErGr79] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics*. Enseign. Math. (1979), 325-344.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Hu25b] Hunter, Zach, *Lower bounds for multicolor van der Waerden numbers*. Israel J. Math.
  (2025), 783--795.
- [FoHu26] J. Fox and Z. Hunter, *Three-color van der Waerden numbers grow super-exponentially*.
  arXiv:2606.02541 (2026).
- [Ba26] J.H. Bae, *A resolution of Erdős problem #190 via Erdős-Lovász, BCT, and
  Baker-Harman-Pintz*. arXiv:2604.20588 (2026).
-/

@[expose] public section

open Filter

namespace Erdos190

/-- A colouring `c` of `{0, …, N - 1}` contains either a monochromatic `k`-term arithmetic
progression or a rainbow one (all terms of different colours). -/
def HasMonochromaticOrRainbowAP (k N : ℕ) (c : ℕ → ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ a + (k - 1) * d < N ∧
    ((∀ i < k, c (a + i * d) = c a) ∨
      (∀ i < k, ∀ j < k, c (a + i * d) = c (a + j * d) → i = j))

/-- `H k` is the smallest `N` such that in any finite colouring of `{1, …, N}` (into any number
of colours) there is always either a monochromatic `k`-term arithmetic progression or a rainbow
arithmetic progression. -/
noncomputable def H (k : ℕ) : ℕ :=
  sInf {N : ℕ | 0 < N ∧ ∀ c : ℕ → ℕ, HasMonochromaticOrRainbowAP k N c}

/--
Let $H(k)$ be the smallest $N$ such that in any finite colouring of $\{1,\ldots,N\}$ (into any
number of colours) there is always either a monochromatic $k$-term arithmetic progression or a
rainbow arithmetic progression (i.e. all elements are different colours). Estimate $H(k)$. Is it
true that
$$H(k)^{1/k}/k \to \infty$$
as $k\to\infty$?

This type of problem belongs to 'canonical' Ramsey theory. The existence of $H(k)$ follows from
Szemerédi's theorem, and it is easy to show that $H(k)^{1/k}\to\infty$.

A recurrence of Hunter [Hu25b] implies $H(k)^{1/k}\to \infty$ (see Section 6 of [FoHu26]). Bae
[Ba26] proved more precisely that $H(k)\geq k^{(2-o(1))k}$. Fox and Hunter [FoHu26]
independently obtained the stronger estimate
$$H(k) \geq k^{(1-o(1))k\log k}.$$

Colourings are functions `ℕ → ℕ` (only the values on `{0, …, N - 1}` matter), which is
equivalent to colourings into an arbitrary finite set of colours.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos190.lean#L897"]
theorem erdos_190 : answer(True) ↔
    Tendsto (fun k : ℕ => (H k : ℝ) ^ (1 / (k : ℝ)) / k) atTop atTop := by
  sorry

/-- Fox and Hunter [FoHu26] proved that $H(k) \geq k^{(1-o(1))k\log k}$. -/
@[category research solved, AMS 5 11]
theorem erdos_190.variants.fox_hunter : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
    (k : ℝ) ^ ((1 - ε) * k * Real.log k) ≤ H k := by
  sorry

end Erdos190
