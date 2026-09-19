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
# Erdős Problem 310

*References:*
- [erdosproblems.com/310](https://www.erdosproblems.com/310)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [LiSa24] Liu, Y. and Sawhney, M., *On further questions regarding unit fractions*.
  arXiv:2404.07113 (2024).
- [Bl21] Bloom, T. F., *On a density conjecture about unit fractions*. arXiv:2112.03726 (2021).
-/

@[expose] public section

namespace Erdos310

/--
Let $\alpha >0$ and $N\geq 1$. Is it true that for any $A\subseteq \{1,\ldots,N\}$ with
$\lvert A\rvert \geq \alpha N$ there exists some $S\subseteq A$ such that
$$\frac{a}{b}=\sum_{n\in S}\frac{1}{n}$$
with $a\leq b =O_\alpha(1)$?

Liu and Sawhney [LiSa24] observed that the main result of Bloom [Bl21] implies a positive
solution to this conjecture. They prove a more precise version, that if
$(\log N)^{-1/7+o(1)}\leq \alpha \leq 1/2$ then there is some $S\subseteq A$ such that
$\frac{a}{b}=\sum_{n\in S}\frac{1}{n}$ with $a\leq b \leq \exp(O(1/\alpha))$. They also observe
that the dependence $b\leq \exp(O(1/\alpha))$ is sharp.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos310.lean#L240"]
theorem erdos_310 : answer(True) ↔ ∀ α : ℝ, 0 < α → ∃ C : ℕ, ∀ N : ℕ, 1 ≤ N →
    ∀ A ⊆ Finset.Icc 1 N, α * N ≤ A.card →
      ∃ S ⊆ A, ∃ a b : ℕ, 0 < a ∧ a ≤ b ∧ b ≤ C ∧ ∑ n ∈ S, (1 / n : ℚ) = a / b := by
  sorry

/--
Liu and Sawhney [LiSa24] proved that if $(\log N)^{-1/7+o(1)}\leq \alpha \leq 1/2$ then there is
some $S\subseteq A$ such that $\frac{a}{b}=\sum_{n\in S}\frac{1}{n}$ with
$a\leq b \leq \exp(O(1/\alpha))$.
-/
@[category research solved, AMS 11]
theorem erdos_310.variants.liu_sawhney : ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop,
    ∀ α : ℝ, Real.log N ^ (-(1 / 7 : ℝ) + ε) ≤ α → α ≤ 1 / 2 →
      ∀ A ⊆ Finset.Icc 1 N, α * N ≤ A.card →
        ∃ S ⊆ A, ∃ a b : ℕ, 0 < a ∧ a ≤ b ∧ (b : ℝ) ≤ Real.exp (C / α) ∧
          ∑ n ∈ S, (1 / n : ℚ) = a / b := by
  sorry

end Erdos310
