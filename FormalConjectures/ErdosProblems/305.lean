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
# Erdős Problem 305

*References:*
- [erdosproblems.com/305](https://www.erdosproblems.com/305)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [BlEr76] Bleicher, M. N. and Erdős, P., *Denominators of unit fractions*. J. Number Th. (1976),
  157-168.
- [Yo88] Yokota, H., *On a problem of Bleicher and Erdős*. J. Number Theory (1988), 198-207.
- [LiSa24] Liu, Y. and Sawhney, M., *On further questions regarding unit fractions*.
  arXiv:2404.07113 (2024).
-/

@[expose] public section

open Filter Real

namespace Erdos305

/--
`D a b` is the minimal value of $n_k$ such that there exist integers $1\leq n_1<\cdots <n_k$ with
$\frac{a}{b}=\frac{1}{n_1}+\cdots+\frac{1}{n_k}$.
-/
noncomputable def D (a b : ℕ) : ℕ :=
  sInf {B | ∃ E : Finset ℕ, 0 ∉ E ∧ (∀ n ∈ E, n ≤ B) ∧
    ∑ n ∈ E, (1 : ℚ) / n = a / b}

/-- $D(b)=\max_{1\leq a<b}D(a,b)$. -/
noncomputable def Dmax (b : ℕ) : ℕ := (Finset.Ico 1 b).sup fun a ↦ D a b

/--
For integers $1\leq a<b$ let $D(a,b)$ be the minimal value of $n_k$ such that there exist
integers $1\leq n_1<\cdots <n_k$ with
$$\frac{a}{b}=\frac{1}{n_1}+\cdots+\frac{1}{n_k}.$$
Estimate $D(b)=\max_{1\leq a<b}D(a,b)$. Is it true that
$$D(b) \ll b(\log b)^{1+o(1)}?$$

Bleicher and Erdős [BlEr76] have shown that $D(b)\ll b(\log b)^2$. If $b=p$ is a prime then
$D(p) \gg p\log p$.

This was solved by Yokota [Yo88], who proved that
$$D(b)\ll b(\log b)(\log\log b)^4(\log\log\log b)^2.$$
This was improved by Liu and Sawhney [LiSa24] to
$$D(b)\ll b(\log b)(\log\log b)^3(\log\log\log b)^{O(1)}.$$
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos305.lean#L217"]
theorem erdos_305 : answer(True) ↔ ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ b : ℕ in atTop,
      (Dmax b : ℝ) ≤ C * b * (log b) ^ (1 + δ b) := by
  sorry

/-- Bleicher and Erdős [BlEr76] have shown that $D(b)\ll b(\log b)^2$. -/
@[category research solved, AMS 11]
theorem erdos_305.variants.bleicher_erdos : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ b : ℕ in atTop, (Dmax b : ℝ) ≤ C * b * (log b) ^ 2 := by
  sorry

/-- If $b=p$ is a prime then $D(p) \gg p\log p$. -/
@[category research solved, AMS 11]
theorem erdos_305.variants.prime_lower_bound : ∃ c : ℝ, 0 < c ∧
    ∀ᶠ p : ℕ in atTop, p.Prime → c * p * log p ≤ Dmax p := by
  sorry

/--
Yokota [Yo88] proved that $D(b)\ll b(\log b)(\log\log b)^4(\log\log\log b)^2$.
-/
@[category research solved, AMS 11]
theorem erdos_305.variants.yokota : ∃ C : ℝ, 0 < C ∧ ∀ᶠ b : ℕ in atTop,
    (Dmax b : ℝ) ≤ C * b * log b * log (log b) ^ 4 * log (log (log b)) ^ 2 := by
  sorry

/--
Liu and Sawhney [LiSa24] proved that $D(b)\ll b(\log b)(\log\log b)^3(\log\log\log b)^{O(1)}$.
-/
@[category research solved, AMS 11]
theorem erdos_305.variants.liu_sawhney : ∃ C K : ℝ, 0 < C ∧ ∀ᶠ b : ℕ in atTop,
    (Dmax b : ℝ) ≤ C * b * log b * log (log b) ^ 3 * log (log (log b)) ^ K := by
  sorry

end Erdos305
