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
# Erdős Problem 806

*References:*
- [erdosproblems.com/806](https://www.erdosproblems.com/806)
- [ErNe77] Erdős, P. and Newman, D. J., *Bases for sets of integers*. J. Number Theory (1977),
  420-425.
- [ABS09] Alon, Noga and Bukh, Boris and Sudakov, Benny, *Discrete Kakeya-type problems and small
  bases*. Israel J. Math. (2009), 285-301.
-/

@[expose] public section

open Filter
open scoped Pointwise

namespace Erdos806

/--
Let $A\subseteq \{1,\ldots,n\}$ with $\lvert A\rvert \leq n^{1/2}$. Must there exist some
$B\subset\mathbb{Z}$ with $\lvert B\rvert=o(n^{1/2})$ such that $A\subseteq B+B$?

A problem of Erdős and Newman [ErNe77], who proved that there exist $A$ with
$\lvert A\rvert\asymp n^{1/2}$ such that if $A\subseteq B+B$ then
$$\lvert B\rvert \gg \frac{\log\log n}{\log n}n^{1/2}.$$

Resolved by Alon, Bukh, and Sudakov [ABS09], who proved that for any $A\subseteq \{1,\ldots,n\}$
with $\lvert A\rvert \leq n^{1/2}$ there exists some $B$ such that $A\subseteq B+B$ and
$$\lvert B\rvert \ll \frac{\log\log n}{\log n}n^{1/2}.$$

See also [333](https://www.erdosproblems.com/333).
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos806.lean#L744"]
theorem erdos_806 : answer(True) ↔ ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → (A.card : ℝ) ≤ √n →
      ∃ B : Finset ℤ, A.map Nat.castEmbedding ⊆ B + B ∧ (B.card : ℝ) ≤ ε * √n := by
  sorry

/--
Alon, Bukh, and Sudakov [ABS09] proved that for any $A\subseteq \{1,\ldots,n\}$ with
$\lvert A\rvert \leq n^{1/2}$ there exists some $B$ such that $A\subseteq B+B$ and
$\lvert B\rvert \ll \frac{\log\log n}{\log n}n^{1/2}$.
-/
@[category research solved, AMS 11]
theorem erdos_806.variants.alon_bukh_sudakov : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → (A.card : ℝ) ≤ √n →
      ∃ B : Finset ℤ, A.map Nat.castEmbedding ⊆ B + B ∧
        (B.card : ℝ) ≤ C * Real.log (Real.log n) / Real.log n * √n := by
  sorry

/--
Erdős and Newman [ErNe77] proved that there exist $A\subseteq\{1,\ldots,n\}$ with
$\lvert A\rvert\asymp n^{1/2}$ such that if $A\subseteq B+B$ then
$\lvert B\rvert \gg \frac{\log\log n}{\log n}n^{1/2}$.
-/
@[category research solved, AMS 11]
theorem erdos_806.variants.erdos_newman : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ c * √n ≤ A.card ∧ (A.card : ℝ) ≤ √n ∧
      ∀ B : Finset ℤ, A.map Nat.castEmbedding ⊆ B + B →
        c * Real.log (Real.log n) / Real.log n * √n ≤ B.card := by
  sorry

end Erdos806
