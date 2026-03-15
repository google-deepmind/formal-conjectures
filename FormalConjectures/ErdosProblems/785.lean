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
# Erdős Problem 785

*Reference:* [erdosproblems.com/785](https://www.erdosproblems.com/785)

Let $A, B \subseteq \mathbb{N}$ be infinite sets such that $A + B$ contains all large integers.
Let $A(x) = |A \cap [1, x]|$ and similarly for $B(x)$. Is it true that if
$A(x)B(x) \sim x$ then $A(x)B(x) - x \to \infty$ as $x \to \infty$?

Such sets $A$ and $B$ (with all large integers in $A + B$ and $A(x)B(x) \sim x$) are
called exact additive complements. Danzer [Da64] proved that exact additive complements exist.

The answer is yes, proved by Sárközy and Szemerédi [SaSz94].
Ruzsa [Ru17] has constructed, for any function $w(x) \to \infty$, such a pair
of sets with $A(x)B(x) - x < w(x)$ for infinitely many $x$.

Chen and Fang [ChFa15] strengthened the result, showing that
$A(x)B(x) - x \ll A(x)^c$ cannot hold for any constant $c > 0$.
Narkiewicz [Na59] proved that $A(2x)/A(x) \to 1$ and $B(2x)/B(x) \to 2$
for exact additive complements.

[SaSz94] Sárközy, A., Szemerédi, E., _On a problem in additive number theory_.
Acta Mathematica Hungarica **65** (1994), 237–245.

[Ru17] Ruzsa, I. Z., _Exact additive complements_.
Quarterly Journal of Mathematics **68** (2017), 227–235.

[Da64] Danzer, L., _Über eine Frage von G. Hanani aus der additiven Zahlentheorie_.
Journal für die Reine und Angewandte Mathematik **214** (1964), 392–394.

[ChFa15] Chen, Y.-G., Fang, J.-H., _On a conjecture of Sárközy and Szemerédi_.
Acta Arithmetica **169** (2015), 47–58.

[Na59] Narkiewicz, W. (1959).
-/

open scoped Classical
open Filter

namespace Erdos785

/-- Counting function: $|A \cap \{1, \ldots, x\}|$ -/
noncomputable def countingFn (A : Set ℕ) (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (· ∈ A)).card

/--
**Erdős Problem 785** (Sárközy and Szemerédi [SaSz94]):

Let $A, B \subseteq \mathbb{N}$ be infinite sets such that $A + B$ contains all sufficiently
large integers (i.e., $A$ and $B$ are additive complements). If $A(x)B(x) \sim x$
(exact additive complements), then $A(x)B(x) - x \to \infty$ as $x \to \infty$.
-/
@[category research solved, AMS 5 11]
theorem erdos_785 : answer(True) ↔
    ∀ (A B : Set ℕ), Set.Infinite A → Set.Infinite B →
    (∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → ∃ a ∈ A, ∃ b ∈ B, a + b = n) →
    Tendsto (fun x : ℕ => (countingFn A x * countingFn B x : ℝ) / (x : ℝ))
      atTop (nhds 1) →
    Tendsto (fun x : ℕ => (countingFn A x * countingFn B x : ℝ) - (x : ℝ))
      atTop atTop := by
  sorry

/--
**Ruzsa's construction [Ru17]:**

For any function $w(x) \to \infty$, there exist exact additive complements $A, B$ such that
$A(x)B(x) - x < w(x)$ for infinitely many $x$. This shows that the divergence in `erdos_785`
can be arbitrarily slow.
-/
@[category research solved, AMS 5 11]
theorem erdos_785_ruzsa_sharpness :
    ∀ w : ℕ → ℝ, Tendsto w atTop atTop →
    ∃ (A B : Set ℕ), Set.Infinite A ∧ Set.Infinite B ∧
    (∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → ∃ a ∈ A, ∃ b ∈ B, a + b = n) ∧
    Tendsto (fun x : ℕ => (countingFn A x * countingFn B x : ℝ) / (x : ℝ))
      atTop (nhds 1) ∧
    ∃ᶠ x in atTop, (countingFn A x * countingFn B x : ℝ) - (x : ℝ) < w x := by
  sorry

end Erdos785
