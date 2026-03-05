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
# Erdős Problem 305

*Reference:* [erdosproblems.com/305](https://www.erdosproblems.com/305)

For integers $1 \leq a < b$, let $D(a,b)$ be the largest denominator in an optimal
Egyptian fraction representation of $a/b$, and let $D(b) = \max_{1 \leq a < b} D(a,b)$.
Is it true that $D(b) \ll b(\log b)^{1+o(1)}$?

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[BlEr76] Bleicher, M. N. and Erdős, P., *Denominators of Egyptian fractions*. J. Number Theory
**8** (1976), 157-168.

[Yo88] Yokota, H., *On a problem of Bleicher and Erdős*. J. Number Theory **30** (1988), 198-207.

[LiSa24] Liu, J. and Sawhney, M., *An improvement on Erdős-Graham's conjecture*. (2024).
-/

open Finset Real

open scoped BigOperators

namespace Erdos305

/--
An *Egyptian fraction representation* of $a/b$ is a nonempty finset $S$ of positive
integers such that $\sum_{n \in S} 1/n = a/b$. Distinctness of denominators is
automatic from the finset structure.
-/
def IsEgyptianRepr (a b : ℕ) (S : Finset ℕ) : Prop :=
  S.Nonempty ∧ (∀ n ∈ S, 0 < n) ∧
  ∑ n ∈ S, (1 : ℝ) / (n : ℝ) = (a : ℝ) / (b : ℝ)

/--
Erdős Problem 305 [ErGr80, p.38]:

For integers $1 \leq a < b$, let $D(a,b)$ be the minimal value of the largest
denominator $n_k$ in an Egyptian fraction representation
$a/b = 1/n_1 + \cdots + 1/n_k$ with $1 \leq n_1 < \cdots < n_k$.

Define $D(b) = \max_{1 \leq a < b} D(a,b)$.

Is it true that $D(b) \ll b(\log b)^{1+o(1)}$?

Bleicher and Erdős [BlEr76] showed $D(b) \ll b(\log b)^2$.
Yokota [Yo88] improved this to
$D(b) \ll b(\log b)(\log \log b)^4(\log \log \log b)^2$,
and Liu and Sawhney [LiSa24] further improved it to
$D(b) \ll b(\log b)(\log \log b)^3(\log \log \log b)^{O(1)}$.

We formalize: for every $\varepsilon > 0$, there exist $C > 0$ and $b_0$ such that
for all $b \geq b_0$ and all $1 \leq a < b$, there exists an Egyptian fraction
representation of $a/b$ whose largest denominator is at most
$C \cdot b \cdot (\log b)^{1+\varepsilon}$.
-/
@[category research open, AMS 11]
theorem erdos_305 :
    answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
      ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b →
        ∀ a : ℕ, 1 ≤ a → a < b →
          ∃ S : Finset ℕ, IsEgyptianRepr a b S ∧
            ∀ n ∈ S, (n : ℝ) ≤ C * (b : ℝ) * (Real.log (b : ℝ)) ^ ((1 : ℝ) + ε) := by
  sorry

end Erdos305
