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
# Erdős Problem 483

*Reference:* [erdosproblems.com/483](https://www.erdosproblems.com/483)

[Er61] Erdős, P., _Some unsolved problems_, Magyar Tud. Akad. Mat. Kutató Int. Közl. 6 (1961),
221-254.

[Er65] Erdős, P., _Extremal problems in number theory_, Proc. Sympos. Pure Math. 8 (1965),
181-189.
-/

namespace Erdos483

/-- A coloring $f : \mathbb{N} \to \text{Fin}\ k$ has a *monochromatic Schur triple* in
$\{1, \ldots, N\}$ if there exist $a, b \geq 1$ with $a + b \leq N$ and
$f(a) = f(b) = f(a + b)$. -/
def HasMonochromaticSchurTriple (k N : ℕ) (f : ℕ → Fin k) : Prop :=
  ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ a + b ≤ N ∧ f a = f b ∧ f b = f (a + b)

/--
Erdős Problem 483 [Er61, p.233] [Er65, p.188]:

Let $f(k)$ be the minimal $N$ such that if $\{1, \ldots, N\}$ is $k$-coloured then there is a
monochromatic solution to $a + b = c$. The values $f(k)$ are known as Schur numbers.

Estimate $f(k)$. In particular, is it true that $f(k) < c^k$ for some constant $c > 0$?

The best-known bounds for large $k$ are
$$
  380^{k/5} - O(1) \leq f(k) \leq \lfloor (e - 1/24)\, k! \rfloor - 1.
$$
The known values are $f(1) = 2$, $f(2) = 5$, $f(3) = 14$, $f(4) = 45$, $f(5) = 161$
(OEIS A030126).

We formalize the conjecture: there exists $c > 0$ such that for all $k \geq 1$,
every $k$-coloring of $\{1, \ldots, N\}$ with $N \geq c^k$ has a monochromatic Schur triple.
Equivalently, the Schur number $f(k)$ grows at most exponentially in $k$.
-/
@[category research open, AMS 5]
theorem erdos_483 : answer(sorry) ↔
    ∃ c : ℝ, 0 < c ∧
      ∀ k : ℕ, 1 ≤ k →
        ∀ N : ℕ, c ^ k ≤ (N : ℝ) →
          ∀ f : ℕ → Fin k,
            HasMonochromaticSchurTriple k N f := by
  sorry

end Erdos483
