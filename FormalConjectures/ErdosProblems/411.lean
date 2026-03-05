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
# Erdős Problem 411

*Reference:* [erdosproblems.com/411](https://www.erdosproblems.com/411)

Let $g(n) = n + \varphi(n)$ and $g_k$ denote the $k$-th iterate of $g$, so
$g_1(n) = g(n) = n + \varphi(n)$ and $g_k(n) = g(g_{k-1}(n))$.

For which $n$ and $r$ is it true that $g_{k+r}(n) = 2 \cdot g_k(n)$ for all
sufficiently large $k$?

The known solutions to $g_{k+2}(n) = 2 \cdot g_k(n)$ are $n = 10$ and $n = 94$.
Selfridge and Weintraub found solutions to $g_{k+9}(n) = 9 \cdot g_k(n)$ and
Weintraub found $g_{k+25}(3114) = 729 \cdot g_k(3114)$ for all $k \geq 6$.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).
-/

namespace Erdos411

/-- The function $g(n) = n + \varphi(n)$ from Erdős Problem 411. -/
def g (n : ℕ) : ℕ := n + Nat.totient n

/--
Erdős Problem 411 [ErGr80, p.81]:

For which positive integers $n$ and $r$ does $g_{k+r}(n) = 2 \cdot g_k(n)$ hold for all
sufficiently large $k$? Cambie conjectures the answer is $r = 2$ and
$n = 2^l \cdot p$ for $l \geq 1$ and $p \in \{2, 3, 5, 7, 35, 47\}$.
-/
@[category research open, AMS 11]
theorem erdos_411 :
    {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧
      ∃ K, ∀ k, K ≤ k → g^[k + p.2] p.1 = 2 * g^[k] p.1} = answer(sorry) := by
  sorry

end Erdos411
