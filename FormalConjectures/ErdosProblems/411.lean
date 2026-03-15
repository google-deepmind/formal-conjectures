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

Steinerberger showed that for $r = 2$, the problem reduces to solving
$\varphi(n) + \varphi(n + \varphi(n)) = n$.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[St25] Steinerberger, S., *On an iterated arithmetic function problem of Erdős and Graham*.
arXiv:2504.08023 (2025).
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

/--
Erdős Problem 411, generalized multiplier variant:

For which positive integers $n$, $r$, and $m$ does $g_{k+r}(n) = m \cdot g_k(n)$ hold for all
sufficiently large $k$? This generalizes the main problem by replacing the multiplier $2$ with
an arbitrary positive integer $m$. Known examples include $g_{k+9}(n) = 9 \cdot g_k(n)$
(Selfridge–Weintraub) and $g_{k+25}(3114) = 729 \cdot g_k(3114)$ for $k \geq 6$ (Weintraub).
-/
@[category research open, AMS 11]
theorem erdos_411_general_multiplier :
    {p : ℕ × ℕ × ℕ | 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧
      ∃ K, ∀ k, K ≤ k → g^[k + p.2.1] p.1 = p.2.2 * g^[k] p.1} = answer(sorry) := by
  sorry

/--
Erdős Problem 411, known solution: $n = 10$, $r = 2$ satisfies
$g_{k+2}(10) = 2 \cdot g_k(10)$ for all sufficiently large $k$.
-/
@[category test, AMS 11]
theorem erdos_411_test_10 :
    ∃ K, ∀ k, K ≤ k → g^[k + 2] 10 = 2 * g^[k] 10 := by
  sorry

/--
Erdős Problem 411, known solution: $n = 94$, $r = 2$ satisfies
$g_{k+2}(94) = 2 \cdot g_k(94)$ for all sufficiently large $k$.
-/
@[category test, AMS 11]
theorem erdos_411_test_94 :
    ∃ K, ∀ k, K ≤ k → g^[k + 2] 94 = 2 * g^[k] 94 := by
  sorry

/--
Cambie's refined conjecture: For primes $p \equiv 7 \pmod{8}$ and integers $t \geq 1$,
the equation $g_k(2p^t) = 4p^t$ has no solutions except $t = 1$ with $p \in \{7, 47\}$.
-/
@[category research open, AMS 11]
theorem erdos_411_cambie :
    {p : ℕ × ℕ | p.1.Prime ∧ p.1 % 8 = 7 ∧ 0 < p.2 ∧
      ∃ k, g^[k] (2 * p.1 ^ p.2) = 4 * p.1 ^ p.2} =
    {(7, 1), (47, 1)} := by
  sorry

end Erdos411
