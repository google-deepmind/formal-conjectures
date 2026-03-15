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
# Erdős Problem 485

*Reference:* [erdosproblems.com/485](https://www.erdosproblems.com/485)

Let $f(k)$ be the minimum number of nonzero terms in $P(x)^2$, where $P \in \mathbb{Q}[x]$
ranges over all polynomials with exactly $k$ nonzero terms. Is it true that
$f(k) \to \infty$ as $k \to \infty$?

[Re47] Rényi, A., _On the minimal number of terms of the square of a polynomial_,
Hungarica Acta Math. (1947), 30–34.

[Er49b] Erdős, P., _On the number of terms of the square of a polynomial_,
Nieuw Arch. Wiskunde (2) (1949), 63–65.

[Ha74] Hayman, W. K., _Research problems in function theory: new problems_, (1974), 155–180.

[Sc87] Schinzel, A., _On the number of terms of a power of a polynomial_, Acta Arith. 49
(1987), 55–70.

[ScZa09] Schinzel, A. and Zannier, U., _On the number of terms of a power of a polynomial_,
Atti Accad. Naz. Lincei Rend. Lincei Mat. Appl. 20 (2009), 95–98.
-/

open Polynomial

namespace Erdos485

/--
Erdős Problem #485 (Erdős–Rényi conjecture, proved by Schinzel [Sc87]):

Let $f(k)$ be the minimum number of nonzero terms in $P(x)^2$, where $P \in \mathbb{Q}[x]$
ranges over all polynomials with exactly $k$ nonzero terms. Is it true that
$f(k) \to \infty$ as $k \to \infty$?

This is Problem 4.4 in [Ha74], where it is attributed to Erdős. First investigated
by Rényi and Rédei [Re47]. Erdős [Er49b] proved the upper bound $f(k) < k^{1-c}$
for some $c > 0$.

Schinzel [Sc87] proved $f(k) > \log(\log k) / \log 2$. Schinzel and Zannier [ScZa09]
improved this to $f(k) \gg \log k$.
-/
@[category research solved, AMS 12]
theorem erdos_485 : answer(True) ↔
    ∀ M : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    ∀ P : ℚ[X], P.support.card = k →
    M ≤ (P ^ 2).support.card := by
  sorry

/--
Generalization of Erdős Problem #485 to arbitrary powers:

For any fixed $n \geq 1$, the minimum number of nonzero terms of $P(x)^n$,
over all polynomials $P \in \mathbb{Q}[x]$ with exactly $k$ nonzero terms,
tends to infinity as $k \to \infty$.

Schinzel [Sc87] established lower bounds for this general case over fields
of characteristic zero or sufficiently large positive characteristic.
-/
@[category research solved, AMS 12]
theorem erdos_485_general_power :
    ∀ (n : ℕ), 1 ≤ n →
    ∀ M : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    ∀ P : ℚ[X], P.support.card = k →
    M ≤ (P ^ n).support.card := by
  sorry

end Erdos485
