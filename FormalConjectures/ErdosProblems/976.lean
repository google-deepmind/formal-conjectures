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
# Erdős Problem 976

For an irreducible polynomial $f \in \mathbb{Z}[x]$ of degree $d \geq 2$, estimate the greatest
prime factor of $\prod_{m=1}^{n} f(m)$. In particular, is this $\gg n^{1+c}$ for some $c > 0$,
or even $\gg n^d$?

Nagell [Na22] and Ricci [Ri34] independently proved that $F_f(n) \gg n \log n$. Erdős [Er52c]
improved this to $F_f(n) \gg n(\log n)^{\log\log\log n}$. Erdős [Er65b] claimed a proof of
$F_f(n) \gg n \exp((\log n)^c)$ for some $c > 0$, but the argument was flawed; a weaker result
was published in [ErSc90]. Tenenbaum [Te90] proved the stronger bound.

## References

[Er52c] Erdős, P., _On the greatest prime factor of $\prod^x_{k=1} f(k)$_.
  J. London Math. Soc. (1952), 379–384.

[Er65b] Erdős, P., _Some recent advances and current problems in number theory_.
  Lectures on Modern Mathematics, Vol. III (1965), 196–244.

[ErSc90] Erdős, P., Schinzel, A., _On the greatest prime factor of $\prod^x_{k=1} f(k)$_.
  Acta Arith. (1990), 191–200.

[Na22] Nagell, T., _Abh. Math. Sem. Hamburg_ (1922), 179–194.

[Ri34] Ricci, G., _Ann. Mat._ (1934), 295–303.

[Te90] Tenenbaum, G., _Sur une question d'Erdős et Schinzel_ (1990), 405–443.

*Reference:* [erdosproblems.com/976](https://www.erdosproblems.com/976)
-/

open Polynomial Filter

namespace Erdos976

/-- The greatest prime factor of a natural number $n$, or $0$ if $n \leq 1$. -/
def greatestPrimeFactor (n : ℕ) : ℕ :=
  n.primeFactorsList.foldr max 0

/-- The product of $|f(m)|$ for $m = 1, \ldots, n$. -/
noncomputable def polyProduct (f : Polynomial ℤ) (n : ℕ) : ℕ :=
  ∏ m ∈ Finset.range n, (f.eval (↑(m + 1) : ℤ)).natAbs

/--
Let $f \in \mathbb{Z}[x]$ be an irreducible polynomial of degree $d \geq 2$. Let $F_f(n)$ be
the greatest prime divisor of $\prod_{m=1}^{n} f(m)$. Is it true that $F_f(n) \gg n^{1+c}$
for some $c > 0$?

Formalized as: there exist constants $c > 0$ and $C > 0$ such that for all sufficiently large
$n$, the greatest prime factor of $\prod_{m=1}^{n} |f(m)|$ is at least $C \cdot n^{1+c}$.
-/
@[category research open, AMS 11]
theorem erdos_976 : answer(sorry) ↔
    ∀ (f : Polynomial ℤ), Irreducible f → 2 ≤ f.natDegree →
      ∃ (c : ℝ) (C : ℝ), c > 0 ∧ C > 0 ∧
        ∀ᶠ n in atTop,
          (greatestPrimeFactor (polyProduct f n) : ℝ) ≥ C * (n : ℝ) ^ (1 + c) := by
  sorry

/--
Is it true that $F_f(n) \gg n^d$ where $d = \deg(f)$?

Formalized as: there exists $C > 0$ such that for all sufficiently large $n$,
the greatest prime factor of $\prod_{m=1}^{n} |f(m)|$ is at least $C \cdot n^d$.
-/
@[category research open, AMS 11]
theorem erdos_976.variants.strong : answer(sorry) ↔
    ∀ (f : Polynomial ℤ), Irreducible f → 2 ≤ f.natDegree →
      ∃ (C : ℝ), C > 0 ∧
        ∀ᶠ n in atTop,
          (greatestPrimeFactor (polyProduct f n) : ℝ) ≥ C * (n : ℝ) ^ (f.natDegree) := by
  sorry

end Erdos976
