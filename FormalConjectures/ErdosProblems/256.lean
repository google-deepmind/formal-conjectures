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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 256

*References:*
- [erdosproblems.com/256](https://www.erdosproblems.com/256)
- [ErSz59] Erdős, P. and Szekeres, G., On the product $\prod_{k=1}^n(1-z^{a_k})$.
  Acad. Serbe Sci. Publ. Inst. Math. (1959), 29-34.
- [BeKo96] Belov, A. S. and Konyagin, S. V., An estimate of the free term of a non-negative
  trigonometric polynomial with integer coefficients. Mat. Zametki (1996), 627-629.
-/

@[expose] public section

namespace Erdos256

open Filter Asymptotics

/-- The maximum of $\left\lvert \prod_i (1 - z^{a_i}) \right\rvert$ over the unit circle. -/
noncomputable def supNorm {n : ℕ} (a : Fin n → ℕ) : ℝ :=
  sSup ((fun z : ℂ ↦ ‖∏ i, (1 - z ^ a i)‖) '' Metric.sphere (0 : ℂ) 1)

/--
$f(n)$ is the largest real number such that
$\max_{\lvert z \rvert = 1} \left\lvert \prod_i (1 - z^{a_i}) \right\rvert \geq f(n)$
for all integers $1 \leq a_1 \leq \cdots \leq a_n$.
-/
noncomputable def f (n : ℕ) : ℝ :=
  sInf {M : ℝ | ∃ a : Fin n → ℕ, (∀ i, 1 ≤ a i) ∧ Monotone a ∧ M = supNorm a}

/--
Let $n \geq 1$ and let $f(n)$ be maximal such that for any integers
$1 \leq a_1 \leq \cdots \leq a_n$ we have
$$\max_{\lvert z \rvert = 1} \left\lvert \prod_i (1 - z^{a_i}) \right\rvert \geq f(n).$$
Is it true that there exists some constant $c > 0$ such that $\log f(n) \gg n^c$?

Belov and Konyagin [BeKo96] proved that $\log f(n) \ll (\log n)^4$, so the answer is no.
-/
@[category research solved, AMS 30]
theorem erdos_256 : answer(False) ↔ ∃ c > (0 : ℝ), ∃ C > (0 : ℝ),
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ c ≤ Real.log (f n) := by
  sorry

/--
Belov and Konyagin [BeKo96] proved that $\log f(n) \ll (\log n)^4$.
-/
@[category research solved, AMS 30]
theorem erdos_256.variants.belov_konyagin :
    (fun n : ℕ ↦ Real.log (f n)) =O[atTop] fun n : ℕ ↦ Real.log (n : ℝ) ^ 4 := by
  sorry

/--
Erdős and Szekeres [ErSz59] proved that $f(n) > \sqrt{2n}$ for all $n \geq 1$.
-/
@[category research solved, AMS 30]
theorem erdos_256.variants.erdos_szekeres (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (2 * (n : ℝ)) < f n := by
  sorry

/--
The weaker bound $f(n) \geq \sqrt{n + 1}$. The polynomial $\prod_i (1 - z^{a_i})$ has a root
of multiplicity at least $n$ at $1$. By Descartes' rule of signs it has at least $n + 1$
non-zero integer coefficients. Parseval's identity on the unit circle gives the bound.
-/
@[category research solved, AMS 30]
theorem erdos_256.variants.sqrt_lower_bound (n : ℕ) :
    Real.sqrt ((n : ℝ) + 1) ≤ f n := by
  sorry

end Erdos256
