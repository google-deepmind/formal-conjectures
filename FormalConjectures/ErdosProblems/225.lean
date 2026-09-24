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
# Erdős Problem 225

*References:*
- [erdosproblems.com/225](https://www.erdosproblems.com/225)
- [Er40b] Erdős, P., *Note on some elementary properties of polynomials*. Bull. Amer. Math. Soc.
  (1940), 954-958.
- [Er57] Erdős, Paul, *Some unsolved problems*. Michigan Math. J. (1957), 291-300.
- [Er61] Erdős, Paul, *Some unsolved problems*. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221-254.
- [Ha74] Hayman, W. K., *Research problems in function theory: new problems*. (1974), 155-180.
- [Kr74] Kristiansen, G. K., *Proof of an inequality for trigonometric polynomials*. Proc. Amer.
  Math. Soc. (1974), 49-57.
- [SaSh74] Saff, E. B. and Sheil-Small, T., *Coefficient and integral mean estimates for
  algebraic and trigonometric polynomials with restricted zeros*. J. London Math. Soc. (2)
  (1974/75), 16-22.
- [Kr76] Kristiansen, G. K., *Erratum to "Proof of a polynomial conjecture"*. Proc. Amer. Math.
  Soc. (1976), 377.
-/

@[expose] public section

open Set

namespace Erdos225

/-- The trigonometric polynomial $f(z) = \sum_{0\leq k\leq n}c_k e^{ikz}$, as an entire function
of $z\in\mathbb{C}$. -/
noncomputable def trigPoly (n : ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), c k * Complex.exp (Complex.I * (k * z))

/--
Let
$$ f(\theta) = \sum_{0\leq k\leq n}c_k e^{ik\theta}$$
be a trigonometric polynomial all of whose roots are real, such that
$\max_{\theta\in [0,2\pi]}\lvert f(\theta)\rvert=1$. Then
$$\int_0^{2\pi}\lvert f(\theta)\rvert \mathrm{d}\theta \leq 4.$$

This is Problem 4.20 in [Ha74], where it is attributed to Erdős.

This was solved independently by Kristiansen [Kr74] (only in the case when $c_k\in\mathbb{R}$)
and Saff and Sheil-Small [SaSh74] (for general $c_k\in \mathbb{C}$). (The original proof of
Kristiansen contained an error which was later fixed in [Kr76].)

"All roots real" refers to the zeros of $f$ as an entire function of $\theta\in\mathbb{C}$. We
normalise by $c_0c_n\neq 0$ and $n\geq 1$: a factor $e^{im\theta}$ affects neither the zeros nor
$\lvert f\rvert$ on the real line, while a single term $c_me^{im\theta}$ has no zeros and
$\int_0^{2\pi}\lvert f\rvert = 2\pi$.
-/
@[category research solved, AMS 30 42, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos225.lean#L2034"]
theorem erdos_225 : answer(True) ↔
    ∀ (n : ℕ) (c : ℕ → ℂ), 0 < n → c 0 ≠ 0 → c n ≠ 0 →
    (∀ z : ℂ, trigPoly n c z = 0 → z.im = 0) →
    (∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), ‖trigPoly n c θ‖ ≤ 1) →
    (∃ θ ∈ Icc (0 : ℝ) (2 * Real.pi), ‖trigPoly n c θ‖ = 1) →
    ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖trigPoly n c θ‖ ≤ 4 := by
  sorry

end Erdos225
