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
# Riemann Hypothesis and its generalizations

The Riemann Hypothesis asserts that all non-trivial zeros of the Riemann zeta function
$\zeta(s)$ have real part $\frac{1}{2}$. The trivial zeros are the negative even integers
$-2, -4, -6, \ldots$. The hypothesis is one of the seven Millennium Prize Problems
posed by the Clay Mathematics Institute.

The Generalized Riemann Hypothesis extends this to Dirichlet $L$-functions of primitive
Dirichlet characters.

The quasi-Riemann hypothesis is the weaker claim that there is a zero-free half-plane
$\operatorname{Re}(s) > \theta$ for some $\theta < 1$.

Note: the **Extended Riemann Hypothesis** (ERH) for Dedekind zeta functions is intentionally
**not** stated here. Mathlib's `NumberField.dedekindZeta` is the naive Dirichlet series
(`LSeries`), not a meromorphic continuation; outside the region of absolute convergence
`tsum` returns junk `0`, producing spurious zeros that make the naive foramlisation of the
conjecture provably false. The ERH should be added once Mathlib provides a meromorphic
continuation of the Dedekind zeta function.

*References:*
- [The Clay Institute](https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf)
- [Wikipedia: Riemann hypothesis](https://en.wikipedia.org/wiki/Riemann_hypothesis)
- [Wikipedia: Generalized Riemann hypothesis](https://en.wikipedia.org/wiki/Generalized_Riemann_hypothesis)
- [Wikipedia: Dedekind zeta function](https://en.wikipedia.org/wiki/Dedekind_zeta_function)
- J. Neukirch, *Algebraic Number Theory*, Springer (Grundlehren 322), 1999, Chapter VII, §5.
- D. A. Marcus, *Number Fields*, Springer (GTM 81), 1977, Chapter VII.
- OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\Re(s)>7/8$* (2026),
  [preprint](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf)
-/

@[expose] public section

namespace RiemannHypothesis

/-- The **Riemann Hypothesis**: all non-trivial zeros of the Riemann zeta function have real
part $\frac{1}{2}$. That is, if $\zeta(s) = 0$, $s \neq 1$, and $s$ is not a trivial zero
$-2(n+1)$ for some $n \in \mathbb{N}$, then $\operatorname{Re}(s) = \frac{1}{2}$.

This is the official Millennium Prize Problem as posed by the
[Clay Mathematics Institute](https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf).

This uses the `RiemannHypothesis` type from Mathlib, which is defined as
`∀ (s : ℂ), riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2`. -/
@[category research open, AMS 11]
theorem riemannHypothesis : RiemannHypothesis := by
  sorry

end RiemannHypothesis

namespace GRH

/-- Let $\chi$ be a Dirichlet character, `trivialZeros` is the set of trivial zeros of the
Dirichlet $L$-function of $\chi$ which is always a set of non-positive integers.
- $\chi = 1$ then the Dirichlet $L$-function is the Riemann zeta function, having trivial
  zeroes at all negative even integers (exclude $0$).
- $\chi$ is odd, then the trivial zeroes are the negative odd integers.
- $\chi \neq 1$ is even, then the trivial zeroes are the non-positive even integers. -/
def trivialZeros {q : ℕ} (χ : DirichletCharacter ℂ q) : Set ℤ :=
  if q = 1 then {-2 * (n + 1) | (n : ℕ) } else
    if χ.Odd then { -2 * n - 1 | (n : ℕ) } else
      { - 2 * n | (n : ℕ) }

/-- The **Generalized Riemann Hypothesis** asserts that all the non-trivial zeros of the
Dirichlet $L$-function $L(\chi, s)$ of a primitive Dirichlet character $\chi$ have real part
$\frac{1}{2}$. -/
@[category research open, AMS 11]
theorem generalized_riemann_hypothesis (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (s : ℂ) (hs : χ.LFunction s = 0)
    (hs_nontrivial : s ∉ Int.cast '' trivialZeros χ) :
    s.re = 1 / 2 := by
  sorry

/-- GRH for $\chi = 1$ is `RiemannHypothesis`. -/
@[category test, AMS 11]
theorem implies_riemannHypothesis :
    type_of% (generalized_riemann_hypothesis 1 1) ↔ RiemannHypothesis := by
  aesop (add simp [DirichletCharacter.isPrimitive_one_level_one, trivialZeros,
    RiemannHypothesis, riemannZeta_one_ne_zero])

end GRH

namespace QuasiRiemannHypothesis

/-- The **quasi-Riemann hypothesis**: there is $\theta < 1$ such that the Riemann zeta function
has no zeros in the half-plane $\operatorname{Re}(s) > \theta$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean#L29"]
theorem quasi_riemann_hypothesis : ∃ θ < 1, ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 := by
  sorry

/-- The **quasi-Riemann hypothesis for Dirichlet $L$-functions**: there is $\theta < 1$ such that
no Dirichlet $L$-function $L(\chi, s)$ has a zero in the half-plane $\operatorname{Re}(s) > \theta$.

The bound `θ` is uniform in the modulus `q` and the character `χ`. The point $s = 1$ is
excluded for the principal character, where $L(\chi, s)$ has a pole. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean#L19"]
theorem quasi_generalized_riemann_hypothesis :
    ∃ θ < 1, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      θ < s.re → ¬(χ = 1 ∧ s = 1) → χ.LFunction s ≠ 0 := by
  sorry

/-- The Riemann hypothesis implies the quasi-Riemann hypothesis with $\theta = 1/2$. -/
@[category test, AMS 11]
theorem of_riemannHypothesis (h : RiemannHypothesis) : type_of% quasi_riemann_hypothesis := by
  refine ⟨1 / 2, by norm_num, fun s hs hz => ?_⟩
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact riemannZeta_one_ne_zero hz
  have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    norm_num at hs
    linarith [n.cast_nonneg (α := ℝ)]
  exact hs.ne' (h s hz htriv hs1)

/-- The Dirichlet version implies the version for $\zeta$, taking $q = 1$. -/
@[category test, AMS 11]
theorem of_quasi_generalized_riemann_hypothesis
    (h : type_of% quasi_generalized_riemann_hypothesis) : type_of% quasi_riemann_hypothesis := by
  obtain ⟨θ, hθ, H⟩ := h
  refine ⟨θ, hθ, fun s hs => ?_⟩
  by_cases hs1 : s = 1
  · exact hs1 ▸ riemannZeta_one_ne_zero
  · simpa using H 1 1 s hs (by simp [hs1])

end QuasiRiemannHypothesis

/- NOTE: Extended Riemann Hypothesis
## Extended Riemann Hypothesis

The ERH for Dedekind zeta functions **cannot** currently be stated correctly because
`NumberField.dedekindZeta` in Mathlib is the naive `LSeries`, not the meromorphic
continuation.  Outside the region of absolute convergence (`re s > 1`), `tsum` returns
junk `0` for non-summable series.  A statement using the raw `dedekindZeta` therefore has
spurious "zeros" that make the conjecture provably **false**.

A correct formalisation requires a meromorphic continuation of the Dedekind zeta function
(analogous to how `ZMod.LFunction` extends the Dirichlet L-series).  Once Mathlib provides
this, the ERH should be added back here.
-/
