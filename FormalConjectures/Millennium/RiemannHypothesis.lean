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
Dirichlet characters. The Extended Riemann Hypothesis extends it to Dedekind zeta functions of
number fields.

*References:*
- [The Clay Institute](https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf)
- L. Alpöge, [Note on the Riemann Hypothesis](https://alpo.ge/remark.pdf), 2026. Announces a
  Lean proof of the Riemann Hypothesis and the Generalized Riemann Hypothesis.
- [Wikipedia: Riemann hypothesis](https://en.wikipedia.org/wiki/Riemann_hypothesis)
- [Wikipedia: Generalized Riemann hypothesis](https://en.wikipedia.org/wiki/Generalized_Riemann_hypothesis)
- [Wikipedia: Dedekind zeta function](https://en.wikipedia.org/wiki/Dedekind_zeta_function)
- J. Neukirch, *Algebraic Number Theory*, Springer (Grundlehren 322), 1999, Chapter VII, §5.
- D. A. Marcus, *Number Fields*, Springer (GTM 81), 1977, Chapter VII.
-/

@[expose] public section

namespace RiemannHypothesis

set_option linter.style.formal_proof_palomar false in
/-- The **Riemann Hypothesis**: all non-trivial zeros of the Riemann zeta function have real
part $\frac{1}{2}$. That is, if $\zeta(s) = 0$, $s \neq 1$, and $s$ is not a trivial zero
$-2(n+1)$ for some $n \in \mathbb{N}$, then $\operatorname{Re}(s) = \frac{1}{2}$.

This is the official Millennium Prize Problem as posed by the
[Clay Mathematics Institute](https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf).

This uses the `RiemannHypothesis` type from Mathlib, which is defined as
`∀ (s : ℂ), riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2`. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/leanprover-community/riemann-hypothesis"]
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

set_option linter.style.formal_proof_palomar false in
/-- The **Generalized Riemann Hypothesis** asserts that all the non-trivial zeros of the
Dirichlet $L$-function $L(\chi, s)$ of a primitive Dirichlet character $\chi$ have real part
$\frac{1}{2}$.

The linked proof states this for the zeros with $0 < \operatorname{Re}(s) < 1$. Our statement
follows by combining it with the
[bridge theorem](https://github.com/leanprover-community/riemann-hypothesis/blob/d27f71347abceb76cd37dc8a5fccbe556ec2be90/comparator/FormalConjecturesBridge.lean#L152). -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/leanprover-community/riemann-hypothesis/blob/d27f71347abceb76cd37dc8a5fccbe556ec2be90/src/Main.lean#L54"]
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

namespace ERH

/-- `Z` is a Dedekind zeta function of the number field `K`: it is holomorphic away from $s = 1$
and agrees with the Dedekind zeta series of `K` on $\operatorname{Re} s > 1$, where that series
converges. Such a `Z` is uniquely determined on $\mathbb{C} \setminus \{1\}$.

Mathlib's `NumberField.dedekindZeta` is only the Dirichlet series. Outside
$\operatorname{Re} s > 1$ it takes the junk value $0$, so we quantify over continuations
instead. -/
def IsDedekindZeta (K : Type*) [Field K] [NumberField K] (Z : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Z {1}ᶜ ∧ ∀ s : ℂ, 1 < s.re → Z s = NumberField.dedekindZeta K s

/-- The **Extended Riemann Hypothesis** for a number field $K$: every zero of (the analytic
continuation of) the Dedekind zeta function $\zeta_K$ in the critical strip
$0 < \operatorname{Re} s < 1$ has real part $\frac{1}{2}$. -/
def ExtendedRiemannHypothesis (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ Z : ℂ → ℂ, IsDedekindZeta K Z → ∀ s : ℂ, 0 < s.re → s.re < 1 → Z s = 0 → s.re = 1 / 2

/-- The **Extended Riemann Hypothesis**: for every number field $K$, all zeros of the Dedekind
zeta function $\zeta_K$ in the critical strip $0 < \operatorname{Re} s < 1$ have real part
$\frac{1}{2}$. -/
@[category research open, AMS 11]
theorem extended_riemann_hypothesis (K : Type*) [Field K] [NumberField K] :
    ExtendedRiemannHypothesis K := by
  sorry

end ERH
