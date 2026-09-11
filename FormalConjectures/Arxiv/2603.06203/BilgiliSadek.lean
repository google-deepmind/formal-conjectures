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

import FormalConjecturesUtil

/-!
# Rational Periodic Points of Quadratic Rational Maps with Nonabelian Automorphism Groups

*Reference:* [arxiv/2603.06203](https://arxiv.org/abs/2603.06203)
**Rational Preperiodic Points of Quadratic Rational Maps over $\mathbb{Q}$ with Nonabelian
Automorphism Groups**
by *Hasan Bilgili, Mohammad Sadek*

This file formalises Conjecture 1.2 from the paper, which is an instance of the
Morton-Silverman Uniform Boundedness Conjecture (1994) in arithmetic dynamics.

## Note on the domain of definition

The conjecture in the paper is stated for a rational map $f : \mathbb{P}^1 \to \mathbb{P}^1$
defined over $\mathbb{Q}$. A fully faithful formalization would use the projective line
(e.g. `ProjectiveSpace ℚ 1`), which includes the point at infinity and correctly handles poles.

For simplicity, we work over `ℚ` and add an explicit **no-pole hypothesis**: the predicate
`IsRationalPeriodicPtOfPeriod` requires that the entire forward orbit of `z` avoids the
denominator zeros of `normalFormMap k d`. This makes the statement conservative — it only
captures periodic orbits that stay in `ℚ` away from poles — but it is still faithful for
the generic case. Cycles that pass through the point at infinity are not captured by this
formalization.
-/

namespace Arxiv.«2603.06203»

open Function

/-
## Normal form of quadratic rational maps with $\mathrm{Aut}(f) \cong S_3$

Every quadratic rational map $f : \mathbb{P}^1 \to \mathbb{P}^1$ defined over $\mathbb{Q}$
with automorphism group $\mathrm{Aut}(f) \cong S_3$ is conjugate over $\mathbb{Q}$ to a map
of the normal form

$$f_{k,d}(z) = \frac{kz^2 - 2dz + d}{kz^2 - 2kz + d}$$

for some $k, d \in \mathbb{Q}$ with $d \neq 0$ and $k^2 \neq d$.
-/

/-- The normal-form rational map $f_{k,d}(z) = \frac{kz^2 - 2dz + d}{kz^2 - 2kz + d}$
associated with a quadratic rational map over $\mathbb{Q}$ whose automorphism group is
isomorphic to $S_3$.

**Remark:** This is defined as a function `ℚ → ℚ` using Lean's field division. In Lean,
`x / 0 = 0`, so any `z` that is a pole of the map (i.e. makes the denominator zero) is
silently sent to `0` instead of `∞`. See `normalFormDenom` and `IsRationalPeriodicPtOfPeriod`
for how we handle this. -/
noncomputable def normalFormMap (k d : ℚ) (z : ℚ) : ℚ :=
  (k * z ^ 2 - 2 * d * z + d) / (k * z ^ 2 - 2 * k * z + d)

/-- The denominator of the normal-form map $f_{k,d}$ at $z$:
$$\mathrm{denom}_{k,d}(z) = kz^2 - 2kz + d$$
The map has a pole at $z$ iff this value is zero. -/
def normalFormDenom (k d z : ℚ) : ℚ := k * z ^ 2 - 2 * k * z + d

/-- A rational number $z$ is a *rational periodic point of exact period $N$* for $f_{k,d}$
if:
- the minimal period of $z$ under `normalFormMap k d` is exactly $N$, and
- the entire forward orbit of $z$ avoids the poles, i.e. `normalFormDenom k d` is nonzero at
  every iterate `(normalFormMap k d)^[n] z`.

The second condition is required because `normalFormMap` is defined on `ℚ` (not on
`ℙ¹(ℚ)`), and Lean's `x / 0 = 0` would otherwise silently corrupt the dynamics at poles. -/
def IsRationalPeriodicPtOfPeriod (k d : ℚ) (N : ℕ) (z : ℚ) : Prop :=
  (normalFormMap k d).IsPeriodicPt N z ∧
  minimalPeriod (normalFormMap k d) z = N ∧
  ∀ n : ℕ, normalFormDenom k d ((normalFormMap k d)^[n] z) ≠ 0

/-
## Bilgili-Sadek Conjecture (Conjecture 1.2)
-/

/-- **Conjecture 1.2 (Bilgili-Sadek, 2026).** Let $f : \mathbb{P}^1 \to \mathbb{P}^1$ be a
rational map of degree $2$ defined over $\mathbb{Q}$ with automorphism group
$\mathrm{Aut}(f) \cong S_3$. Then $f$ has no rational periodic point of exact period $N > 3$.

Equivalently, for all $k, d \in \mathbb{Q}$ with $d \neq 0$ and $k^2 \neq d$, the normal-form
map $f_{k,d}(z) = \frac{kz^2 - 2dz + d}{kz^2 - 2kz + d}$ admits no $\mathbb{Q}$-rational
periodic point of exact period $N \geq 4$.

This is an instance of the Morton-Silverman Uniform Boundedness Conjecture (1994),
and the nonabelian-automorphism analogue of Poonen's conjecture (1998) for quadratic
polynomials and Manes' conjecture (2008) for maps with $\mathrm{Aut}(f) \cong \mathbb{Z}/2\mathbb{Z}$.

*Reference:* Conjecture 1.2, p. 2 of [arxiv/2603.06203](https://arxiv.org/abs/2603.06203).

**Note on formalization:** We work over `ℚ` (not over `ℙ¹(ℚ)`). The predicate
`IsRationalPeriodicPtOfPeriod` includes a no-pole condition ensuring the orbit stays in `ℚ`
away from denominators zeros. This captures all periodic orbits in `ℚ` that avoid poles, but
does not account for cycles passing through the point at infinity. -/
@[category research open, AMS 11 37]
theorem bilgili_sadek_conjecture :
    ∀ (k d : ℚ), d ≠ 0 → k ^ 2 ≠ d →
    ∀ (N : ℕ), 4 ≤ N →
    ∀ (z : ℚ), ¬ IsRationalPeriodicPtOfPeriod k d N z := by
  sorry

/-
## Known partial results (Theorem 1.1, Bilgili-Sadek)
-/

/-- **Theorem 1.1(i) (Bilgili-Sadek, 2026).** No map $f_{k,d}$ with $d \neq 0$ and $k^2 \neq d$
admits a $\mathbb{Q}$-rational periodic point of exact period $4$ or $5$.

This settles the conjecture for $N \in \{4, 5\}$.

*Reference:* Theorem 1.1(i), p. 2 of [arxiv/2603.06203](https://arxiv.org/abs/2603.06203). -/
@[category research solved, AMS 11 37]
theorem bilgili_sadek_period_4_5 :
    ∀ (k d : ℚ), d ≠ 0 → k ^ 2 ≠ d →
    ∀ (N : ℕ), N = 4 ∨ N = 5 →
    ∀ (z : ℚ), ¬ IsRationalPeriodicPtOfPeriod k d N z := by
  sorry

/-- **Theorem 1.1(ii) (Bilgili-Sadek, 2026).** At most finitely many parameter pairs $(k, d)$
with $d \neq 0$ and $k^2 \neq d$ give a map $f_{k,d}$ that admits a $\mathbb{Q}$-rational
periodic point of exact period $6$.

*Reference:* Theorem 1.1(ii), p. 2 of [arxiv/2603.06203](https://arxiv.org/abs/2603.06203). -/
@[category research solved, AMS 11 37]
theorem bilgili_sadek_period_6_finite :
    Set.Finite {p : ℚ × ℚ | p.2 ≠ 0 ∧ p.1 ^ 2 ≠ p.2 ∧
      ∃ z : ℚ, IsRationalPeriodicPtOfPeriod p.1 p.2 6 z} := by
  sorry

end Arxiv.«2603.06203»
