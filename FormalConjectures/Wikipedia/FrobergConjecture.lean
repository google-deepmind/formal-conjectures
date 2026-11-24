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
# The Fröberg conjecture on Hilbert series of generic ideals

Let $K$ be an infinite field (such as $\mathbb{C}$), let $R = K[x_1, \dots, x_n]$ be the
standard $\mathbb{N}$-graded polynomial ring in $n \ge 1$ variables, and fix positive degrees
$d_1, \dots, d_r \ge 1$. For homogeneous forms $f_j \in R_{d_j}$ generating
$I = (f_1, \dots, f_r)$, Fröberg [Fr85] proved a lexicographic lower bound for the quotient
Hilbert function $t \mapsto \dim_K (R / I)_t$ in terms of the power series
$$S_{n; d_1, \dots, d_r}(z) = \frac{\prod_{j=1}^r (1 - z^{d_j})}{(1 - z)^n}
  = \sum_{t=0}^{\infty} c_t z^t$$
truncated to zero from its first nonpositive coefficient onward, and conjectured that generic
forms achieve this bound in every degree. Over an infinite field $K$, generic achievement is
equivalent to the existence of at least one tuple $(f_1, \dots, f_r)$ achieving the bound.
Anick [An86] proved the conjecture for $n \le 3$ variables; $n \ge 4$ remains open in general.

The ideal Hilbert function `MvPolynomial.hilbertFunction` is defined in
`FormalConjecturesForMathlib.RingTheory.MvPolynomial.LexPlusPowers`.

*References:*
- [Wikipedia: Fröberg conjecture](https://en.wikipedia.org/wiki/Fr%C3%B6berg_conjecture)
- [Fr85] R. Fröberg, *An inequality for Hilbert series of graded algebras*, Math. Scand. **56**
  (1985), 117–144.
- [An86] D. J. Anick, *Thin algebras of embedding dimension three*, J. Algebra **100** (1986),
  235–259.
-/

@[expose] public section

namespace FrobergConjecture

/-- Coefficient $c_t$ of $z^t$ in $(1 - z)^{-n} \prod_{j=0}^{r-1} (1 - z^{d_j})$, obtained by
expanding $\prod_{j=0}^{r-1} (1 - z^{d_j})$ over subsets $S \subseteq \mathrm{Fin}\, r$ and
convolving with the coefficients $\binom{n + u - 1}{u}$ of $(1 - z)^{-n}$. -/
def frobergRawCoeff (n : ℕ) {r : ℕ} (d : Fin r → ℕ) (t : ℕ) : ℤ :=
  ∑ S ∈ (Finset.univ : Finset (Fin r)).powerset,
    if ∑ j ∈ S, d j ≤ t then
      (-1 : ℤ) ^ S.card *
        (Nat.choose (n + (t - ∑ j ∈ S, d j) - 1) (t - ∑ j ∈ S, d j) : ℤ)
    else 0

/-- Fröberg's predicted Hilbert function [Fr85, p. 120]: `frobergRawCoeff n d t` while all
coefficients `0 ≤ u ≤ t` are strictly positive, and `0` from the first nonpositive coefficient
onward (since $(R / I)_u = 0$ forces $(R / I)_t = 0$ for all $t \ge u$). -/
def frobergTruncatedCoeff (n : ℕ) {r : ℕ} (d : Fin r → ℕ) (t : ℕ) : ℕ :=
  if ∀ u ≤ t, 0 < frobergRawCoeff n d u then (frobergRawCoeff n d t).toNat else 0

/-- Degree-$t$ Hilbert function $\dim_K (K[x_1, \dots, x_n] / I)_t$ of the graded quotient by a
homogeneous ideal $I$, defined via `MvPolynomial.hilbertFunction`. -/
noncomputable def quotientHilbertFunction {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (t : ℕ) : ℕ :=
  Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin n) K t) -
    MvPolynomial.hilbertFunction I t

/-- For the zero ideal $\bot$, `quotientHilbertFunction` equals the dimension of the degree-$t$
homogeneous polynomial space. -/
@[category API, AMS 13 14]
theorem quotientHilbertFunction_bot {K : Type*} [Field K] (n t : ℕ) :
    quotientHilbertFunction (⊥ : Ideal (MvPolynomial (Fin n) K)) t =
      Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin n) K t) := by
  simp [quotientHilbertFunction, MvPolynomial.hilbertFunction_bot]

/-- With $r = 0$ generators, `frobergRawCoeff` recovers the coefficient $\binom{n + t - 1}{t}$
of $(1 - z)^{-n}$ for all $n, t \in \mathbb{N}$. -/
@[category API, AMS 13 14]
theorem frobergRawCoeff_empty (n t : ℕ) (d₀ : Fin 0 → ℕ) :
    frobergRawCoeff n d₀ t = (Nat.choose (n + t - 1) t : ℤ) := by
  simp [frobergRawCoeff]

/-- For $n = 2$ variables and three quadrics $d = (2, 2, 2)$, the raw coefficient turns
negative ($-2$) at degree $t = 3$. -/
@[category test, AMS 13 14]
theorem frobergRawCoeff_two_vars_three_quadrics_three :
    frobergRawCoeff 2 (fun _ : Fin 3 => 2) 3 = -2 := by
  decide

/-- For $n = 2$ variables and three quadrics $d = (2, 2, 2)$, Fröberg's truncated Hilbert
values in degrees $0, 1, 2, 3$ are $[1, 2, 0, 0]$. -/
@[category test, AMS 13 14]
theorem frobergTruncatedCoeff_two_vars_three_quadrics :
    List.ofFn (fun t : Fin 4 => frobergTruncatedCoeff 2 (fun _ : Fin 3 => 2) t) =
      [1, 2, 0, 0] := by
  decide

/-- **Fröberg's conjecture** over $\mathbb{C}$: for $n \ge 1$ variables and positive degrees
$d_1, \dots, d_r \ge 1$, there exist homogeneous polynomials $f_j \in \mathbb{C}[x_1, \dots, x_n]$
of degrees $d_j$ whose quotient Hilbert function equals `frobergTruncatedCoeff n d t` in every
degree $t \ge 0$. By Zariski semicontinuity of $\dim_{\mathbb{C}} I_t$ together with Fröberg's
lexicographic lower bound [Fr85], existence of one such tuple is equivalent to a nonempty
Zariski-open (generic) set of tuples achieving the bound. -/
@[category research open, AMS 13 14]
theorem froberg_conjecture (n r : ℕ) (hn : 1 ≤ n) (d : Fin r → ℕ) (hd : ∀ j, 1 ≤ d j) :
    ∃ f : Fin r → MvPolynomial (Fin n) ℂ,
      (∀ j, (f j).IsHomogeneous (d j)) ∧
      ∀ t : ℕ,
        quotientHilbertFunction (Ideal.span (Set.range f)) t =
          frobergTruncatedCoeff n d t := by
  sorry

/-- **Fröberg's conjecture over an infinite field** [Fr85, p. 120] (not stated separately on
Wikipedia): the same existence statement over an arbitrary infinite base field $K$. -/
@[category research open, AMS 13 14]
theorem froberg_conjecture.variants.infinite_field
    (K : Type*) [Field K] [Infinite K]
    (n r : ℕ) (hn : 1 ≤ n) (d : Fin r → ℕ) (hd : ∀ j, 1 ≤ d j) :
    ∃ f : Fin r → MvPolynomial (Fin n) K,
      (∀ j, (f j).IsHomogeneous (d j)) ∧
      ∀ t : ℕ,
        quotientHilbertFunction (Ideal.span (Set.range f)) t =
          frobergTruncatedCoeff n d t := by
  sorry

/-- **Anick's theorem** [An86] (not stated on Wikipedia): Fröberg's conjecture holds in
$1 \le n \le 3$ variables over every infinite field $K$. -/
@[category research solved, AMS 13 14]
theorem anick_three_variables
    (K : Type*) [Field K] [Infinite K]
    (n r : ℕ) (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (d : Fin r → ℕ) (hd : ∀ j, 1 ≤ d j) :
    ∃ f : Fin r → MvPolynomial (Fin n) K,
      (∀ j, (f j).IsHomogeneous (d j)) ∧
      ∀ t : ℕ,
        quotientHilbertFunction (Ideal.span (Set.range f)) t =
          frobergTruncatedCoeff n d t := by
  sorry

end FrobergConjecture
