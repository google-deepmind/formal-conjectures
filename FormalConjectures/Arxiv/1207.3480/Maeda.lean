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
# Maeda's conjecture

*Reference:* [arxiv/1207.3480](https://arxiv.org/abs/1207.3480)
**Experimental evidence for Maeda's conjecture on modular forms**
by *Alexandru Ghitza, Angus McAndrew*

The conjecture is due to Maeda and was first published in H. Hida and Y. Maeda,
*Non-abelian base change for totally real fields*, Pacific J. Math. 181 (1997), Special Issue,
189–217, Conjecture 1.2. The reference above states it as Conjecture 1.1: let $m > 1$ and let $F$
be the characteristic polynomial of the Hecke operator $T_m$ acting on $S_k$, the space of cusp
forms of weight $k$ and level one. Then (1) the polynomial $F$ is irreducible over $\mathbb{Q}$, and
(2) the Galois group of the splitting field of $F$ is the full symmetric group $S_d$, where $d$ is
the dimension of $S_k$. The paper verifies the conjecture for every weight $k \leq 12000$ and
every $n$ with $2 \leq n \leq 10000$, as well as for many larger primes $n$ (Theorem 1.5; the
abstract says "less than 12000", but the theorem and the reported computation include
$k = 12000$).

The Hecke operators `CuspForm.heckeOperatorₗ` and their characteristic polynomials
`CuspForm.heckeCharpoly` are defined in
`FormalConjecturesForMathlib/NumberTheory/ModularForms/Hecke/`. The characteristic polynomial
classically has rational coefficients, so it comes from a rational polynomial, which is unique
(`CuspForm.eq_of_map_eq_heckeCharpoly`); its existence is not formalised here. The *Maeda
property*, that this rational polynomial is irreducible with Galois group $S_d$, is defined
below. The sanity checks about it are stated with `sorry`: their proofs rest on the rationality
of the characteristic polynomial.
-/

namespace Arxiv.«1207.3480»

open CuspForm Module Polynomial

open scoped MatrixGroups

/-- **The Maeda property** for `T_n` acting on `S_k`: the characteristic polynomial of `T_n` is
`P.map (algebraMap ℚ ℂ)` for a rational polynomial `P` which is irreducible over `ℚ` and whose
Galois group (the Galois group of its splitting field over `ℚ`) is isomorphic to the symmetric
group on `dim_ℂ S_k` letters.

The rational polynomial `P` is unique (`CuspForm.eq_of_map_eq_heckeCharpoly`); that it exists,
i.e. that the characteristic polynomial has rational coefficients, is classical but not
formalised here. -/
def HasMaedaProperty (k : ℤ) (n : ℕ) : Prop :=
  ∃ P : ℚ[X], P.map (algebraMap ℚ ℂ) = heckeCharpoly k n ∧ Irreducible P ∧
    Nonempty (P.Gal ≃* Equiv.Perm (Fin (finrank ℂ (CuspForm 𝒮ℒ k))))

/-- The Maeda property in `∀`-form: whichever rational polynomial gives the characteristic
polynomial, it is irreducible with full symmetric Galois group. -/
@[category API, AMS 11]
theorem hasMaedaProperty_iff_forall (k : ℤ) (n : ℕ) :
    HasMaedaProperty k n ↔ ∀ P : ℚ[X], P.map (algebraMap ℚ ℂ) = heckeCharpoly k n →
      Irreducible P ∧ Nonempty (P.Gal ≃* Equiv.Perm (Fin (finrank ℂ (CuspForm 𝒮ℒ k)))) := by
  sorry

/--
**Maeda's conjecture.** For every even weight $k$ with $S_k \neq 0$ and every $n \geq 2$, the
characteristic polynomial of the Hecke operator $T_n$ acting on $S_k$ is irreducible over
$\mathbb{Q}$, and the Galois group of its splitting field is the symmetric group on
$\dim_{\mathbb{C}} S_k$ letters.

The hypothesis $S_k \neq 0$ excludes the degenerate weights, where the characteristic polynomial
is the constant $1$ and is not irreducible; $k$ even is automatic from $S_k \neq 0$ but is kept
explicit, as in the sources.
-/
@[category research open, AMS 11]
theorem maeda_conjecture (k : ℕ) (hk : Even k) (hS : 0 < finrank ℂ (CuspForm 𝒮ℒ k)) (n : ℕ)
    (hn : 2 ≤ n) : HasMaedaProperty k n := by
  sorry

/--
**Maeda's conjecture for $T_2$**, the case $n = 2$ of `maeda_conjecture` and the form in which the
conjecture is usually tested: for every even weight $k$ with $S_k \neq 0$, the characteristic
polynomial of $T_2$ acting on $S_k$ is irreducible over $\mathbb{Q}$ with Galois group
$S_{\dim S_k}$. Ghitza and McAndrew verify it for all $k \leq 12000$ (Theorem 1.5).
-/
@[category research open, AMS 11]
theorem maeda_conjecture_two (k : ℕ) (hk : Even k) (hS : 0 < finrank ℂ (CuspForm 𝒮ℒ k)) :
    HasMaedaProperty k 2 := by
  sorry

/-- On a one-dimensional space the Maeda property holds for every `n`: the characteristic
polynomial is linear, hence irreducible with trivial Galois group `S_1`. -/
@[category API, AMS 11]
theorem hasMaedaProperty_of_finrank_eq_one (k : ℤ) (n : ℕ) (h : finrank ℂ (CuspForm 𝒮ℒ k) = 1) :
    HasMaedaProperty k n := by
  sorry

/--
In weight $12$ the space $S_{12}$ is one-dimensional, spanned by $\Delta$, so the characteristic
polynomial of every $T_n$ is linear: irreducible, with trivial Galois group $S_1$.
-/
@[category test, AMS 11]
theorem hasMaedaProperty_twelve (n : ℕ) : HasMaedaProperty 12 n := by
  sorry

end Arxiv.«1207.3480»
