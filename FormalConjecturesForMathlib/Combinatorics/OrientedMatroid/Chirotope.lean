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

public import Mathlib.Data.Sign.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

/-!
# Chirotopes (oriented matroids)

Mathlib has no oriented matroids (as of 2026). This file defines a *chirotope* of
rank `r` on the ground set `Fin n`: a map `χ : (Fin r → Fin n) → SignType`
(a sign `{-1, 0, +1}` per `r`-tuple) that is *alternating* and satisfies the
*3-term Grassmann–Plücker relations*. This encodes a rank-`r` oriented matroid on
`n` elements. A *uniform* chirotope is nonzero on all injective tuples (general
position). A *mutation* is a flippable `r`-subset; mutations correspond to the
*simplicial* cells (simplicial topes) of the associated pseudohyperplane
arrangement, bounded by exactly `r` hyperplanes. This is distinct from a *complete
cell* (a tope bounded by all `n` hyperplanes; see `IsCompleteCell` below).

*Reference:* A. Björner, M. Las Vergnas, B. Sturmfels, N. White, G. M. Ziegler,
*Oriented Matroids*, Encyclopedia of Mathematics and its Applications 46,
Cambridge University Press, 1993/1999.
-/

open Finset

namespace OrientedMatroid

variable {r n : ℕ}

/-- A *chirotope candidate* of rank `r` on the ground set `Fin n`: a map assigning
a sign in `{-1, 0, +1}` (a `SignType`) to every `r`-tuple of ground-set elements. -/
abbrev Chirotope (r n : ℕ) : Type := (Fin r → Fin n) → SignType

/-- **Alternating axiom.** Permuting the `r` slots of a tuple multiplies the sign
by the sign of the permutation (`perm_sign`). -/
def IsAlternating (χ : Chirotope r n) : Prop :=
  ∀ (t : Fin r → Fin n) (σ : Equiv.Perm (Fin r)),
    χ (t ∘ σ) = SignType.sign (Equiv.Perm.sign σ : ℤ) * χ t

/-- **Uniformity / non-degeneracy.** The sign is nonzero on every tuple whose `r`
entries are pairwise distinct: the general-position case (a uniform oriented
matroid, an arrangement with no special incidences). -/
def IsUniform (χ : Chirotope r n) : Prop :=
  ∀ t : Fin r → Fin n, Function.Injective t → χ t ≠ 0

/-- **3-term Grassmann–Plücker relations** (`satisfies_3term_gp`): for any two
ground-set elements `b₁ b₂` and any injective tuple `a` disjoint from `{b₁, b₂}`,
if `χ(b₁,a₂,…) = χ(a₁,b₂,a₃,…)` and `χ(b₂,a₂,…) = χ(b₁,a₁,a₃,…)`, then
`χ(a₁,…,a_r) = χ(b₁,b₂,a₃,…)`. -/
def Satisfies3TermGP (χ : Chirotope r n) : Prop :=
  ∀ (hr : 2 ≤ r) (b₁ b₂ : Fin n) (a : Fin r → Fin n),
    Function.Injective a → b₁ ∉ Set.range a → b₂ ∉ Set.range a → b₁ ≠ b₂ →
      let i0 : Fin r := ⟨0, by omega⟩
      let i1 : Fin r := ⟨1, by omega⟩
      χ (Function.update a i0 b₁) = χ (Function.update a i1 b₂) →
      χ (Function.update a i0 b₂) = χ (Function.update (Function.update a i0 (a i1)) i1 b₁) →
        χ a = χ (Function.update (Function.update a i0 b₁) i1 b₂)

/-- A **chirotope** of rank `r` on `Fin n`: alternating and satisfying the 3-term
Grassmann–Plücker relations. Encodes a rank-`r` oriented matroid on `n` elements. -/
def IsChirotope (r n : ℕ) (χ : Chirotope r n) : Prop :=
  IsAlternating χ ∧ Satisfies3TermGP χ

/-- A **uniform chirotope**: a chirotope that is additionally uniform. This is the
oriented matroid of an arrangement of `n` pseudohyperplanes in general position in
`ℙ^{r-1}`. -/
def IsUniformChirotope (r n : ℕ) (χ : Chirotope r n) : Prop :=
  IsChirotope r n χ ∧ IsUniform χ

/-- Negate the sign of `χ` on every tuple whose underlying `r`-set equals `I`
(keeping all other tuples fixed). Since a chirotope is alternating, this is the
natural "sign flip at `I`" (`flip_sign_at`). -/
def flipAt (χ : Chirotope r n) (I : Finset (Fin n)) : Chirotope r n :=
  fun t => if (Finset.univ.image t = I) then - χ t else χ t

/-- **Mutation (simplicial cell).** An `r`-subset `I` is a *mutation* of a uniform
chirotope `χ` if flipping the sign of `χ` on `I` again yields a uniform chirotope.
Mutations are the *flippable* `r`-subsets, in bijection with the simplicial cells
(simplicial topes) of the arrangement, bounded by exactly `r` hyperplanes. See
`IsCompleteCell` for the (different) notion bounded by all `n`. -/
def IsMutation (χ : Chirotope r n) (I : Finset (Fin n)) : Prop :=
  I.card = r ∧ IsUniformChirotope r n (flipAt χ I)

open Classical in
/-- The **number of mutations** (simplicial cells / simplicial topes) of `χ`: the
number of `r`-subsets of the ground set that are mutations. -/
noncomputable def numMutations (χ : Chirotope r n) : ℕ :=
  (Finset.univ.filter (fun I : Finset (Fin n) => IsMutation χ I)).card

/-! ### Topes and complete cells

A *tope* of an oriented matroid is a maximal covector: a full-support sign vector
`T : Fin n → SignType` (no zero entries) that is orthogonal to every circuit. For a
uniform rank-`r` chirotope every circuit is supported on an `(r+1)`-subset and its
signs are the alternating minors of the chirotope. Concretely, for an `(r+1)`-subset
`C = {c₀ < c₁ < … < c_r}` the circuit sign on `cⱼ` is
`(-1)^j · χ(c₀,…,ĉⱼ,…,c_r)` (delete the `j`-th element). A sign vector `T` is
*orthogonal* to a circuit `X` if either their supports meet in a coordinate where the
signs agree and in another where they disagree, or they are disjoint. On a full-support
`T` and a circuit the disjoint case cannot arise, so orthogonality means: `T` and `X`
agree on at least one coordinate of the circuit support and disagree on at least one.

A *complete cell* (Roudneff) is a tope `T` bounded by **all** `n` pseudohyperplanes:
flipping `T` at any single coordinate again gives a tope. This is strictly stronger
than a *mutation* / simplicial cell (bounded by exactly `r = d+1` hyperplanes) and is
the object of Roudneff's conjecture. Cf. `Complete_cells` logic of arXiv:2303.14212. -/

/-- A **tope candidate** on the ground set `Fin n`: a full-support sign vector, i.e. a
map `T : Fin n → SignType` with no zero entry (equivalently `T : Fin n → {-1, +1}`). -/
def IsSignVector (T : Fin n → SignType) : Prop := ∀ i, T i ≠ 0

/-- The signed **circuit** on an `(r+1)`-subset `C = {c₀ < … < c_r}` of the ground set,
evaluated at the `j`-th element `c_j`: the alternating minor
`(-1)^j · χ(c₀,…,ĉⱼ,…,c_r)`, where `c : Fin (r+1) → Fin n` lists `C` in increasing
order and `Fin.succAbove j` skips the `j`-th slot. Off the support the circuit is `0`
(handled in `IsOrthogonalToCircuit`). This is the standard cofactor formula giving the
oriented circuit of a uniform chirotope (BLSWZ99, Ch. 3). -/
def circuitSign (χ : Chirotope r n) (c : Fin (r + 1) → Fin n) (j : Fin (r + 1)) :
    SignType :=
  (-1) ^ (j : ℕ) * χ (fun k : Fin r => c (j.succAbove k))

/-- **Orthogonality of a full-support sign vector `T` to the circuit on `c`.** The
circuit is supported on the image of `c : Fin (r+1) → Fin n`. For a full-support `T`
the disjoint-support case never occurs, so the covector–circuit orthogonality axiom
reduces to: among the `r+1` support coordinates, the product `T · (circuit sign)` takes
the value `+1` on at least one and `-1` on at least one (an *agreement* and a
*disagreement*). Cf. `min(H, S) > 0` in the reference `Complete_cells`. -/
def IsOrthogonalToCircuit (χ : Chirotope r n) (T : Fin n → SignType)
    (c : Fin (r + 1) → Fin n) : Prop :=
  (∃ j, T (c j) * circuitSign χ c j = 1) ∧ (∃ j, T (c j) * circuitSign χ c j = -1)

/-- **`T` is a tope of `χ`.** A full-support sign vector that is orthogonal to every
circuit, i.e. a maximal covector of the oriented matroid. Circuits range over all
increasing `(r+1)`-tuples `c : Fin (r+1) → Fin n` (strictly monotone), one per
`(r+1)`-subset of the ground set. -/
def IsTope (χ : Chirotope r n) (T : Fin n → SignType) : Prop :=
  IsSignVector T ∧
    ∀ c : Fin (r + 1) → Fin n, StrictMono c → IsOrthogonalToCircuit χ T c

/-- **Complete cell (Roudneff).** A tope `T` of `χ` such that flipping `T` at *any*
single coordinate `i` again yields a tope: the cell is bounded by *all* `n`
pseudohyperplanes. This is the notion whose count Roudneff's conjecture bounds, and it
is strictly stronger than a mutation (`IsMutation`, bounded by exactly `r` hyperplanes).
-/
def IsCompleteCell (χ : Chirotope r n) (T : Fin n → SignType) : Prop :=
  IsTope χ T ∧ ∀ i : Fin n, IsTope χ (Function.update T i (- T i))

open Classical in
/-- The **number of complete cells** of `χ`, counted **up to antipode** (as cells in
projective space `ℙ^{r-1}`). If `T` is a complete cell then so is its antipode `-T`, and
`T`, `-T` are the two sign vectors of the *same* projective cell; the reference program
`Roudneff_cc` counts full-support topes and its bound is exactly twice the projective
bound `∑_{i} binomial(n-1, i)` of Conjecture 1.1. We therefore halve the count of
complete-cell sign vectors to count projective complete cells. -/
noncomputable def numCompleteCells (χ : Chirotope r n) : ℕ :=
  (Finset.univ.filter (fun T : Fin n → SignType => IsCompleteCell χ T)).card / 2

end OrientedMatroid
