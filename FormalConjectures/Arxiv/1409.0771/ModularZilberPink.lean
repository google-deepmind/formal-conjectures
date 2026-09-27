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
# Modular Zilber–Pink conjecture

The Zilber–Pink conjecture, formulated independently by Zilber and by Pink, predicts that a
subvariety of a (mixed) Shimura variety has only finitely many *atypical* intersections with
special subvarieties. This file states the case of the product $Y(1)^n$ of modular curves. The
modular $j$-function, CM points and the action of $\mathrm{GL}_2^+(\mathbb{Q})$ on the upper
half-plane are `ModularForm.j`, `UpperHalfPlane.IsCMPoint` and `UpperHalfPlane.moebius`.

## The ambient space

We identify $Y(1)$ with the affine line via the modular $j$-invariant, hence $Y(1)^n$ with
$\mathbb{A}^n_{\mathbb{C}} = \operatorname{Spec} \mathbb{C}[x_1, \dots, x_n]$. The ambient space
`Y1Pow n` is the underlying topological space of this scheme, the prime spectrum of the polynomial
ring with its Zariski topology. Its closed points are the maximal ideals, that is, the points of
$\mathbb{C}^n$ by the Nullstellensatz, and its remaining points are the generic points of the
irreducible subvarieties of $\mathbb{C}^n$. A point $x \in \mathbb{C}^n$ gives the closed point
`ofPoint x`, the ideal of polynomials vanishing at $x$.

## Special subvarieties

A *special subvariety* of $Y(1)^n$ is an irreducible component of a subvariety cut out by
equations of the two forms $x_i = \sigma$, with $\sigma$ a singular modulus, i.e.
$\sigma = j(\tau)$ for an imaginary quadratic $\tau \in \mathbb{H}$, and $\Phi_N(x_i, x_k) = 0$,
with $\Phi_N$ the modular polynomial of level $N$. Since the zero set of $\Phi_N$ is the image of
$z \mapsto (j(z), j(gz))$ for any $g \in \mathrm{GL}_2^+(\mathbb{Q})$ proportional to a primitive
integer matrix of determinant $N$, the complex points of the special subvarieties are equivalently
the images of the maps
$$\mathbb{H}^k \to \mathbb{C}^n, \qquad (z_1, \dots, z_k) \mapsto (x_1, \dots, x_n),$$
in which each coordinate $x_i$ is either a singular modulus $j(\sigma_i)$ or $j(g_i z_{l(i)})$
for some $g_i \in \mathrm{GL}_2^+(\mathbb{Q})$ and some $l(i) \in \{1, \dots, k\}$. We formalise
this second description, which does not require the modular polynomials: a special subvariety is
the Zariski closure in `Y1Pow n` of the closed points given by such an image. The equivalence of
the two descriptions, and the irreducibility of this closure, are taken from Section 3.2 of the
reference and are not formalised (see `IsSpecialSubvariety.isIrreducible`).

## The conjecture

A *subvariety* of $Y(1)^n$ is a nonempty irreducible closed subset, i.e. a term of
`TopologicalSpace.IrreducibleCloseds (Y1Pow n)`, and $\dim$ denotes Krull dimension. Given a
special subvariety $T \subseteq Y(1)^n$ and a subvariety $V \subseteq T$, a subvariety
$A \subseteq V$ is *atypical* for $V$ in $T$ if there is a special subvariety $S \subseteq T$ with
$A \subseteq V \cap S$ and
$$\dim A > \dim V + \dim S - \dim T,$$
i.e. the intersection $V \cap S$ is larger along $A$ than dimension counting in $T$ predicts. The
conjecture states that for every special subvariety $T$, every subvariety $V \subseteq T$
contains only finitely many maximal atypical subvarieties. The quantification over $T$ is part of
the statement: a subvariety contained in a proper special subvariety is atypical for itself in
$Y(1)^n$ (`isAtypical_univ_self_iff`), so the case $T = Y(1)^n$ alone concerns only the
subvarieties not contained in any proper special subvariety. That case, in the form Pink stated
it, and the optimal-subvariety formulation of Habegger–Pila are recorded as variants. The latter
uses the *special closure* $\langle A \rangle$, the smallest special subvariety containing $A$,
and the *defect* $\delta(A) = \dim \langle A \rangle - \dim A$: a subvariety $A \subseteq V$ is
*optimal* if every subvariety strictly between $A$ and $V$ has strictly larger defect.

The literature usually asks in the definition of atypicality that $A$ be an irreducible component
of $V \cap S$. Every atypical subvariety in the above sense is contained in such a component,
which is again atypical, so the maximal atypical subvarieties are the same for both definitions.

*Reference:* [arxiv/1409.0771](https://arxiv.org/abs/1409.0771)
**O-minimality and certain atypical intersections**
by *Philipp Habegger, Jonathan Pila*, Ann. Sci. Éc. Norm. Supér. (4) 49 (2016), 813–858.
Section 2 states the conjecture: Conjecture 2.2 (finitely many maximal atypical subvarieties,
for every special $T$), Definition 2.5 and Conjecture 2.6 (optimal subvarieties), and Lemma 2.7
(their equivalence); it notes that Conjecture 2.2 is on its face stronger than Pink's statement,
and that the two are equivalent for $Y(1)^n$ by the argument of Bombieri–Masser–Zannier.
Section 3.2 describes the special subvarieties of $Y(1)^n$.

*Further references:*
- [R. Pink, *A common generalization of the conjectures of André–Oort, Manin–Mumford, and
  Mordell–Lang*, preprint (2005)](https://people.math.ethz.ch/~pink/ftp/AOMMML.pdf)
- [B. Zilber, *Exponential sums equations and the Schanuel conjecture*, J. London Math. Soc. (2)
  65 (2002), 27–44](https://doi.org/10.1112/S0024610701002861)
- [P. Habegger, J. Pila, *Some unlikely intersections beyond André–Oort*, Compos. Math. 148
  (2012), 1–27](https://doi.org/10.1112/S0010437X11005604)
- [J. Pila, *O-minimality and the André–Oort conjecture for $\mathbb{C}^n$*, Ann. of Math. (2)
  173 (2011), 1779–1840](https://doi.org/10.4007/annals.2011.173.3.11)
- [J. Pila, *Point-counting and the Zilber–Pink conjecture*, Cambridge Tracts in Math. 228,
  Cambridge Univ. Press (2022)](https://doi.org/10.1017/9781009170314)
-/

open TopologicalSpace UpperHalfPlane ModularForm
open scoped MatrixGroups

namespace Arxiv.«1409.0771»

/- ### The ambient space $Y(1)^n$ -/

/-- The underlying Zariski space of $Y(1)^n \cong \mathbb{A}^n_{\mathbb{C}}$, i.e. of
$\operatorname{Spec} \mathbb{C}[x_1, \dots, x_n]$. Its closed points are the points of
$\mathbb{C}^n$; see `ofPoint`. -/
abbrev Y1Pow (n : ℕ) : Type := PrimeSpectrum (MvPolynomial (Fin n) ℂ)

/-- The closed point of $Y(1)^n$ corresponding to $x \in \mathbb{C}^n$: the maximal ideal of
polynomials vanishing at $x$. -/
noncomputable def ofPoint {n : ℕ} (x : Fin n → ℂ) : Y1Pow n := MvPolynomial.pointToPoint x

/- ### Special subvarieties -/

/-- A coordinate of a special subvariety of $Y(1)^n$ with $k$ free parameters
$z_1, \dots, z_k \in \mathbb{H}$ is either *fixed*, equal to the singular modulus $j(\sigma)$ of a
CM point $\sigma$, or *free*, equal to $j(g z_l)$ for one of the parameters $z_l$ and some
$g \in \mathrm{GL}_2^+(\mathbb{Q})$. -/
inductive SpecialCoordinate (k : ℕ)
  /-- The coordinate is the singular modulus $j(\sigma)$. -/
  | fixed (σ : ℍ) (hσ : IsCMPoint σ)
  /-- The coordinate is $j(g z_l)$. -/
  | free (l : Fin k) (g : GL(2, ℚ)⁺)

/-- The value of a special coordinate at the parameters $z \in \mathbb{H}^k$. -/
noncomputable def SpecialCoordinate.eval {k : ℕ} (z : Fin k → ℍ) : SpecialCoordinate k → ℂ
  | .fixed σ _ => j σ
  | .free l g => j (moebius g (z l))

/-- The complex points of the special subvariety with coordinates `φ`: the image of the map
$\mathbb{H}^k \to \mathbb{C}^n$ whose $i$-th coordinate is the special coordinate `φ i`. -/
def specialPoints {n k : ℕ} (φ : Fin n → SpecialCoordinate k) : Set (Fin n → ℂ) :=
  Set.range fun z : Fin k → ℍ ↦ fun i ↦ (φ i).eval z

/-- A subset $T$ of $Y(1)^n$ is a *special subvariety* if it is the Zariski closure of the set of
closed points $(x_1, \dots, x_n) \in \mathbb{C}^n$ in which each $x_i$ is either a singular modulus
$j(\sigma_i)$ or of the form $j(g_i z_{l(i)})$ with $g_i \in \mathrm{GL}_2^+(\mathbb{Q})$, for
parameters $z_1, \dots, z_k$ ranging over $\mathbb{H}^k$. In Section 3.2 of the reference, $T$ is
equivalently an irreducible component of a subvariety cut out by equations $x_i = \sigma$ with
$\sigma$ a singular modulus and $\Phi_N(x_i, x_k) = 0$ with $\Phi_N$ a modular polynomial, since
the zero set of $\Phi_N$ is the image of $z \mapsto (j(z), j(gz))$ for any
$g \in \mathrm{GL}_2^+(\mathbb{Q})$ proportional to a primitive integer matrix of determinant $N$.
That equivalence is not formalised. -/
def IsSpecialSubvariety {n : ℕ} (T : Set (Y1Pow n)) : Prop :=
  ∃ (k : ℕ) (φ : Fin n → SpecialCoordinate k), T = closure (ofPoint '' specialPoints φ)

/-- A point of $Y(1)^n$ is *special* if it is the closed point given by a tuple of singular moduli.
The special points are the special subvarieties of dimension zero. -/
def IsSpecialPoint {n : ℕ} (x : Y1Pow n) : Prop :=
  ∃ y : Fin n → ℂ, x = ofPoint y ∧ ∀ i, ∃ σ : ℍ, IsCMPoint σ ∧ y i = j σ

/- ### Atypical and optimal subvarieties -/

/-- The dimension of a subset `V ⊆ Y(1)^n`: the Krull dimension of `V` with the subspace
topology. -/
noncomputable abbrev dim {n : ℕ} (V : Set (Y1Pow n)) : WithBot ℕ∞ := topologicalKrullDim V

/-- Let `T` be a special subvariety and `V ⊆ T` a subvariety. A subvariety `A ⊆ V` is *atypical*
(for `V` in `T`) if there is a special subvariety `S ⊆ T` with `A ⊆ V ∩ S` and
$\dim A > \dim V + \dim S - \dim T$. The inequality is written without subtraction.

For `T = Set.univ` this is atypicality for `V` in $Y(1)^n$, since `dim Set.univ = n`
(`dim_univ`). -/
def IsAtypical {n : ℕ} (T : Set (Y1Pow n)) (V A : IrreducibleCloseds (Y1Pow n)) : Prop :=
  ∃ S, IsSpecialSubvariety S ∧ S ⊆ T ∧ (A : Set (Y1Pow n)) ⊆ (V : Set (Y1Pow n)) ∩ S ∧
    dim (V : Set (Y1Pow n)) + dim S < dim (A : Set (Y1Pow n)) + dim T

/-- The *special closure* $\langle A \rangle$ of `A ⊆ Y(1)^n`: the intersection of all special
subvarieties containing `A`. Since the irreducible components of an intersection of special
subvarieties are special (Section 3.2 of the reference), this is the smallest special subvariety
containing a subvariety `A`. -/
def specialClosure {n : ℕ} (A : Set (Y1Pow n)) : Set (Y1Pow n) :=
  ⋂₀ {T | IsSpecialSubvariety T ∧ A ⊆ T}

/-- The *defect* of a subvariety `A` is $\delta(A) = \dim \langle A \rangle - \dim A$.
A subvariety `A ⊆ V` is *optimal* (for `V`) if every subvariety `B` with `A ⊊ B ⊆ V` has
strictly larger defect, $\delta(B) > \delta(A)$. This is Definition 2.5 of the reference. The
inequality is written without subtraction, as
$\dim \langle A \rangle + \dim B < \dim \langle B \rangle + \dim A$. -/
def IsOptimal {n : ℕ} (V A : IrreducibleCloseds (Y1Pow n)) : Prop :=
  A ≤ V ∧ ∀ B : IrreducibleCloseds (Y1Pow n), A < B → B ≤ V →
    dim (specialClosure (A : Set (Y1Pow n))) + dim (B : Set (Y1Pow n))
      < dim (specialClosure (B : Set (Y1Pow n))) + dim (A : Set (Y1Pow n))

/- ### The conjecture -/

/--
**Modular Zilber–Pink conjecture.** For every special subvariety $T \subseteq Y(1)^n$, every
subvariety $V \subseteq T$ contains only finitely many maximal atypical subvarieties, where a
subvariety $A \subseteq V$ is atypical for $V$ in $T$ if there is a special subvariety
$S \subseteq T$ with $A \subseteq V \cap S$ and $\dim A > \dim V + \dim S - \dim T$.

This is Conjecture 2.2 of the reference for the Shimura variety $Y(1)^n$. The statement for
$T = Y(1)^n$ alone is weaker: a subvariety contained in a proper special subvariety, which then
has smaller dimension, is atypical for itself in $Y(1)^n$ (`isAtypical_univ_self_iff`), so that
case only concerns the subvarieties not contained in any proper special subvariety.
-/
@[category research open, AMS 11 14]
theorem modular_zilber_pink_conjecture (n : ℕ) (T : Set (Y1Pow n)) (hT : IsSpecialSubvariety T)
    (V : IrreducibleCloseds (Y1Pow n)) (hV : (V : Set (Y1Pow n)) ⊆ T) :
    {A | Maximal (IsAtypical T V) A}.Finite := by
  sorry

/--
**Pink's formulation.** If a subvariety $V \subseteq Y(1)^n$ is not contained in any proper
special subvariety, then the union of the intersections $V \cap T$ over all special subvarieties
$T$ of codimension greater than $\dim V$, i.e. with $\dim V + \dim T < n = \dim Y(1)^n$
(`topologicalKrullDim_Y1Pow`), is not Zariski dense in $V$. This is Pink's Conjecture 1.3 for the
Shimura variety $Y(1)^n$. "Proper" is encoded as `T ≠ Set.univ`, which is a special subvariety
(`isSpecialSubvariety_univ`).

It is the case $T = Y(1)^n$ of `modular_zilber_pink_conjecture`, which only concerns subvarieties
not contained in a proper special subvariety, in the form Pink stated it. The reference notes that
Conjecture 2.2 is on its face stronger, and that the two are equivalent for $Y(1)^n$ by the
argument of Bombieri–Masser–Zannier for $\mathbb{G}_m^n$; the equivalence is not formalised.
-/
@[category research open, AMS 11 14]
theorem modular_zilber_pink_conjecture.variants.pink (n : ℕ) (V : IrreducibleCloseds (Y1Pow n))
    (hV : ∀ T, IsSpecialSubvariety T → (V : Set (Y1Pow n)) ⊆ T → T = Set.univ) :
    closure ((V : Set (Y1Pow n)) ∩
      ⋃₀ {T | IsSpecialSubvariety T ∧ dim (V : Set (Y1Pow n)) + dim T < n}) ≠ V := by
  sorry

/--
**Optimal subvarieties formulation** (Habegger–Pila). Every subvariety $V \subseteq Y(1)^n$ has
only finitely many optimal subvarieties. This is Conjecture 2.6 of the reference, which is
equivalent to `modular_zilber_pink_conjecture` by its Lemma 2.7, using that $Y(1)^n$ is special
and that the irreducible components of intersections of special subvarieties are special; the
equivalence is not formalised.
-/
@[category research open, AMS 11 14]
theorem modular_zilber_pink_conjecture.variants.optimal (n : ℕ)
    (V : IrreducibleCloseds (Y1Pow n)) : {A | IsOptimal V A}.Finite := by
  sorry

/--
**André–Oort for $\mathbb{C}^n$.** A subvariety of $Y(1)^n$ containing a Zariski-dense set of
special points is special. This is the case of the Zilber–Pink conjecture concerning the
zero-dimensional special subvarieties; it was proved unconditionally by Pila (2011).
-/
@[category research solved, AMS 11 14]
theorem modular_zilber_pink_conjecture.variants.andre_oort (n : ℕ)
    (V : IrreducibleCloseds (Y1Pow n)) (h : closure {x ∈ V | IsSpecialPoint x} = V) :
    IsSpecialSubvariety (V : Set (Y1Pow n)) := by
  sorry

/- ### Sanity checks -/

/-- Special subvarieties are Zariski closed. -/
@[category API, AMS 11 14]
theorem IsSpecialSubvariety.isClosed {n : ℕ} {T : Set (Y1Pow n)}
    (hT : IsSpecialSubvariety T) : IsClosed T := by
  obtain ⟨k, φ, rfl⟩ := hT
  exact isClosed_closure

/-- Special subvarieties are subvarieties: the closure of the image of $\mathbb{H}^k$ under a
$j$-parametrisation is irreducible. -/
@[category API, AMS 11 14]
theorem IsSpecialSubvariety.isIrreducible {n : ℕ} {T : Set (Y1Pow n)}
    (hT : IsSpecialSubvariety T) : IsIrreducible T := by
  sorry

/-- $Y(1)^n$ is a special subvariety of itself, since $j$ is surjective. -/
@[category API, AMS 11 14]
theorem isSpecialSubvariety_univ (n : ℕ) : IsSpecialSubvariety (Set.univ : Set (Y1Pow n)) := by
  sorry

/-- The special subvarieties of dimension zero are exactly the special points. -/
@[category API, AMS 11 14]
theorem isSpecialSubvariety_singleton_iff {n : ℕ} (x : Y1Pow n) :
    IsSpecialSubvariety {x} ↔ IsSpecialPoint x := by
  sorry

/-- $Y(1)^n$ has dimension $n$: the Krull dimension of $\mathbb{C}[x_1, \dots, x_n]$ is $n$. -/
@[category API, AMS 14]
theorem topologicalKrullDim_Y1Pow (n : ℕ) : topologicalKrullDim (Y1Pow n) = n := by
  show topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin n) ℂ)) = n
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The dimension of $Y(1)^n$ as a subset of itself is $n$. -/
@[category API, AMS 14]
theorem dim_univ (n : ℕ) : dim (Set.univ : Set (Y1Pow n)) = n :=
  (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ (Y1Pow n)).isHomeomorph).trans
    (topologicalKrullDim_Y1Pow n)

/-- An atypical subvariety of `V` is contained in `V`. -/
@[category API, AMS 11 14]
theorem IsAtypical.le {n : ℕ} {T : Set (Y1Pow n)} {V A : IrreducibleCloseds (Y1Pow n)}
    (h : IsAtypical T V A) : A ≤ V :=
  let ⟨_, _, _, hA, _⟩ := h
  hA.trans Set.inter_subset_left

/-- An atypical subvariety for `V` in `T` is contained in `T`. -/
@[category API, AMS 11 14]
theorem IsAtypical.subset_special {n : ℕ} {T : Set (Y1Pow n)} {V A : IrreducibleCloseds (Y1Pow n)}
    (h : IsAtypical T V A) : (A : Set (Y1Pow n)) ⊆ T :=
  let ⟨_, _, hST, hA, _⟩ := h
  (hA.trans Set.inter_subset_right).trans hST

/-- A subvariety is atypical for itself in $Y(1)^n$ exactly when it is contained in a proper
special subvariety. This is why `modular_zilber_pink_conjecture` quantifies over the special
subvariety $T$: for $T = Y(1)^n$ the statement is trivial for such $V$. -/
@[category API, AMS 11 14]
theorem isAtypical_univ_self_iff {n : ℕ} (V : IrreducibleCloseds (Y1Pow n)) :
    IsAtypical Set.univ V V ↔
      ∃ T, IsSpecialSubvariety T ∧ (V : Set (Y1Pow n)) ⊆ T ∧ T ≠ Set.univ := by
  sorry

/-- A subset is contained in its special closure. -/
@[category API, AMS 11 14]
theorem subset_specialClosure {n : ℕ} (A : Set (Y1Pow n)) : A ⊆ specialClosure A :=
  Set.subset_sInter fun _ hT ↦ hT.2

/-- A special subvariety is its own special closure. -/
@[category API, AMS 11 14]
theorem specialClosure_eq_self {n : ℕ} {A : Set (Y1Pow n)} (hA : IsSpecialSubvariety A) :
    specialClosure A = A :=
  have hA' : A ∈ {T | IsSpecialSubvariety T ∧ A ⊆ T} := ⟨hA, subset_rfl⟩
  (Set.sInter_subset_of_mem hA').antisymm (subset_specialClosure A)

/-- An optimal subvariety of `V` is contained in `V`. -/
@[category API, AMS 11 14]
theorem IsOptimal.le {n : ℕ} {V A : IrreducibleCloseds (Y1Pow n)} (h : IsOptimal V A) : A ≤ V :=
  h.1

/-- Every subvariety is optimal for itself: no subvariety lies strictly between `V` and `V`. -/
@[category API, AMS 11 14]
theorem isOptimal_self {n : ℕ} (V : IrreducibleCloseds (Y1Pow n)) : IsOptimal V V :=
  ⟨le_rfl, fun _ hVB hBV ↦ (hVB.not_ge hBV).elim⟩

end Arxiv.«1409.0771»
