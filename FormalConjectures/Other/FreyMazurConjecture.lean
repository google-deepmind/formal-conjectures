/-
Copyright 2025 The Formal Conjectures Authors.

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
# The Frey–Mazur conjecture

If two elliptic curves over $\mathbb{Q}$ have isomorphic $p$-torsion Galois modules for a
prime $p > 17$, then they are isogenous.

*References:*
- [CF2022] John Cremona and Nuno Freitas. Global methods for the symplectic type of congruences
  between elliptic curves, Math. Comp. 91 (2022), 2925-2972, https://arxiv.org/abs/1910.12290
- [BT2016] Benjamin Bakker and Jacob Tsimerman. On the Frey–Mazur conjecture over low genus
  curves, https://arxiv.org/abs/1309.6568
- [KO1992] Alain Kraus and Joseph Oesterlé. Sur une question de B. Mazur,
  Mathematische Annalen 293 (1992), 259-275, https://doi.org/10.1007/BF01444715
- [Fisher2014] Tom Fisher. On families of 7- and 11-congruent elliptic curves,
  LMS J. Comput. Math. 17 (2014), 536-564, https://doi.org/10.1112/S1461157014000059
- [Fisher2021] Tom Fisher. On pairs of 17-congruent elliptic curves,
  https://arxiv.org/abs/2106.02033
-/

namespace FreyMazur

open WeierstrassCurve

/-- An algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$. -/
abbrev Qbar := AlgebraicClosure ℚ

noncomputable local instance : DecidableEq Qbar := Classical.decEq _

variable (E : Affine ℚ) (p : ℕ)

/-- The group of $\overline{\mathbb{Q}}$-points of an elliptic curve over $\mathbb{Q}$. -/
abbrev Points := (E.baseChange Qbar).Point

/-- The action of $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on
$E(\overline{\mathbb{Q}})$, given by acting on the coordinates of a point. -/
noncomputable def galoisMap (σ : Qbar ≃ₐ[ℚ] Qbar) : Points E →+ Points E :=
  Affine.Point.map (S := ℚ) (F := Qbar) (K := Qbar) σ.toAlgHom

/-- The $p$-torsion subgroup $E[p] \subseteq E(\overline{\mathbb{Q}})$. -/
noncomputable def torsion : AddSubgroup (Points E) :=
  (Submodule.torsionBy ℤ (Points E) p).toAddSubgroup

/-- A point of $E(\overline{\mathbb{Q}})$ lies in $E[p]$ if and only if it is killed by $p$. -/
@[category API, AMS 11 14]
theorem mem_torsion_iff {P : Points E} : P ∈ torsion E p ↔ (p : ℤ) • P = 0 :=
  Submodule.mem_torsionBy_iff _ _

/-- The Galois action on $E(\overline{\mathbb{Q}})$ restricts to the $p$-torsion $E[p]$. -/
@[category API, AMS 11 14]
theorem galoisMap_mem_torsion (σ : Qbar ≃ₐ[ℚ] Qbar) {P : Points E} (hP : P ∈ torsion E p) :
    galoisMap E σ P ∈ torsion E p := by
  rw [mem_torsion_iff] at hP ⊢
  rw [← map_zsmul, hP, map_zero]

/-- The action of $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on the
$p$-torsion $E[p]$. -/
noncomputable def galoisTorsion (σ : Qbar ≃ₐ[ℚ] Qbar) : torsion E p →+ torsion E p :=
  ((galoisMap E σ).comp (torsion E p).subtype).codRestrict _
    fun P ↦ galoisMap_mem_torsion E p σ P.2

/-- Two elliptic curves over $\mathbb{Q}$ are *$p$-congruent* if their $p$-torsion subgroups are
isomorphic as $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$-modules, that is, there is a group
isomorphism $E_1[p] \simeq E_2[p]$ commuting with the action of the Galois group.

This is the notion of congruence used in [CF2022]; no compatibility with the Weil pairing is
imposed, so both symplectic and antisymplectic congruences are allowed. -/
def IsCongruent (E₁ E₂ : Affine ℚ) (p : ℕ) : Prop :=
  ∃ e : torsion E₁ p ≃+ torsion E₂ p, ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (P : torsion E₁ p),
    e (galoisTorsion E₁ p σ P) = galoisTorsion E₂ p σ (e P)

/-- Every elliptic curve over $\mathbb{Q}$ is $p$-congruent to itself. -/
@[category test, AMS 11 14]
theorem isCongruent_self : IsCongruent E E p :=
  ⟨.refl _, fun _ _ ↦ rfl⟩

/-- The reduction modulo $\ell$ of a Weierstrass curve with integral coefficients. -/
def reduction (E : Affine ℤ) (l : ℕ) : Affine (ZMod l) := E.map (Int.castRingHom (ZMod l))

/-- Two elliptic curves over $\mathbb{Q}$, given by Weierstrass models with integral
coefficients, are isogenous if and only if their reductions have the same number of points over
$\mathbb{F}_\ell$ for all but finitely many primes $\ell$. This is the isogeny theorem of
Faltings, in the form of the Serre–Tate criterion, and we take it here as the definition of being
isogenous, since Mathlib does not yet have isogenies of elliptic curves.

Some remarks on the formalisation:

* `WeierstrassCurve.Affine.Point` is the group of nonsingular affine points together with the
  point at infinity, so for a prime $\ell$ of good reduction `Nat.card (reduction E l).Point` is
  $\#E(\mathbb{F}_\ell) = \ell + 1 - a_\ell(E)$, and the condition below compares the traces of
  Frobenius $a_\ell(E_1)$ and $a_\ell(E_2)$.
* A Weierstrass model with integral coefficients is singular modulo only finitely many primes,
  so the primes of bad reduction (and, for a non-minimal model, the primes where the model
  degenerates although the curve does not) are absorbed by "all but finitely many". In
  particular the condition does not depend on the choice of integral models, only on the two
  curves over $\mathbb{Q}$.
* `ZMod l` is a field exactly when `l` is prime, and the definition only looks at prime `l`. -/
def IsIsogenous (E₁ E₂ : Affine ℤ) : Prop :=
  {l : ℕ | l.Prime ∧ Nat.card (reduction E₁ l).Point ≠ Nat.card (reduction E₂ l).Point}.Finite

/-- Every elliptic curve over $\mathbb{Q}$ is isogenous to itself. -/
@[category test, AMS 11 14]
theorem isIsogenous_self (E : Affine ℤ) : IsIsogenous E E := by
  simp [IsIsogenous]

/-- **The Frey–Mazur conjecture.** If $E_1$ and $E_2$ are elliptic curves over $\mathbb{Q}$
whose $p$-torsion Galois modules are isomorphic for some prime $p > 17$, then $E_1$ and $E_2$
are isogenous. See Section 1 of [CF2022] and the abstract of [BT2016].

The bound is sharp as stated: there are pairs of non-isogenous elliptic curves over $\mathbb{Q}$
that are $p$-congruent for each of $p = 3, 5, 7, 11, 13, 17$ (see Section 1 of [CF2022]). The
first such pair for $p = 7$ is due to [KO1992], further families for $p = 7$ and $p = 11$ are
constructed in [Fisher2014], and a pair for $p = 17$ is given in [Fisher2021]. No example is
known for any prime $p \geq 19$. -/
@[category research open, AMS 11 14]
theorem frey_mazur_conjecture (E₁ E₂ : Affine ℤ) [(E₁.map (Int.castRingHom ℚ)).IsElliptic]
    [(E₂.map (Int.castRingHom ℚ)).IsElliptic] (hp : p.Prime) (hp17 : 17 < p)
    (h : IsCongruent (E₁.map (Int.castRingHom ℚ)) (E₂.map (Int.castRingHom ℚ)) p) :
    IsIsogenous E₁ E₂ := by
  sorry

/-- A uniform weakening of the Frey–Mazur conjecture, stated as in Section 1 of [CF2022]: there
is a constant $C$ such that $p$-congruent elliptic curves over $\mathbb{Q}$ are isogenous for
every prime $p > C$. This is implied by `frey_mazur_conjecture` with $C = 17$, and is also open.

[CF2022] states the conjecture with $C \geq 17$; that constraint is omitted here, since a
constant $C$ works if and only if `max C 17` does. -/
@[category research open, AMS 11 14]
theorem frey_mazur_conjecture.variants.uniform :
    ∃ C : ℕ, ∀ (p : ℕ) (E₁ E₂ : Affine ℤ), (E₁.map (Int.castRingHom ℚ)).IsElliptic →
      (E₂.map (Int.castRingHom ℚ)).IsElliptic → p.Prime → C < p →
      IsCongruent (E₁.map (Int.castRingHom ℚ)) (E₂.map (Int.castRingHom ℚ)) p →
      IsIsogenous E₁ E₂ := by
  sorry

end FreyMazur
