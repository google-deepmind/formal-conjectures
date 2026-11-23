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
# Brauer's $k(B)$ Conjecture

Given a prime $p$ and a finite group $G$, the complex irreducible characters
$\operatorname{Irr}(G)$ partition into $p$-blocks. Each $p$-block $B$ determines a conjugacy class
of defect $p$-subgroups $D \le G$. Setting $k(B) = |\operatorname{Irr}(B)|$, Brauer (1946, 1956)
conjectured the upper bound $k(B) \le |D|$.

Brauer and Feit (1959) proved the general quadratic bound $k(B) \le \frac{1}{4}|D|^2 + 1$. For
$p$-solvable groups, Nagao (1962) reduced the conjecture to the $k(GV)$ problem—bounding the
conjugacy class count of $V \rtimes G$ by $|V|$ when $G$ is a $p'$-group acting faithfully on a
finite elementary abelian $p$-group $V$—which was completed by Gluck, Magaard, Riese, and Schmid
(2004) building on Robinson and Thompson (1996). We formalize $p$-blocks via Osima's idempotent
criterion and defect groups via Brauer's defect-class characterization (Isaacs 1976, Chapter 15).

*References:*
- [Wikipedia: Brauer's k(B)](https://en.wikipedia.org/wiki/Brauer%27s_k%28B%29_conjecture)
- R. Brauer, *On blocks of characters of groups of finite order. II*, Proc. Natl. Acad. Sci.
  U.S.A. **32** (1946), 215–219.
- R. Brauer, *Zur Darstellungstheorie der Gruppen endlicher Ordnung*, Math. Z. **63** (1956),
  406–444.
- R. Brauer and W. Feit, *On the number of irreducible characters of finite groups in a given
  block*, Proc. Natl. Acad. Sci. U.S.A. **45** (1959), 361–365.
- H. Nagao, *On a conjecture of Brauer for $p$-solvable groups*, J. Math. Osaka City Univ. **13**
  (1962), 35–38.
- G. R. Robinson and J. G. Thompson, *On Brauer's $k(B)$-problem*, J. Algebra **184** (1996),
  1143–1160.
- D. Gluck, K. Magaard, U. Riese, and P. Schmid, *The solution of the $k(GV)$-problem*,
  J. Algebra **279** (2004), 694–719.
- I. M. Isaacs, *Character Theory of Finite Groups*, Academic Press, 1976, Ch. 15.
-/

@[expose] public section

namespace BrauerKBConjecture

/-- Subring of algebraic integers inside $\mathbb{C}$. -/
def AlgIntRing : Subring ℂ := (integralClosure ℤ ℂ).toSubring

/-- Membership $z \in R_{\mathfrak{P}}$ in the localization of `AlgIntRing` at an ideal
$\mathfrak{P}$. -/
def InLocalRing (P : Ideal AlgIntRing) (z : ℂ) : Prop :=
  ∃ a b : AlgIntRing, b ∉ P ∧ z * (b : ℂ) = (a : ℂ)

/-- Membership $z \in \mathfrak{P} R_{\mathfrak{P}}$ in the maximal ideal of the localized ring. -/
def InLocalMaxIdeal (P : Ideal AlgIntRing) (z : ℂ) : Prop :=
  ∃ a b : AlgIntRing, a ∈ P ∧ b ∉ P ∧ z * (b : ℂ) = (a : ℂ)

/-- Predicate that $\chi : G \to \mathbb{C}$ is the character of a finite-dimensional irreducible
complex representation of $G$. -/
def IsIrrCharacter (G : Type*) [Group G] [Fintype G] (χ : G → ℂ) : Prop :=
  ∃ (d : ℕ) (ρ : Representation ℂ G (Fin d → ℂ)),
    Representation.IsIrreducible ρ ∧ χ = ρ.character

open scoped Classical in
/-- Group-algebra coefficient at $g \in G$ of the central idempotent
$e_B = \sum_{\chi \in B} e_\chi$. -/
noncomputable def blockIdempotentCoeff {G : Type*} [Group G] [Fintype G]
    (B : Finset (G → ℂ)) (g : G) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ χ ∈ B, χ 1 * χ g⁻¹

open scoped Classical in
/-- Central character value $\omega_\chi(\hat{x}) = |\operatorname{cl}_G(x)| \chi(x) / \chi(1)$. -/
noncomputable def centralCharVal {G : Type*} [Group G] [Fintype G]
    (χ : G → ℂ) (x : G) : ℂ :=
  ((Finset.univ.filter (fun g : G => IsConj x g)).card : ℂ) * χ x / χ 1

/-- Osima's characterization (Isaacs 1976, Theorem 15.27) of a $p$-block
$B \subseteq \operatorname{Irr}(G)$ relative to a maximal ideal $\mathfrak{P}$ of `AlgIntRing`
containing $p$. -/
def IsPBlock {G : Type*} [Group G] [Fintype G]
    (p : ℕ) (P : Ideal AlgIntRing) (B : Finset (G → ℂ)) : Prop :=
  p.Prime ∧ P.IsMaximal ∧ (p : AlgIntRing) ∈ P ∧ B.Nonempty ∧
    (∀ χ ∈ B, IsIrrCharacter G χ) ∧
    (∀ g : G, InLocalRing P (blockIdempotentCoeff B g)) ∧
    ∀ B' ⊂ B, B'.Nonempty → ∃ g : G, ¬ InLocalRing P (blockIdempotentCoeff B' g)

/-- Brauer's defect-class characterization (Isaacs 1976, Definition 15.35) of a defect subgroup
$D \le G$ of a $p$-block $B$: $D$ is a Sylow $p$-subgroup of $C_G(x)$ for an element $x \in G$ whose
conjugacy class is a defect class for $B$. -/
def IsDefectGroup {G : Type*} [Group G] [Fintype G]
    (p : ℕ) (P : Ideal AlgIntRing) (B : Finset (G → ℂ)) (D : Subgroup G) : Prop :=
  IsPGroup p D ∧ ∃ x : G,
    ¬ InLocalMaxIdeal P (blockIdempotentCoeff B x) ∧
    (∃ χ ∈ B, ¬ InLocalMaxIdeal P (centralCharVal χ x)) ∧
    D ≤ Subgroup.centralizer {x} ∧
    ∀ Q : Subgroup G, IsPGroup p Q → D ≤ Q → Q ≤ Subgroup.centralizer {x} → Q = D

/-- An empty set of characters is never a $p$-block. -/
@[category test, AMS 20]
theorem not_isPBlock_empty (p : ℕ) (P : Ideal AlgIntRing) :
    ¬ IsPBlock p P (∅ : Finset (PUnit → ℂ)) := by
  rintro ⟨_, _, _, hne, _⟩
  simp at hne

/-- An empty set of characters admits no defect subgroup. -/
@[category test, AMS 20]
theorem not_isDefectGroup_empty (p : ℕ) (P : Ideal AlgIntRing) (D : Subgroup PUnit) :
    ¬ IsDefectGroup p P ∅ D := by
  rintro ⟨_, _, _, ⟨χ, hχ, _⟩, _⟩
  simp at hχ

/-- Every natural number belongs to `InLocalRing P` for any proper ideal `P ≠ ⊤`. -/
@[category API, AMS 20]
theorem inLocalRing_natCast (P : Ideal AlgIntRing) (hP : P ≠ ⊤) (n : ℕ) :
    InLocalRing P (n : ℂ) :=
  ⟨(n : AlgIntRing), 1, fun h1 => hP ((Ideal.eq_top_iff_one P).mpr h1), by simp⟩

/-- The unit `1 : ℂ` does not belong to `InLocalMaxIdeal ⊥`. -/
@[category test, AMS 20]
theorem not_inLocalMaxIdeal_bot_one :
    ¬ InLocalMaxIdeal ⊥ (1 : ℂ) := by
  rintro ⟨a, b, ha, hb, hmul⟩
  rw [Ideal.mem_bot] at ha
  subst ha
  have hb0 : (b : ℂ) = 0 := by simpa using hmul
  exact hb (Ideal.mem_bot.mpr (Subtype.ext hb0))

/-- For the singleton trivial character on `PUnit`, the block idempotent coefficient at `1` equals
`1`. -/
@[category test, AMS 20]
theorem blockIdempotentCoeff_singleton_unit :
    blockIdempotentCoeff ({fun _ : PUnit => (1 : ℂ)} : Finset (PUnit → ℂ)) 1 = 1 := by
  simp [blockIdempotentCoeff]

/-- On `PUnit`, the constant character `1` has central character value `1` at `1`. -/
@[category test, AMS 20]
theorem centralCharVal_punit_one :
    centralCharVal (fun _ : PUnit => (1 : ℂ)) 1 = 1 := by
  simp [centralCharVal]

/-- On `PUnit`, the constant function `1` is an irreducible complex character. -/
@[category test, AMS 20]
theorem isIrrCharacter_punit_one :
    IsIrrCharacter PUnit (fun _ => 1) := by
  let ρ : Representation ℂ PUnit (Fin 1 → ℂ) := 1
  have hbot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    have hsub := congr_arg Subrepresentation.toSubmodule h
    have hmem : (fun _ : Fin 1 => (1 : ℂ)) ∈ (⊤ : Subrepresentation ρ).toSubmodule := trivial
    rw [← hsub] at hmem
    have h0 : (fun _ : Fin 1 => (1 : ℂ)) = 0 := hmem
    exact one_ne_zero (congr_fun h0 0)
  have : Nontrivial (Subrepresentation ρ) := ⟨⊥, ⊤, hbot_ne_top⟩
  refine ⟨1, ρ, ⟨fun W => ?_⟩, ?_⟩
  · by_cases hW : W = ⊥
    · exact Or.inl hW
    · right
      apply Subrepresentation.toSubmodule_injective
      change W.toSubmodule = ⊤
      rw [eq_top_iff]
      have hW' : W.toSubmodule ≠ ⊥ := fun h => hW (Subrepresentation.toSubmodule_injective h)
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW'
      intro x _
      have hx : x = (x 0 / v 0) • v := by
        ext i; fin_cases i
        exact (div_mul_cancel₀ (x 0) (fun h0 => hv0 (by ext j; fin_cases j; exact h0))).symm
      rw [hx]
      exact W.toSubmodule.smul_mem (x 0 / v 0) hv
  · ext g
    simp [ρ, Representation.character]

/-- **Brauer's $k(B)$ Conjecture** (1946): For any finite group $G$, prime $p$, $p$-block $B$ of
$G$, and defect subgroup $D$ of $B$, the cardinality $|B|$ of ordinary characters in $B$ satisfies
$|B| \le |D|$. -/
@[category research open, AMS 20]
theorem brauer_kB_conjecture {G : Type} [Group G] [Fintype G]
    (p : ℕ) (P : Ideal AlgIntRing) (B : Finset (G → ℂ)) (D : Subgroup G)
    (hB : IsPBlock p P B) (hD : IsDefectGroup p P B D) :
    B.card ≤ Nat.card D := by
  sorry

/-- **Brauer–Feit Bound** (1959): For any finite group $G$, prime $p$, $p$-block $B$ of $G$, and
defect subgroup $D$ of $B$, $|B| \le \frac{1}{4}|D|^2 + 1$. Stated from Brauer and Feit (1959). -/
@[category research solved, AMS 20]
theorem brauer_feit_quadratic_bound {G : Type} [Group G] [Fintype G]
    (p : ℕ) (P : Ideal AlgIntRing) (B : Finset (G → ℂ)) (D : Subgroup G)
    (hB : IsPBlock p P B) (hD : IsDefectGroup p P B D) :
    (B.card : ℚ) ≤ (1 / 4 : ℚ) * (Nat.card D : ℚ) ^ 2 + 1 := by
  sorry

/-- **Solution of the $k(GV)$ Problem** (Gluck–Magaard–Riese–Schmid 2004): If $p$ is prime, $V$ is a
finite elementary abelian $p$-group, and $G$ is a finite group with $p \nmid |G|$ acting faithfully
on $V$ via $\varphi : G \to \operatorname{Aut}(V)$, then the number of conjugacy classes of the
semidirect product $V \rtimes_\varphi G$ is at most $|V|$. -/
@[category research solved, AMS 20]
theorem k_gv_theorem (p : ℕ) (hp : p.Prime)
    (V : Type) [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ p = 1)
    (G : Type) [Group G] [Finite G] (hcop : ¬ p ∣ Nat.card G)
    (φ : G →* MulAut V) (hfaith : Function.Injective φ) :
    Nat.card (ConjClasses (V ⋊[φ] G)) ≤ Nat.card V := by
  sorry

end BrauerKBConjecture
