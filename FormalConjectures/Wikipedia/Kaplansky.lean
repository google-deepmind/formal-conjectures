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
module

public import FormalConjecturesUtil

/-!
# Kaplansky's Conjectures

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Kaplansky%27s_conjectures)
* [Ka69] I. Kaplansky, *Fields and Rings*, Chicago Lectures in Mathematics, University of
  Chicago Press, 1969.
* [OAI26c] OpenAI, *A Counterexample to Kaplansky's Direct-Finiteness Conjecture in
  Characteristic Two*. OpenAI Math Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Characteristic-Two-September-23-2026/paper.pdf
* [OAI26a] OpenAI, *A Torsion-Free Group Algebra with Zero Divisors*. OpenAI Math Release
  preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026/paper.pdf

Throughout, "torsion-free" means that the identity is the only element of finite order
(`Monoid.IsTorsionFree`). This is weaker than Mathlib's `IsMulTorsionFree`, which asks for
uniqueness of roots and fails for the Promislow group below.
-/

@[expose] public section

variable (K : Type*) [Field K]
variable (G : Type*) [Group G] (hG : Monoid.IsTorsionFree G)
include hG

namespace Kaplansky

omit hG in
set_option linter.style.formal_proof_palomar false in
/--
**The zero-divisor conjecture**

If `G` is torsion-free, then the group algebra `K[G]` has no non-trivial zero divisors.

This is false. It was disproved by an internal OpenAI model in September 2026 [OAI26a], which
constructed a finitely presented torsion-free group $G$ and non-zero
$\alpha, \beta \in \mathbb{F}_2[G]$ with $\alpha \beta = 0$; see
`counter_zero_divisor_conjecture` and the linked Lean proof.
-/
@[category research solved, AMS 16 20, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/GroupRing/Main.lean#L13"]
theorem zero_divisor_conjecture :
    ¬ ∀ (K : Type) [Field K] (G : Type) [Group G], Monoid.IsTorsionFree G →
      NoZeroDivisors (MonoidAlgebra K G) := by
  sorry

/--
**The idempotent conjecture**

If `G` is torsion-free, then `K[G]` has no non-trivial idempotents.
-/
@[category research open, AMS 16 20]
theorem idempotent_conjecture (a : MonoidAlgebra K G) (h : IsIdempotentElem a) :
    a = 0 ∨ a = 1 := by
  sorry

variable {K G} in
/--
A unit in `K[G]` is trivial if it is exactly of the form `kg` where:
- `k` is a unit in the base field `K`
- `g` is an element of the group `G`
-/
def IsTrivialUnit (u : MonoidAlgebra K G) : Prop :=
  ∃ (k : Kˣ) (g : G), u = MonoidAlgebra.single g (k : K)

omit hG

@[category API, AMS 16 20]
lemma IsTrivialUnit.isUnit {u : MonoidAlgebra K G} (h : IsTrivialUnit u) : IsUnit u := by
  obtain ⟨k, g, rfl⟩ := h
  exact (Prod.isUnit_iff (x := (k.1, g)).mpr ⟨k.isUnit, Group.isUnit g⟩).map MonoidAlgebra.singleHom

/-  ## Counterexamples -/

/--
**The Promislow group** `⟨ a, b | b⁻¹a²ba², a⁻¹b²ab² ⟩`
-/
abbrev PromislowGroup : Type :=
  letI a := FreeGroup.of (0 : Fin 2)
  letI b := FreeGroup.of (1 : Fin 2)
  PresentedGroup {b⁻¹ * a * a * b * a * a, a⁻¹ * b * b * a * b * b}

/--
The Promislow group is torsion-free.
-/
@[category API, AMS 20]
lemma promislow_group_is_torsionfree :
    Monoid.IsTorsionFree PromislowGroup := by
  sorry

/--
If $P$ is the Promislow group, then the group ring $\mathbb{F}_p[P]$ has a non-trivial unit.
-/
@[category research solved, AMS 16 20]
theorem UnitConjecture.counterexamples.i (p : ℕ) [hp : Fact p.Prime] :
    ∃ (u : (MonoidAlgebra (ZMod p) PromislowGroup)ˣ), ¬IsTrivialUnit u.val := by
  sorry

/--
If $P$ is the Promislow group, then the group ring $\mathbb{C}[P]$ has a non-trivial unit.
-/
@[category research solved, AMS 16 20]
theorem UnitConjecture.counterexamples.ii :
    ∃ (u : (MonoidAlgebra ℂ PromislowGroup)ˣ), ¬IsTrivialUnit u.val := by
  sorry

/--
The **Unit Conjecture** is false.

At least there is a counterexample for any prime and zero characteristic:
[Mu21] Murray, A. (2021). More Counterexamples to the Unit Conjecture for Group Rings.
[Pa21] Passman, D. (2021). On the counterexamples to the unit conjecture for group rings.
[Ga24] Gardam, G. (2024). Non-trivial units of complex group rings.
-/
@[category research solved, AMS 16 20]
theorem counter_unit_conjecture :
    ∃ (G : Type) (_ : Group G) (_ : Monoid.IsTorsionFree G),
    ∀ (p : ℕ) (_ : p = 0 ∨ p.Prime),
    ∃ (K : Type) (_ : Field K) (_ :  CharP K p) (u : (MonoidAlgebra K G)ˣ), ¬IsTrivialUnit u.val :=
  ⟨PromislowGroup, _, promislow_group_is_torsionfree, fun p hp ↦
    hp.by_cases (by rintro rfl; exact ⟨ℂ, _, inferInstance, UnitConjecture.counterexamples.ii⟩)
      fun h ↦ have := Fact.mk h; ⟨ZMod p, _, inferInstance, UnitConjecture.counterexamples.i p⟩⟩

/--
There is a counterexample to **Unit Conjecture** in any characteristic.
-/
@[category research solved, AMS 16 20]
theorem counter_unit_conjecture_weak (p : ℕ) (hp : p = 0 ∨ p.Prime) :
    ∃ (G : Type) (_ : Group G) (_ : Monoid.IsTorsionFree G)
      (K : Type) (_ : Field K) (_ :  CharP K p) (u : (MonoidAlgebra K G)ˣ), ¬IsTrivialUnit u.val :=
  have ⟨G, _, _, hG⟩ := counter_unit_conjecture
  ⟨G, _, ‹_›, hG p hp⟩

/-! ## Direct finiteness -/

set_option linter.style.formal_proof_palomar false in
/--
**Kaplansky's direct finiteness conjecture** asserts that for every field $K$ and every group
$G$, the group algebra $K[G]$ is directly finite: $ab = 1$ implies $ba = 1$.

It is false. An internal OpenAI model found a finite field $K$ of characteristic two, a finitely
generated group $G$ and $a, b \in K[G]$ with $ab = 1$ and $ba \neq 1$ in September 2026
[OAI26c]; see `direct_finiteness_conjecture.variants.char_two` and the linked Lean proof.
-/
@[category research solved, AMS 16 20, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/DirectFiniteness/Main.lean#L9"]
theorem direct_finiteness_conjecture :
    ¬ ∀ (K : Type) [Field K] (G : Type) [Group G],
      IsDedekindFiniteMonoid (MonoidAlgebra K G) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
The counterexample of [OAI26c], as stated in the linked Lean proof: a finite field $K$ of
characteristic two, a finitely generated group $G$ and $a, b \in K[G]$ with $ab = 1$ and
$ba \neq 1$.
-/
@[category research solved, AMS 16 20, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/DirectFiniteness/Main.lean#L9"]
theorem direct_finiteness_conjecture.variants.char_two :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2),
      ∃ (G : Type) (_ : Group G) (_ : Group.FG G),
        ∃ a b : MonoidAlgebra K G, a * b = 1 ∧ b * a ≠ 1 := by
  sorry

/--
Kaplansky proved the conjecture for fields of characteristic zero [Ka69].
-/
@[category research solved, AMS 16 20]
theorem direct_finiteness_conjecture.variants.char_zero (K : Type*) [Field K] [CharZero K]
    (G : Type*) [Group G] : IsDedekindFiniteMonoid (MonoidAlgebra K G) := by
  sorry

/-- The counterexample of [OAI26c] refutes `direct_finiteness_conjecture`. -/
@[category test, AMS 16 20]
theorem direct_finiteness_conjecture_of_char_two
    (h : type_of% direct_finiteness_conjecture.variants.char_two) :
    type_of% direct_finiteness_conjecture := by
  intro hall
  obtain ⟨K, _, _, _, G, _, _, a, b, hab, hba⟩ := h
  exact hba ((isDedekindFiniteMonoid_iff _).mp (hall K G) hab)

set_option linter.style.formal_proof_palomar false in
/--
The **Zero-divisor Conjecture** is false: there is a finitely presented torsion-free group $G$
and non-zero $\alpha, \beta \in \mathbb{F}_2[G]$ with $\alpha \beta = 0$.

This was proved by an internal OpenAI model in September 2026 [OAI26a]; see the linked Lean
proof.
-/
@[category research solved, AMS 16 20, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/GroupRing/Main.lean#L13"]
theorem counter_zero_divisor_conjecture :
    ∃ (G : Type) (_ : Group G) (_ : Monoid.IsTorsionFree G) (_ : Group.IsFinitelyPresented G)
      (α β : MonoidAlgebra (ZMod 2) G), α ≠ 0 ∧ β ≠ 0 ∧ α * β = 0 := by
  sorry

end Kaplansky
