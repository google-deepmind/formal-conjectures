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
# Gottschalk's surjunctivity conjecture

A group $G$ is *surjunctive* if every injective, continuous, $G$-equivariant map
$A^G \to A^G$ (for any finite alphabet $A$) is surjective.

Here equivariance is with respect to the left shift action of $G$ on $A^G$,
defined by $(g \cdot x)(h) = x(g^{-1} h)$, and continuity is with respect to
the product topology on $A^G$ (where $A$ carries the discrete topology).

Gottschalk's conjecture (1973) states that every group is surjunctive. It is false: an
internal OpenAI model gave counterexamples in September 2026 [OAI26a], [OAI26b].

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Surjunctive_group)
- Gottschalk, W. H. (1973), "Some general dynamical notions"
- [OAI26a] OpenAI, *A Counterexample to Kaplansky's Direct-Finiteness Conjecture in
  Characteristic Two*. OpenAI Math Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Characteristic-Two-September-23-2026/paper.pdf
- [OAI26b] OpenAI, *A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Odd
  Characteristic*. OpenAI Math Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Odd-Characteristic-September-26-2026/paper.pdf
-/

@[expose] public section

namespace GottschalkSurjunctivity

variable (G : Type*) [Group G]

/-- The left shift of `x : G → A` by `g : G`, defined by `(shift g x)(h) = x(g⁻¹ * h)`.
This is the standard left shift action of `G` on `A^G`. We define it as a plain function
rather than a `MulAction` instance to avoid conflict with the pointwise `Pi.instMulAction`. -/
def shift {A : Type*} (g : G) (x : G → A) : G → A :=
  fun h => x (g⁻¹ * h)

@[simp, category API, AMS 20 37]
theorem shift_apply {A : Type*} (g : G) (x : G → A) (h : G) :
    shift G g x h = x (g⁻¹ * h) := rfl

@[simp, category API, AMS 20 37]
theorem shift_one {A : Type*} (x : G → A) :
    shift G 1 x = x := by
  ext h; simp [shift]

@[category API, AMS 20 37]
theorem shift_mul {A : Type*} (g₁ g₂ : G) (x : G → A) :
    shift G (g₁ * g₂) x = shift G g₁ (shift G g₂ x) := by
  ext h; simp [shift, mul_assoc]

/-- A map `τ : (G → A) → (G → A)` is *equivariant* (with respect to the left shift action)
if `τ(shift g x) = shift g (τ x)` for all `g : G` and `x : G → A`. -/
def IsShiftEquivariant {A : Type*} (τ : (G → A) → (G → A)) : Prop :=
  ∀ (g : G) (x : G → A), τ (shift G g x) = shift G g (τ x)

/-- A group `G` is *surjunctive* if for every finite nonempty type `A`, every injective,
continuous, shift-equivariant map `(G → A) → (G → A)` is also surjective.

Continuity is with respect to the product topology on `G → A` where `A` carries the
discrete topology. -/
def IsSurjunctive : Prop :=
  ∀ (A : Type) [Fintype A] [Nonempty A] [TopologicalSpace A] [DiscreteTopology A]
    (τ : (G → A) → (G → A)),
    Continuous τ →
    IsShiftEquivariant G τ →
    Function.Injective τ →
    Function.Surjective τ

set_option linter.style.formal_proof_palomar false in
/-- **Gottschalk's surjunctivity conjecture** (1973): every group is surjunctive.
That is, for every group `G` and every finite alphabet `A`, every injective cellular
automaton on `A^G` is surjective.

This is false. It was disproved by an internal OpenAI model in September 2026 [OAI26a],
[OAI26b]; see `counter_gottschalk_surjunctivity` for the counterexample and for what the
linked Lean proof covers. -/
@[category research solved, AMS 20 37, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/OddKaplansky/Main.lean#L81"]
theorem gottschalk_surjunctivity_conjecture :
    ¬ ∀ (G : Type) [Group G], IsSurjunctive G := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- **Gottschalk's surjunctivity conjecture** is false: there is a group that is not
surjunctive.

There are a finite field $K$, a group $G$ and $a, b \in K[G]$ with $ab = 1$ and
$ba \neq 1$. The linear cellular automaton $x \mapsto (g \mapsto \sum_u b_u x(gu))$ on
$K^G$ is then injective but not surjective. In [OAI26a], $K$ has characteristic two and $G$
is finitely presented. In [OAI26b], $K$ has odd characteristic and $G$ is finitely
generated.

This was proved by an internal OpenAI model in September 2026. The linked Lean proof is for
[OAI26b]. It shows that the map above is injective and not surjective. That the map is
continuous and shift-equivariant, as `IsSurjunctive` requires, is not part of the linked
proof. -/
@[category research solved, AMS 20 37, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/OddKaplansky/Main.lean#L81"]
theorem counter_gottschalk_surjunctivity :
    ∃ (G : Type) (_ : Group G), ¬ IsSurjunctive G := by
  sorry

/-- Every finite group is surjunctive. This is a classical result: an injective
endomorphism of a finite set is surjective. -/
@[category textbook, AMS 20 37]
theorem isSurjunctive_of_finite (G : Type) [Group G] [Finite G] :
    IsSurjunctive G := by
  intro A _ _ _ _ τ _ _ hInj
  exact Finite.surjective_of_injective hInj

end GottschalkSurjunctivity
