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
# Rigidity of the Turing degrees

The Turing degrees of subsets of $\mathbb{N}$, ordered by Turing reducibility, form a partial
order $\mathcal{D}$. The rigidity problem asks whether $\mathcal{D}$ has a nontrivial
automorphism.

*References:*
- [JS77] C. G. Jockusch, Jr. and R. M. Solovay, *Fixed points of jump preserving automorphisms
  of degrees*, Israel J. Math. 26 (1977), 91–94.
- [NS80] A. Nerode and R. A. Shore, *Reducibility orderings: theories, definability and
  automorphisms*, Ann. Math. Logic 18 (1980), 61–89.
- [Sl08] T. A. Slaman, *Global properties of the Turing degrees and the Turing jump*, in
  Computational Prospects of Infinity, Part I, Lecture Notes Ser. Inst. Math. Sci. Natl. Univ.
  Singap. 14, World Scientific (2008), 83–101.
- [OAI26] OpenAI, *Rigidity of the Turing degrees*. OpenAI Math Release preprint (2026).
  https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf
-/

@[expose] public section

namespace TuringDegreeRigidity

/-- A subset of $\mathbb{N}$, given by its characteristic function. -/
abbrev Oracle := ℕ → Bool

/-- The characteristic function of an oracle, as a partial function. -/
def oracleFunction (A : Oracle) : ℕ →. ℕ := fun n => Part.some (if A n then 1 else 0)

/-- Turing reducibility of oracles. -/
def Reduces (A B : Oracle) : Prop := TuringReducible (oracleFunction A) (oracleFunction B)

instance : IsPreorder Oracle Reduces where
  refl A := TuringReducible.refl (oracleFunction A)
  trans _ _ _ h k := TuringReducible.trans h k

/-- The Turing degrees of subsets of $\mathbb{N}$. -/
def Degree := Antisymmetrization Oracle Reduces

instance : PartialOrder Degree :=
  @instPartialOrderAntisymmetrization Oracle
    { le := Reduces
      lt A B := Reduces A B ∧ ¬ Reduces B A
      lt_iff_le_not_ge _ _ := Iff.rfl
      le_refl A := TuringReducible.refl (oracleFunction A)
      le_trans _ _ _ h k := TuringReducible.trans h k }

/--
**Rigidity of the Turing degrees.** Every order automorphism of the Turing degrees is the
identity.

Nerode and Shore proved that every automorphism fixes some cone of degrees [NS80]; Slaman and
Woodin proved that every automorphism fixes all degrees above $\mathbf{0}''$ and that there are
only countably many automorphisms [Sl08]. An internal OpenAI model proved rigidity in September
2026 [OAI26].
-/
@[category research solved, AMS 3]
theorem turing_degree_rigidity : ∀ π : Degree ≃o Degree, ∀ a : Degree, π a = a := by
  sorry

/-- **Slaman–Woodin.** The Turing degrees have only countably many automorphisms [Sl08]. -/
@[category research solved, AMS 3]
theorem turing_degree_rigidity.variants.countable : Countable (Degree ≃o Degree) := by
  sorry

/-- Rigidity implies that there are only countably many automorphisms. -/
@[category test, AMS 3]
theorem countable_of_turing_degree_rigidity (h : type_of% turing_degree_rigidity) :
    type_of% turing_degree_rigidity.variants.countable := by
  have : Subsingleton (Degree ≃o Degree) :=
    ⟨fun π σ => DFunLike.ext _ _ fun a => (h π a).trans (h σ a).symm⟩
  infer_instance

end TuringDegreeRigidity
