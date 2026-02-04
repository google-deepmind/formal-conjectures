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

import FormalConjectures.Util.ProblemImports

/-!
# Conjectures about Weakly First Countable spaces

This file formalizes the notion of a weakly first countable topological space and some conjectures
around those.

*References:*
* [Ar2013] Arhangeliski, Alexandr. "Selected old open problems in general topology."
  Buletinul Academiei de Ştiinţe a Republicii Moldova. Matematica 73.2-3 (2013): 37-46.
  https://www.math.md/files/basm/y2013-n2-3/y2013-n2-3-(pp37-46).pdf.pdf
* [Ya1976] Yakovlev, N. N. "On the theory of o-metrizable spaces."
  Doklady Akademii Nauk. Vol. 229. No. 6. Russian Academy of Sciences, 1976.
  https://www.mathnet.ru/links/016f74007f9f96fa3aadae05cbd98457/dan40570.pdf (in Russian)
-/

open TopologicalSpace
open scoped Cardinal

namespace WeaklyFirstCountable

/-- A topological space $X$ is called *weakly first countable* if there exists a function
$N : X → ℕ → Set X, such that:

* For all $x : X, n : ℕ$ we have $x ∈ V x n$
* For all $x : X, n : ℕ$: $V x (n + 1) ⊆ V x n$
* $O ⊆ X$ is open iff $∀ x ∈ O, ∃ n : ℕ, V x n ⊆ O$
-/
class WeaklyFirstCountableTopology (X : Type*) [TopologicalSpace X] : Prop where
  nhds_countable_weak_basis : ∃ V : X → ℕ → Set X, (∀ (x : X), Antitone (V x) ∧ ∀ (n : ℕ), x ∈ V x n)
    ∧ ∀ O : Set X, IsOpen O ↔ ∀ x ∈ O, ∃ k : ℕ, V x k ⊆ O

/-- There are weakly first countable spaces which are not first countable,
for example the [Arens Space](https://topology.pi-base.org/spaces/S000156). -/
@[category undergraduate, AMS 54]
theorem exists_weakly_first_countable_not_first_countable : ∃ (X : Type) (_ : TopologicalSpace X),
      WeaklyFirstCountableTopology X ∧ ¬ FirstCountableTopology X := by sorry

/-- Every first countable space is weakly first countable,
simply take $N x$ as a countable neighborhood basis of $x$. -/
@[category test, AMS 54]
instance FirstCountableTopology.weaklyFirstCountableTopology (X : Type*) [TopologicalSpace X]
    [FirstCountableTopology X] : WeaklyFirstCountableTopology X := by
  have has_basis: ∀ a : X, ∃ x : ℕ → Set X, (𝓝 a).HasAntitoneBasis x := by
    intro a
    rw [← Filter.isCountablyGenerated_iff_exists_antitone_basis]
    exact FirstCountableTopology.nhds_generated_countable a
  let U : X → ℕ → Set X := fun x ↦ (has_basis x).choose
  have hU : ∀ x, (𝓝 x).HasAntitoneBasis (U x) :=
    fun x ↦ Exists.choose_spec (has_basis x)
  use U
  constructor
  · exact fun x ↦ ⟨(hU x).antitone, fun n ↦ mem_of_mem_nhds (HasAntitoneBasis.mem (hU x) n)⟩
  intro O
  rw [isOpen_iff_mem_nhds]
  constructor <;> intro h x hx
  · exact (HasAntitoneBasis.mem_iff (hU x)).mp (h x hx)
  · obtain ⟨n, hn⟩ := h x hx
    exact mem_of_superset (HasAntitoneBasis.mem (hU x) n) hn

/-- Problem 2 in [Ar2013]: Give an example in ZFC of a weakly first-
countable compact space X such that $𝔠 < |X|$. -/
@[category research open, AMS 54]
theorem existsWeaklyFirstCountableCompactBig : answer(sorry) ↔
    ∃ (X : Type) (_ : TopologicalSpace X),
      WeaklyFirstCountableTopology X ∧ CompactSpace X ∧ 𝔠 < #X := by sorry

/-- Problem 3 in [Ar2013]: Give an example in ZFC of a weakly first-
countable compact space which is not first countable. -/
def ExistsWeaklyFirstCountableCompactNotFirstCountable : Prop :=
    ∃ (X : Type) (_ : TopologicalSpace X), WeaklyFirstCountableTopology X ∧ CompactSpace X ∧
      ¬ FirstCountableTopology X

/-- Problem 4 in [Ar2013]: Give an example in ZFC of a weakly first-
countable compact space X which is not first countable. -/
@[category test, AMS 54]
theorem existsWeaklyFirstCountableCompactNotFirstCountable :
    ExistsWeaklyFirstCountableCompactNotFirstCountable := by sorry

/-- Under CH, such a space exists as constructed in [Ya1976] by Yakovlev. -/
@[category research solved, AMS 54]
theorem CH.existsWeaklyFirstCountableCompactNotFirstCountable [Fact (ℵ₁ = 𝔠)] :
    ExistsWeaklyFirstCountableCompactNotFirstCountable := by sorry

-- TODO: add Problem 4 in [Ar2013]

end WeaklyFirstCountable
