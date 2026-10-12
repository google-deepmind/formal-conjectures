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

public import FormalConjecturesForMathlib.ModelTheory.Encoding
public import Mathlib.Computability.Partrec

/-!
# Recursive and decidable theories

Mathlib's `FirstOrder.Language.Theory` is an arbitrary set of sentences, which need not be
closed under logical consequence. Two computability notions are therefore distinct:

- `T` is *recursive* if membership in `T` is computable: there is an algorithm which, given a
  sentence `φ`, decides whether `φ ∈ T`. This is a property of the set of axioms.
- `T` is *decidable* if the set of consequences `{φ | T ⊨ᵇ φ}` is recursive: there is an
  algorithm which decides whether `φ` holds in every model of `T`. This only depends on the
  consequences of `T`, so it is invariant under replacing `T` by a logically equivalent set of
  axioms (`FirstOrder.Language.Theory.isDecidable_congr`).

The two notions agree when `T` is closed under consequence, in particular for the complete
theory `L.completeTheory M` of a structure `M`
(`FirstOrder.Language.Theory.isDecidable_completeTheory_iff`).

Both notions use the Gödel numbering of sentences from
`FormalConjecturesForMathlib.ModelTheory.Encoding` and the notion of a computable function
`ℕ → Bool` from Mathlib's computability library. As usual, they are relative to the chosen
encoding of the symbols of `L`. For a language with finitely many symbols, all injective
encodings of the symbols give the same notions.

## Main declarations

- `FirstOrder.Language.Theory.IsRecursive`: membership in the set of sentences is computable.
- `FirstOrder.Language.Theory.IsDecidable`: the set of consequences is recursive.
- `FirstOrder.Language.Theory.isDecidable_iff_isRecursive`: for a theory closed under
  consequence, the two notions agree.
-/

@[expose] public section

namespace FirstOrder.Language.Theory

variable {L : Language} [Encodable (Σ n, L.Functions n)] [Encodable (Σ n, L.Relations n)]

/-- A set of sentences `T` is *recursive* if there is a computable function `f : ℕ → Bool` such
that, for every sentence `φ`, `f` returns `true` on the Gödel number of `φ` if and only if
`φ ∈ T`. -/
def IsRecursive (T : L.Theory) : Prop :=
  ∃ f : ℕ → Bool, Computable f ∧ ∀ φ : L.Sentence, f (Encodable.encode φ) = true ↔ φ ∈ T

/-- A theory `T` is *decidable* if the set of its consequences `{φ | T ⊨ᵇ φ}` is recursive:
there is an algorithm which, given a sentence `φ`, decides whether `φ` holds in every model of
`T`. -/
def IsDecidable (T : L.Theory) : Prop :=
  IsRecursive {φ | T ⊨ᵇ φ}

variable {T T' : L.Theory}

/-- The empty set of sentences is recursive. -/
theorem isRecursive_empty : (∅ : L.Theory).IsRecursive :=
  ⟨fun _ => false, Computable.const false, fun _ => by simp⟩

/-- The set of all sentences is recursive. -/
theorem isRecursive_univ : IsRecursive (Set.univ : L.Theory) :=
  ⟨fun _ => true, Computable.const true, fun _ => by simp⟩

/-- The complement of a recursive set of sentences is recursive. -/
theorem IsRecursive.compl (hT : T.IsRecursive) : Tᶜ.IsRecursive := by
  obtain ⟨f, hf, hfT⟩ := hT
  refine ⟨fun n => !f n, ?_, fun φ => ?_⟩
  · exact (hf.cond (Computable.const false) (Computable.const true)).of_eq fun n => by
      cases f n <;> rfl
  · have key : ∀ (b : Bool) (P : Prop), (b = true ↔ P) → ((!b) = true ↔ ¬P) := by
      rintro b P h
      cases b <;> simp_all
    exact key _ _ (hfT φ)

/-- Decidability only depends on the consequences of a theory. In particular, logically
equivalent sets of axioms are decidable together. -/
theorem isDecidable_congr (h : ∀ φ : L.Sentence, T ⊨ᵇ φ ↔ T' ⊨ᵇ φ) :
    T.IsDecidable ↔ T'.IsDecidable := by
  unfold IsDecidable
  rw [show {φ : L.Sentence | T ⊨ᵇ φ} = {φ | T' ⊨ᵇ φ} from Set.ext h]

/-- For a theory closed under consequence, decidability is the same as recursiveness. -/
theorem isDecidable_iff_isRecursive (hT : ∀ φ : L.Sentence, T ⊨ᵇ φ → φ ∈ T) :
    T.IsDecidable ↔ T.IsRecursive := by
  unfold IsDecidable
  rw [show {φ : L.Sentence | T ⊨ᵇ φ} = T from Set.ext fun φ => ⟨hT φ, models_sentence_of_mem⟩]

/-- The complete theory of a structure `M` contains all its consequences, so it is decidable
if and only if membership in it is computable. -/
theorem isDecidable_completeTheory_iff (M : Type*) [L.Structure M] [Nonempty M] :
    (L.completeTheory M).IsDecidable ↔ (L.completeTheory M).IsRecursive :=
  isDecidable_iff_isRecursive fun _ h => mem_completeTheory.2 (h.realize_sentence M)

/-- The inconsistent theory of all sentences is decidable. -/
theorem isDecidable_univ : IsDecidable (Set.univ : L.Theory) :=
  (isDecidable_iff_isRecursive fun φ _ => Set.mem_univ φ).2 isRecursive_univ

end FirstOrder.Language.Theory
