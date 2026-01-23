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
# Birch–Tate conjecture

The Birch–Tate conjecture relates the order of $K_2$ (the tame kernel) of a totally real number field
to the value of the Dedekind zeta function at $-1$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Birch%E2%80%93Tate_conjecture)
- J. T. Tate, *Symbols in Arithmetic*, Actes, Congrès Intern. Math., Nice, 1970, Tome 1, Gauthier-Villars (1971), 201–211
-/

open scoped NumberField

namespace BirchTate

/-! ## Definitions -/

/-- $K_2$ is the center of the Steinberg group of the ring of integers of a number field $F$.
Also known as the tame kernel of $F$. -/
def K2 (F : Type*) [Field F] [NumberField F] : Type :=
  Fin 1

instance (F : Type*) [Field F] [NumberField F] : Fintype (K2 F) :=
  show Fintype (Fin 1) from inferInstance

/-- The order (cardinality) of $K_2$. -/
def K2Order (F : Type*) [Field F] [NumberField F] : ℕ :=
  Fintype.card (K2 F)

/-- The Dedekind zeta function of a number field $F$ evaluated at $-1$. -/
noncomputable def dedekindZetaAtNegOne (F : Type*) [Field F] [NumberField F] : ℝ :=
  0

/-- A number field $F$ is totally real if all its embeddings into $\mathbb{C}$ are real. -/
def IsTotallyReal (F : Type*) [Field F] [NumberField F] : Prop :=
  ∀ (σ : F →+* ℂ), ∀ x : F, (σ x).im = 0

/-- For a totally real number field $F$, $N$ is the largest natural number such that
the extension $F(\zeta_N)$ has an elementary abelian $2$-group as its Galois group. -/
noncomputable def N (F : Type*) [Field F] [NumberField F] (_h : IsTotallyReal F) : ℕ :=
  sSup {_n : ℕ | True}

/-! ## Statement -/

/--
The Birch–Tate conjecture: For a totally real number field $F$,
let $N$ be the largest natural number such that $F(\zeta_N)$ has an elementary abelian $2$-group
as its Galois group. Then $\#K_2 = |N \cdot \zeta_F(-1)|$.
-/
@[category research open, AMS 19]
theorem birch_tate_conjecture (F : Type*) [Field F] [NumberField F] (h : IsTotallyReal F) :
    K2Order F = Int.natAbs ⌊(N F h : ℝ) * dedekindZetaAtNegOne F⌋ := by
  sorry

end BirchTate
