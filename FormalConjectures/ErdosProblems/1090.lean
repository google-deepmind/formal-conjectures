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
# Erdős Problem 1090

*References:*
- [erdosproblems.com/1090](https://www.erdosproblems.com/1090)
- [Er75f] Erdős, Paul, *On some problems of elementary and combinatorial geometry*. Ann. Mat. Pura Appl. (4) (1975), 99-108.
-/

namespace Erdos1090

/--
Let $k\geq 3$. Does there exist a finite set $A\subset \mathbb{R}^2$ such that, in any $2$-colouring of $A$, there exists a line which contains at least $k$ points from $A$, and all the points of $A$ on the line have the same colour?

Erdős [Er75f] says Graham and Selfridge proved the answer is yes when $k=3$. Hunter has observed that, for sufficiently large $n$, a generic projection of $[k]^n$ into $\mathbb{R}^2$ has this property, by the Hales-Jewett theorem.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1090.lean"]
theorem erdos_1090 : answer(True) ↔ ∀ (k : ℕ), ∀ (hk : 3 ≤ k),
    ∃ (A : Finset (Fin 2 → ℝ)), ∀ (C : A → Fin 2),
      ∃ (S : Finset (Fin 2 → ℝ)), ∃ (hSA : S ⊆ A),
        Collinear ℝ (S : Set (Fin 2 → ℝ)) ∧ S.card ≥ k ∧
          (∀ y ∈ A, y ∈ affineSpan ℝ (S : Set (Fin 2 → ℝ)) → y ∈ S) ∧
          ∃ c, ∀ x (hx : x ∈ S), C ⟨x, hSA hx⟩ = c := by
  sorry

end Erdos1090
