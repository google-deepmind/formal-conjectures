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
# Erdős Problem 1035

*Reference:* [erdosproblems.com/1035](https://www.erdosproblems.com/1035)

Is there a constant `c > 0` such that every graph on `2^n` vertices with
minimum degree greater than `(1 - c) 2^n` contains the `n`-dimensional
hypercube `Q_n`?
-/

noncomputable section

namespace Erdos1035

open Classical Filter

/-- A simple graph on the finite vertex type `Fin n`. -/
structure SimpleGraphOn (n : ℕ) where
  Adj : Fin n → Fin n → Prop
  symm : ∀ {u v : Fin n}, Adj u v → Adj v u
  loopless : ∀ v : Fin n, ¬ Adj v v

/-- The degree of a vertex in a finite simple graph. -/
def degree {n : ℕ} (G : SimpleGraphOn n) (v : Fin n) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin n)).filter fun w => G.Adj v w).card

/-- Two Boolean vectors are adjacent in the `n`-dimensional hypercube. -/
def HypercubeAdjacent {n : ℕ} (x y : Fin n → Bool) : Prop :=
  ∃ i : Fin n, x i ≠ y i ∧ ∀ j : Fin n, j ≠ i → x j = y j

/-- `G` contains a copy of the `n`-dimensional hypercube. -/
def ContainsHypercube (n : ℕ) (G : SimpleGraphOn (2 ^ n)) : Prop :=
  ∃ emb : (Fin n → Bool) → Fin (2 ^ n),
    Function.Injective emb ∧
      ∀ x y : Fin n → Bool,
        HypercubeAdjacent x y →
          G.Adj (emb x) (emb y)

/-- Every vertex has degree greater than `(1 - c) * 2^n`. -/
def MinimumDegreeGreaterThanOneMinusC (n : ℕ) (c : ℝ)
    (G : SimpleGraphOn (2 ^ n)) : Prop :=
  ∀ v : Fin (2 ^ n), (1 - c) * (2 ^ n : ℝ) < (degree G v : ℝ)

/-- The conjecture that sufficiently dense graphs on `2^n` vertices contain `Q_n`. -/
def Erdos1035Conjecture : Prop :=
  ∃ c : ℝ,
    0 < c ∧
      ∀ᶠ n in atTop,
        ∀ G : SimpleGraphOn (2 ^ n),
          MinimumDegreeGreaterThanOneMinusC n c G →
            ContainsHypercube n G

/--
Is there `c > 0` such that every graph on `2^n` vertices with minimum degree
greater than `(1 - c) 2^n` contains `Q_n`?
-/
@[category research open, AMS 5]
theorem erdos_1035 : answer(sorry) ↔ Erdos1035Conjecture := by
  sorry

end Erdos1035

end

