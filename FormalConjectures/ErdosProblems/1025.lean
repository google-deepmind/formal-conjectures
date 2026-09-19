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

import FormalConjecturesUtil

/-!
# Erdős Problem 1025

*References:*
- [erdosproblems.com/1025](https://www.erdosproblems.com/1025)
- [Sp72] Spencer, J., *Turán's theorem for k-graphs*. Discrete Mathematics 2 (1972), 183–186.
- [CFS16] Conlon, D., Fox, J., and Sudakov, B., *Short proofs of some extremal results II*.
  Journal of Combinatorial Theory, Series B 121 (2016), 173–196.
-/

namespace Erdos1025

/-- An unordered pair of distinct vertices in an $n$-element set. -/
def Pair (n : ℕ) : Type := {p : Finset (Fin n) // p.card = 2}

/-- Each pair is mapped to a vertex outside that pair. -/
def IsAdmissible {n : ℕ} (f : Pair n → Fin n) : Prop :=
  ∀ p, f p ∉ p.val

/-- The image of every pair contained in $S$ lies outside $S$. -/
def IsFree {n : ℕ} (f : Pair n → Fin n) (S : Finset (Fin n)) : Prop :=
  ∀ p, p.val ⊆ S → f p ∉ S

/--
Erdős and Hajnal asked for the growth of the largest independent-set size guaranteed for
all maps from pairs to vertices that avoid the input pair. Spencer [Sp72] established the
lower bound $g(n) \gg \sqrt{n}$: every such map has a free set of size at least $c\sqrt{n}$,
with a uniform positive constant for all sufficiently large $n$.

Pairs are two-element subsets, as in the set-mapping formulation of [CFS16]. The threshold
is at least $3$ because an admissible map does not exist on a two-element ground set.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/iiis-lean/Erdos1025/blob/30a98247750d691ba76dda074b80b7465a229036/Erdos1025/Main/SpencerIndependence/SquareRootLowerBound/Theorems/lower_bound.lean#L26-L37"]
theorem erdos_1025.lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 3 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ f : Pair n → Fin n,
        IsAdmissible f → ∃ S : Finset (Fin n),
          IsFree f S ∧ c * Real.sqrt (n : ℝ) ≤ (S.card : ℝ) := by
  sorry

/--
Conlon, Fox, and Sudakov [CFS16] established the matching upper bound $g(n) \ll \sqrt{n}$:
for every sufficiently large $n$ there is an admissible map for which every free set has
size at most $C\sqrt{n}$, with a uniform constant $C>0$.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/iiis-lean/Erdos1025/blob/30a98247750d691ba76dda074b80b7465a229036/Erdos1025/Main/GridWitness/ArbitraryNUpperBound/Theorems/upper_bound.lean#L33-L71"]
theorem erdos_1025.upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∃ f : Pair n → Fin n,
        IsAdmissible f ∧ ∀ S : Finset (Fin n), IsFree f S →
          (S.card : ℝ) ≤ C * Real.sqrt (n : ℝ) := by
  sorry

/-- An empty set is free for every map. -/
@[category test, AMS 5]
theorem empty_isFree {n : ℕ} (f : Pair n → Fin n) : IsFree f ∅ := by
  intro p hp
  have h := Finset.subset_empty.mp hp
  have : (0 : ℕ) = 2 := by simpa [h] using p.property
  omega

end Erdos1025
