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
# Erdős Problem 774

Is every proportionately dissociated set of natural numbers the union of finitely many
dissociated sets?

Pisier [Pi83] showed that proportionately dissociated sets are equivalent to Sidon sets in the
harmonic analysis sense. The analogous question for Sidon sets (in the additive combinatorics
sense) was answered negatively by Nešetřil, Rödl, and Sales [NRS24].

See also **Problem 328** (the Sidon set analogue).

*Reference:* [erdosproblems.com/774](https://www.erdosproblems.com/774)

[AlEr85] Alon, N. and Erdős, P., _An application of graph theory to additive number theory_.
European J. Combin. **6** (1985), 201–203.

[Er92b] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Matematiche (Catania) **47** (1992), 231–240.

[Pi83] Pisier, G., _Arithmetic characterizations of Sidon sets_.
Bull. Amer. Math. Soc. (N.S.) **8** (1983), 87–89.

[NRS24] Nešetřil, J., Rödl, V., and Sales, M., _On Pisier type theorems_.
Combinatorica **44** (2024), 1211–1232.
-/

open Finset

namespace Erdos774

/-- A set $A \subseteq \mathbb{N}$ is *dissociated* if all finite subset sums are distinct:
for any two distinct finite subsets $X \neq Y$ of $A$, $\sum X \neq \sum Y$. -/
def Dissociated (A : Set ℕ) : Prop :=
  ∀ X Y : Finset ℕ, ↑X ⊆ A → ↑Y ⊆ A → X ≠ Y → X.sum id ≠ Y.sum id

/-- A set $A \subseteq \mathbb{N}$ is *proportionately dissociated* if there exists $c > 0$ such
that every finite subset $B \subseteq A$ contains a dissociated subset of size
$\geq c \cdot |B|$. -/
def ProportionatelyDissociated (A : Set ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ B : Finset ℕ, ↑B ⊆ A →
    ∃ D : Finset ℕ, D ⊆ B ∧ Dissociated ↑D ∧ (D.card : ℝ) ≥ c * B.card

/--
**Erdős Problem 774** (Alon–Erdős conjecture [AlEr85]):
Is every proportionately dissociated set the union of finitely many
dissociated sets?
-/
@[category research open, AMS 5 11]
theorem erdos_774 : answer(sorry) ↔
    ∀ A : Set ℕ, A.Infinite →
    ProportionatelyDissociated A →
    ∃ n : ℕ, ∃ D : Fin n → Set ℕ,
      (∀ i, Dissociated (D i)) ∧ A ⊆ ⋃ i, D i := by
  sorry

end Erdos774
