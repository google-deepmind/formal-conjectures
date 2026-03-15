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
import FormalConjecturesForMathlib.Data.Set.Density

/-!
# Erdős Problem 432

*Reference:* [erdosproblems.com/432](https://www.erdosproblems.com/432)

Asked by Straus, inspired by a problem of Ostmann (see Problem #431).

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980), p.85.
-/

open Filter

namespace Erdos432

/--
Erdős Problem 432 [ErGr80, p.85]:

Let $A, B \subseteq \mathbb{N}$ be two infinite sets. If all elements of the sumset
$A + B = \{a + b \mid a \in A, b \in B\}$ are pairwise coprime, then $A + B$ has
zero upper density.
-/
@[category research open, AMS 5 11]
theorem erdos_432
    (A B : Set ℕ) (hA : A.Infinite) (hB : B.Infinite)
    (h_coprime : (Set.image2 (· + ·) A B).Pairwise Nat.Coprime) :
    (Set.image2 (· + ·) A B).upperDensity = 0 := by
  sorry

end Erdos432
