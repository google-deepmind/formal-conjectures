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
# Strong IIA in separable matching markets

Galichon and Salanié conjecture that no separable transferable-utility model satisfies strong
independence of irrelevant alternatives: both families of double odds, including singlehood,
cannot be invariant under every change in populations while surplus and joint taste laws stay fixed.

We state the finite-type version with at least two observed types on each side. The admissible
class has atomless pairwise taste differences and a unique positive equilibrium table for every
strictly positive demographic vector. The source does not specify a complete regularity class;
these explicit conditions select a well-defined version of its conjecture. Independence among
a taste vector's coordinates is not assumed.

## References

* A. Galichon and B. Salanié, [*Labeling Dependence in Separable Matching Markets*]
  (https://bsalanie.github.io/files/MatchingIIL_9dec2019.pdf), 9 December 2019,
  Assumption 1 (p. 4), Property 2 (p. 7), and the conjecture in §3 (p. 9).
-/

@[expose] public section

open TransferableUtilityMatching

namespace GalichonSalanieStrongIIA

/-- Every admissible finite separable TU model with at least two types on each side violates
strong IIA. The surplus and taste laws remain fixed while the demographics vary. -/
@[category research open, AMS 60 91]
theorem no_strongIIA {X Y : Type*} [Fintype X] [Fintype Y]
    (hX : 2 ≤ Fintype.card X) (hY : 2 ≤ Fintype.card Y)
    (M : SeparableModel X Y) (hM : M.IsAdmissible) : ¬ M.StrongIIA := by
  sorry

end GalichonSalanieStrongIIA
