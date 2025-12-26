/-
Copyright 2025 The Formal Conjectures Authors.

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
import FormalConjectures.ForMathlib.NumberTheory.BirchSwinnertonDyer

/-!
# Birch and Swinnerton-Dyer conjecture

The Birch and Swinnerton-Dyer conjecture (BSD conjecture) relates the algebraic rank of an
elliptic curve over ℚ to the analytic rank (the order of vanishing of its L-function at s = 1).

Specifically, the weak BSD conjecture states that the algebraic rank equals the analytic rank.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Birch_and_Swinnerton-Dyer_conjecture)
-/

namespace BirchSwinnertonDyer

open scoped WeierstrassCurve.Affine
open Module (finrank)

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/--
The algebraic rank of an elliptic curve E over ℚ is the rank of the finitely generated
abelian group E(ℚ) of rational points.

By the Mordell-Weil theorem, E(ℚ) is a finitely generated abelian group, so its rank
is well-defined as the rank of its free part.
-/
noncomputable def algebraicRank (E : WeierstrassCurve ℚ) : ℕ := sorry
/--
The weak Birch and Swinnerton-Dyer conjecture states that for an elliptic curve E over ℚ,
the algebraic rank equals the analytic rank.

That is, the rank of the group of rational points E(ℚ) equals the order of vanishing
of the L-function L(E, s) at s = 1.
-/
@[category research open, AMS 11 14]
theorem weak_Birch_Swinnerton_Dyer_conjecture :
    algebraicRank E = EllipticCurve.analyticRank E := by
  sorry

end BirchSwinnertonDyer

