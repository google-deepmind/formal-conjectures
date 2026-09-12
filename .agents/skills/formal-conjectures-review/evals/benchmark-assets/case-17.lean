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
# Jacobson Conjecture

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Jacobson's_conjecture)
- [He1965]: Herstein, I. N. (1965), "A counterexample in Noetherian rings",
  Proceedings of the National Academy of Sciences of the United States of America, 54 (4): 1036–1037
  https://pmc.ncbi.nlm.nih.gov/articles/PMC219788/
- [Ja1956]: Jacobson, Nathan. Structure of rings. Vol. 37. American Mathematical Soc., 1956.
- [Le1977]: Lenagan, T. H. (1977), "Noetherian rings with Krull dimension one",
  J. London Math. Soc. Series 2, 15 (1): 41–47
  https://londmathsoc.onlinelibrary.wiley.com/doi/abs/10.1112/jlms/s2-15.1.41
-/

open Ring

universe u

namespace Jacobson

/-- The Jacobson conjecture for a ring $R$: the infimum of the powers of the Jacobson radical
$J$ is the zero ideal. -/
def JacobsonConjectureFor (R : Type u) [Ring R] : Prop :=
  ⨅ n : ℕ, jacobson R ^ n = 0

/-- The Jacobson conjecture (in its modern form):
In a (noncommutative) ring which is left and right Noetherian,
the intersection of the powers of the Jacobson ideal is trivial -/
@[category research open, AMS 16]
theorem jacobson_conjecture :
    answer(sorry) ↔ ∀ (R : Type) [Ring R] [IsNoetherianRing R] [IsRightNoetherianRing R],
      JacobsonConjectureFor R := by
  sorry

/-- For commutative rings this is the case as a consequence of Krull's intersection theorem. -/
@[category textbook, AMS 13 16]
theorem jacobson_conjecture_of_comm_ring (R : Type u) [CommRing R] [IsNoetherianRing R] :
    JacobsonConjectureFor R := by
  sorry

/-- Originally, on page 200 of [Ja1956], Jacobson asked if the Jacobson conjecture holds for all right
Noetherian rings. However in [He1965] Herstein constructs a right Noetherian ring for which the
Jacobson conjecture does not hold. -/
@[category research solved, AMS 16]
theorem jacobson_conjecture_of_right_noetherian :
    answer(False) ↔ ∀ (R : Type) [Ring R] [IsRightNoetherianRing R], JacobsonConjectureFor R := by
  sorry

/- In [Le1977] Lenagan shows the Jacobson conjecture holds for left and right Noetherian rings
with Krull dimension $1$. -/
-- TODO: Add this result. Note that we do not have Krull dimension for noncommutative rings yet.

end Jacobson
