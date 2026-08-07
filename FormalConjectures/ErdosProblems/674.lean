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
# Erdős Problem 674

*References:*
- [erdosproblems.com/674](https://www.erdosproblems.com/674)
- [Ko40] Ko, Chao, *Note on the Diophantine equation $x^xy^y=z^z$*. J. Chinese Math. Soc.
  (1940), 31-39.
-/

namespace Erdos674

/-- The set of integer solutions to $x^x y^y = z^z$ with $x, y, z > 1$. -/
def solutionSet : Set (ℕ × ℕ × ℕ) :=
  {(x, y, z) | 1 < x ∧ 1 < y ∧ 1 < z ∧ x ^ x * y ^ y = z ^ z}

/--
Are there any integer solutions to $x^xy^y=z^z$ with $x,y,z>1$?

Ko [Ko40] proved there are none if $(x,y)=1$, but there are in fact infinitely many solutions in
general - for example, $x=2^{12}3^6$, $y = 2^83^8$, and $z = 2^{11}3^7$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos674.lean"]
theorem erdos_674 : answer(True) ↔ solutionSet.Nonempty := by
  sorry

/--
There are in fact infinitely many integer solutions to $x^xy^y=z^z$ with $x,y,z>1$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos674.lean"]
theorem erdos_674.variants.infinite : solutionSet.Infinite := by
  sorry

end Erdos674
