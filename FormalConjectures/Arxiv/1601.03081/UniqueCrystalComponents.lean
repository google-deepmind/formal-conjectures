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

/-!
# Unique Crystal Components

*Reference:* [arxiv/1601.03081](https://arxiv.org/abs/1601.03081)
**The Biharmonic mean**
by *Marco Abrate, Stefano Barbero, Umberto Cerruti, Nadir Murru*
-/

namespace Arxiv.«1601.03081»

/--
An odd number $n$ is called a crystal if $n = ab$, with $a, b > 1$
and $B(a, b) ∈ ℕ$, where $B(a, b) := ((a + b)^2 + (a b + 1)^2) / (2 (a + 1) (b + 1))$.
-/
def IsCrystalWithComponents (n a b : ℕ) : Prop :=
  Odd n ∧ 1 < a ∧ 1 < b ∧ n = a * b ∧ 2 * (a + 1) * (b + 1) ∣ (a + b)^2 + (a * b + 1)^2

@[category test, AMS 11]
theorem isCrystalWithComponents_35_5_7 : IsCrystalWithComponents 35 5 7 := by
  norm_num [IsCrystalWithComponents]
  decide

-- TODO(firsching): show divisibility properties from section 3.

/--
If $n = ab$ is a crystal, then there are no other pairs of
positive integers $c, d > 1$, different from the couple $a, b$, such that $n = cd$ and
$B(c, d) ∈ ℕ$, i.e., the components of the crystals are unique.
-/
@[category research open, AMS 11 26]
theorem crystals_components_unique (n a b c d : ℕ)
    (hab : IsCrystalWithComponents n a b) (hcd : IsCrystalWithComponents n c d) :
    ({a, b} : Finset ℕ) = {c, d} := by
  sorry

end Arxiv.«1601.03081»
