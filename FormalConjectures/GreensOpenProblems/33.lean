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
# Ben Green's Open Problem 33

*References:*
- [Gr24] [Ben Green's Open Problem 33](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.33)
- [CaHa20] Caprace, Pierre-Emmanuel, and Pierre de la Harpe. "Groups with irreducibly unfaithful
  subsets for unitary representations." Confluentes Mathematici 12.1 (2020): 31-68.
- [CrLe07] Croot, Ernie, and Vsevolod F. Lev. "Open problems in additive combinatorics."
  Additive combinatorics 43.207-233 (2007): 1.
-/

open Filter
open scoped Pointwise

namespace Green33

/--
Are there infinitely many $q$ for which there is a set $A \subset \mathbb{Z}/q\mathbb{Z}$,
$|A| = (\sqrt{2} + o(1))q^{1/2}$, with $A + A = \mathbb{Z}/q\mathbb{Z}$? [Gr24]
-/
@[category research open, AMS 5 11]
theorem green_33 :
    answer(sorry) ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ᶠ q : ℕ+ in atTop,
          ∃ A : Finset (ZMod q),
            A + A = Finset.univ ∧
            |((A.card : ℝ) / Real.sqrt q - Real.sqrt 2)| < ε := by
  sorry

-- TODO(jgd): Add variants from comments in [Gr24]

end Green33
