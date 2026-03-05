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
# Erdős Problem 518

*Reference:* [erdosproblems.com/518](https://www.erdosproblems.com/518)

A problem of Erdős and Gyárfás [ErGy95]. Gerencsér and Gyárfás [GeGy67]
proved that, if the paths do not need to be of the same colour, then two
paths suffice. Erdős and Gyárfás proved that $2\sqrt{n}$ paths suffice and
observed that $\sqrt{n}$ would be best possible.

Solved in the affirmative by Pokrovskiy, Versteegen, and Williams [PVW24].
-/

namespace Erdos518

/-- A path is monochromatic of color $b$ under edge coloring $c$ if every
    consecutive pair of vertices in the path receives color $b$. A path
    of length $\leq 1$ is trivially monochromatic. -/
def IsMonochromaticPath {α : Type*} (c : α → α → Bool) (b : Bool) (p : List α) : Prop :=
  p.IsChain (fun u v => c u v = b)

/--
Erdős Problem 518 [ErGy95]:

Is it true that, in any two-colouring of the edges of $K_n$, there exist
at most $\lceil\sqrt{n}\rceil$ monochromatic paths, all of the same colour,
which together cover all vertices?

The bound is formalized as `Nat.sqrt n + 1`, which satisfies
$\lceil\sqrt{n}\rceil \leq \text{Nat.sqrt}\; n + 1$ for all $n$.

Solved in the affirmative by Pokrovskiy, Versteegen, and Williams [PVW24].
-/
@[category research solved, AMS 5]
theorem erdos_518 : answer(True) ↔
    ∀ (n : ℕ) (c : Fin n → Fin n → Bool),
      (∀ i j : Fin n, c i j = c j i) →
      ∃ (b : Bool) (paths : List (List (Fin n))),
        paths.length ≤ Nat.sqrt n + 1 ∧
        (∀ p ∈ paths, p.Nodup ∧ IsMonochromaticPath c b p) ∧
        (∀ v : Fin n, ∃ p ∈ paths, v ∈ p) := by sorry

end Erdos518
