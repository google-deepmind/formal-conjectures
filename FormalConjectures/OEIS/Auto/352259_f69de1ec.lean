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
open Nat Finset

/--
A352259: Number of ways to write $n$ as $w^6 + x^2 + 2y^2 + 3z^2 + x y z$,
where $w, x, y, z$ are nonnegative integers.
-/
def A352259 (n : ℕ) : ℕ :=
  -- Define an upper bound for the search space. Bounding by n + 1 is sufficient since
  -- for any solution, w, x, y, z <= n.
  let B := n + 1
  let variables_range : Finset ℕ := range B

  -- The search space is the Cartesian product of four copies of variables_range.
  -- The resulting type is (((ℕ × ℕ) × ℕ) × ℕ).
  let search_space : Finset (((ℕ × ℕ) × ℕ) × ℕ) :=
    ((variables_range.product variables_range).product variables_range).product variables_range

  -- Count the number of elements in the search space that satisfy the equation.
  (Finset.filter (fun p =>
    -- Destructure the nested pair (((w, x), y), z)
    let w := p.fst.fst.fst
    let x := p.fst.fst.snd
    let y := p.fst.snd
    let z := p.snd
    n = w^6 + x^2 + 2 * y^2 + 3 * z^2 + x * y * z
  ) search_space).card

/--
Conjecture 2: Every n = 0,1,2,... can be written as 2*w^4 + 3*x^2 + y^2 + z^2 + x*y*z,
where w,x,y,z are nonnegative integers.
We have verified Conjectures 1 and 2 for all n <= 10^5.
-/
theorem oeis_352259_conjecture_2 (n : ℕ) :
  ∃ (w x y z : ℕ), n = 2 * w^4 + 3 * x^2 + y^2 + z^2 + x * y * z :=
by sorry
