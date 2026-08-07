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

open Nat

/--
A286885: Number of ways to write $6n+1$ as $x^2 + 3y^2 + 54z^2$ with $x,y,z$ nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  let N : ℕ := 6 * n + 1
  -- Maximum possible values for x, y, and z, giving tight bounds for the search space.
  -- x_max = floor(sqrt(N))
  let X_max : ℕ := N.sqrt
  -- y_max = floor(sqrt(N/3))
  let Y_max : ℕ := (N / 3).sqrt
  -- z_max = floor(sqrt(N/54))
  let Z_max : ℕ := (N / 54).sqrt

  -- The search sets for each variable.
  let X_set : Finset ℕ := Finset.range (X_max + 1)
  let Y_set : Finset ℕ := Finset.range (Y_max + 1)
  let Z_set : Finset ℕ := Finset.range (Z_max + 1)

  -- The Finset of all candidate triples $(x, y, z)$, structured as $ℕ \times (ℕ \times ℕ)$.
  let Candidates : Finset (ℕ × ℕ × ℕ) := Finset.product X_set (Finset.product Y_set Z_set)

  -- The result is the cardinality of the filtered set that satisfies the Diophantine equation.
  Finset.card <| Candidates.filter
    (fun p : ℕ × (ℕ × ℕ) =>
      let x := p.fst
      let y := p.snd.fst
      let z := p.snd.snd
      x^2 + 3 * y^2 + 54 * z^2 = N)

/--
Conjecture: a(n) > 0 for all n = 0,1,2,....
-/
theorem oeis_286885_conjecture_0 : ∀ n : ℕ, a n > 0 := by
  sorry
