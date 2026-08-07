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

open Nat Finset Int

/--
A301376: Number of ways to write $n^2$ as $x^2 + y^2 + z^2 + w^2$ with $x,y,z,w$ nonnegative integers and $z \le w$ such that $x^2-(3y)^2 = 4^k$ for some $k = 0,1,2,\ldots$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  -- Search space for (x, y, z, w) as nested products ((x, y), (z, w)).
  let domain : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := (R.product R).product (R.product R)

  Finset.card $ domain.filter (λ p : (ℕ × ℕ) × (ℕ × ℕ) =>
    let x := p.fst.fst; let y := p.fst.snd;
    let z := p.snd.fst; let w := p.snd.snd;

    x^2 + y^2 + z^2 + w^2 = n^2 ∧
    z ≤ w ∧
    -- The condition: x^2 - (3*y)^2 = 4^k. Casted to ℤ for subtraction, then compared to 4^k (which is in ℕ and implicitly cast to ℤ).
    -- Bounded existence: 4^k <= n^2 implies k is bounded by log_4(n^2). range (n + 1) is a safe upper bound for k.
    (∃ k ∈ Finset.range (n + 1), (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ))
  )

/--
Conjecture: a(n) > 0 for all n > 0. Moreover, any positive square n² can be written as
x² + y² + z² + w² with x,y,z,w integers and y even such that x² - (3*y)² = 4ᵏ for some k = 0,1,2,....
-/
theorem A301376_conjecture : ∀ (n : ℕ), n > 0 → a n > 0 := by
  sorry
