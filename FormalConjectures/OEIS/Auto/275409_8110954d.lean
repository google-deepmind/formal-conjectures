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
A275409: Number of ordered ways to write $n$ as $2w^2 + x^2 + y^2 + z^2$ with $w + x + 2y + 4z$ a square, where $w,x,y,z$ are nonnegative integers.
$$a(n) = \# \left\{(w, x, y, z) \in \mathbb{N}^4 \mid 2w^2 + x^2 + y^2 + z^2 = n, \quad w + x + 2y + 4z \text{ is a square} \right\}$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Define perfect square check using computable `Nat.sqrt`.
  let is_sq (k : ℕ) : Prop := k.sqrt * k.sqrt = k

  -- A safe upper bound for $w, x, y, z$ is $\lfloor\sqrt{n}\rfloor + 1$.
  let M : ℕ := n.sqrt + 1
  let R : Finset ℕ := range M

  -- The search space of ordered quadruples, structured as $w \times (x \times (y \times z))$.
  -- This allows for robust iteration over $w, x, y, z$.
  let search_space : Finset (ℕ × (ℕ × (ℕ × ℕ))) := R.product (R.product (R.product R))

  search_space.sum fun p : ℕ × (ℕ × (ℕ × ℕ)) =>
    let w := p.fst
    let x := p.snd.fst
    let y := p.snd.snd.fst
    let z := p.snd.snd.snd

    let sum_sq := 2 * w^2 + x^2 + y^2 + z^2
    let lin_comb := w + x + 2 * y + 4 * z

    -- The bounds chosen ensures that we will find all solutions (w,x,y,z) where w^2, x^2, y^2, z^2 <= n.
    -- If $2w^2 + x^2 + y^2 + z^2 = n$, then $w, x, y, z \le \sqrt{n}$, so this upper bound is sufficient.
    if sum_sq = n ∧ is_sq lin_comb
    then 1
    else 0

-- Proof snippets provided in the prompt are removed as requested, only
-- the definition needs to be present and the conjecture must be stated.
-- The definition has been corrected to rely on a mathematically sound search space bound
-- based on the fact that $w, x, y, z \le \sqrt{n}$.

/-- The set of natural numbers $n$ for which $a(n) = 0$ is conjectured to be $\{3, 10\}$. -/
def A275409_zero_set : Finset ℕ :=
  {3, 10}

/-- The set of natural numbers $n$ for which $a(n) = 1$ is conjectured to be a specific finite set. -/
def A275409_one_set : Finset ℕ :=
  {0, 2, 7, 8, 9, 12, 14, 15, 22, 23, 24, 25, 36, 39, 44, 45, 60, 87, 98, 106, 110, 111, 183}

/--
Conjecture (i) from A275409:
a(n) > 0 except for n = 3, 10, and a(n) = 1 only for
n = 0, 2, 7, 8, 9, 12, 14, 15, 22, 23, 24, 25, 36, 39, 44, 45, 60, 87, 98, 106, 110, 111, 183.
-/
theorem oeis_275409_conjecture_0 :
  (∀ n : ℕ, (a n > 0 ↔ n ∉ A275409_zero_set)) ∧
  (∀ n : ℕ, (a n = 1 ↔ n ∈ A275409_one_set)) :=
by sorry
