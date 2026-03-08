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
# Erdős Problem 204

*References:*
- [erdosproblems.com/204](https://www.erdosproblems.com/204)
- [Ad25] S. Adenwalla, A Question of Erdős and Graham on Covering Systems. arXiv:2501.15170 (2025).
-/

namespace Erdos204

/--
Are there $n$ such that there is a covering system with moduli the divisors of $n$ which is 'as
disjoint as possible'?

That is, for all $d\mid n$ with $d>1$ there is an associated $a_d$ such that every integer is
congruent to some $a_d\pmod{d}$, and if there is some integer $x$ with
\[x\equiv a_d\pmod{d}\textrm{ and }x\equiv a_{d'}\pmod{d'}\]then $(d,d')=1$.

The density of such $n$ is zero. Erdős and Graham believed that no such $n$ exist.

Adenwalla [Ad25] has proved there are no such $n$.
-/
@[category research solved, AMS 5]
theorem erdos_204 : answer(False) ↔ ∃ (n : ℕ) (a : ℕ → ℤ),
    let D := {d : ℕ | d ∣ n ∧ d > 1}
    (∀ x : ℤ, ∃ d ∈ D, x ≡ a d [ZMOD d]) ∧
    (∀ d ∈ D, ∀ d' ∈ D, d ≠ d' → (∃ x : ℤ, x ≡ a d [ZMOD d] → x ≡ a d' [ZMOD d']) →
      Nat.gcd d d' = 1) := by
  sorry

end Erdos204
