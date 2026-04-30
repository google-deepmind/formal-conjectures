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
# Ben Green's Open Problem 43

*Reference:* [Ben Green's Open Problem 43](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.43)
-/

open Filter

namespace Green43

/--
Let $N$ be a large integer. For each prime $p$ with $N^{0.51} \leq p < 2N^{0.51}$, pick some
residue $a(p) \in \mathbb{Z}/p\mathbb{Z}$. Is it true that
$$\#\{n \in [N] : n \equiv a(p) \pmod{p} \text{ for some } p\} \gg N^{1-o(1)}?$$
-/
@[category research open, AMS 11]
theorem green_43 : answer(sorry) ↔
    ∃ o : ℕ → ℝ, Tendsto o atTop (𝓝 0) ∧ (∀ n ∈ ℕ, 0 ≤ o n) ∧ ∀ᶠ N : ℕ in atTop, ∀ (a : ℕ → ℤ), (N : ℝ) ^ (1 - o N) ≤
    ((Finset.Icc 1 N).filter fun n => ∃ p, Nat.Prime p ∧ (N : ℝ) ^ (0.51 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < 2 * (N : ℝ) ^ (0.51 : ℝ) ∧
    (p : ℤ) ∣ ((n : ℤ) - a p)).card := by
  sorry

end Green43
