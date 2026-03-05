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
# Erdős Problem 998

Is it true that if, for an irrational $\alpha$, the number of $m \leq n$ with
$\{\alpha m\} \in [u,v)$ is $n(v-u) + O(1)$, then $u$ and $v$ must be fractional
parts of integer multiples of $\alpha$? Proved by Kesten.

*Reference:* [erdosproblems.com/998](https://www.erdosproblems.com/998)

[Ke66] Kesten, H., _On a conjecture of Erdős and Szüsz related to uniform distribution mod 1_.
Acta Arithmetica (1966), 193-212.
-/

open Classical Finset

namespace Erdos998

/--
The number of integers $m$ with $1 \leq m \leq n$ such that the fractional part of $\alpha \cdot m$
lies in $[u, v)$.
-/
noncomputable def countFracInInterval (α : ℝ) (u v : ℝ) (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun m : ℕ =>
    u ≤ Int.fract (α * ↑m) ∧ Int.fract (α * ↑m) < v)).card

/--
Let $\alpha$ be an irrational number. Is it true that if, for all large $n$,
$$\#\{1 \leq m \leq n : \{\alpha m\} \in [u,v)\} = n(v-u) + O(1)$$
then $u = \{\alpha k\}$ and $v = \{\alpha \ell\}$ for some integers $k$ and $\ell$?

Here $\{x\}$ denotes the fractional part of $x$. This is a problem of Erdős and
Szüsz. The converse was proved by Hecke and Ostrowski. The conjecture itself
was proved by Kesten [Ke66].
-/
@[category research solved, AMS 11]
theorem erdos_998 : answer(True) ↔
    ∀ (α : ℝ), Irrational α →
    ∀ (u v : ℝ), 0 ≤ u → u < v → v ≤ 1 →
    (∃ C : ℝ, ∀ n : ℕ, 0 < n →
      |(↑(countFracInInterval α u v n) : ℝ) - ↑n * (v - u)| ≤ C) →
    (∃ k : ℤ, u = Int.fract (α * ↑k)) ∧ (∃ ℓ : ℤ, v = Int.fract (α * ↑ℓ)) := by
  sorry

end Erdos998
