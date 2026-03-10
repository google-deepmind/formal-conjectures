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
# Erdős Problem 342

*References:*
- [erdosproblems.com/342](https://www.erdosproblems.com/342)
- [Ben Green's Open Problem 7](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.7)
- [OEIS A002858](https://oeis.org/A002858)
-/

open Nat Set Filter
open scoped Topology

namespace Erdos342

/-- `UniqueUlamSum a n m` means that $m$ has a unique representation as $a(i) + a(j)$
with $i < j < n$. -/
def UniqueUlamSum (a : ℕ → ℕ) (n m : ℕ) : Prop :=
  ∃! p : ℕ × ℕ, p.1 < p.2 ∧ p.2 < n ∧ m = a p.1 + a p.2

/-- `IsUlamSequence a` means that $a$ is the Ulam sequence (OEIS A002858):
$a(0) = 1$, $a(1) = 2$, and for each $n \geq 2$, $a(n)$ is the least integer
greater than $a(n-1)$ that has a unique representation as $a(i) + a(j)$
with $i < j < n$. -/
def IsUlamSequence (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ a 1 = 2 ∧
  ∀ n, 2 ≤ n →
    a (n - 1) < a n ∧
    UniqueUlamSum a n (a n) ∧
    ∀ m, a (n - 1) < m → m < a n → ¬ UniqueUlamSum a n m

/--
Do infinitely many pairs $(a, a+2)$ occur in Ulam's sequence? -/
@[category research open, AMS 05 11 40]
theorem erdos_342.parts.i :
    answer(sorry) ↔
      ∀ a : ℕ → ℕ, IsUlamSequence a →
        ∀ N : ℕ, ∃ n ≥ N, (a (n + 1)) = (a n) + 2 := by
  sorry

/--
Does Ulam's sequence eventually have periodic differences? That is, is $a(n+1) - a(n)$ eventually periodic?
-/
@[category research open, AMS 05 11 40]
theorem erdos_342.parts.ii :
    answer(sorry) ↔
      ∀ a : ℕ → ℕ, IsUlamSequence a →
        let d (n : ℕ) : ℤ := a (n + 1) - a n
        ∃ p > 0, ∀ᶠ m in atTop, d (m + p) = d m := by
  sorry

/--
Part (iii), is the density of the sequence 0?
-/
@[category research open, AMS 05 11 40]
theorem erdos_342.parts.iii :
    answer(sorry) ↔
      ∀ a : ℕ → ℕ, IsUlamSequence a →
        Tendsto
          (fun N : ℕ =>
            (Finset.card (Finset.filter (fun n ↦ a n ≤ N) (Finset.range N)) : ℝ) / N)
          atTop (𝓝 0) := by
  sorry

end Erdos342
