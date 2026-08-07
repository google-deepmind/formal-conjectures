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
# Erdős Problem 405

*References:*
- [erdosproblems.com/405](https://www.erdosproblems.com/405)
- [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number
theory. Monographies de L'Enseignement Mathematique (1980)
- [BrEr91] Brindza, B. and Erdős, P., On some {D}iophantine problems involving powers and
factorials. J. Austral. Math. Soc. Ser. A (1991), 1--7.
- [YuLi96] Yu, Kunrui and Liu, Dehua, A complete resolution of a problem of {E}rdős and {G}raham.
Rocky Mountain J. Math. (1996), 1235--1244.
-/

open scoped Nat

namespace Erdos405

/--
Let $p$ be an odd prime. Is it true that the equation $(p-1)!+a^{p-1}=p^k$ has only finitely many
solutions?

Originally proposed by Erdős and Graham [ErGr80].
Brindza and Erdős [BrEr91] proved that there are finitely many such solutions.
-/
@[category research solved, AMS 11]
theorem erdos_405 :
    Set.Finite { x : ℕ × ℕ × ℕ | let (a, k, p) := x; p.Prime ∧ Odd p ∧
      Nat.factorial (p - 1) + a ^ (p - 1) = p ^ k} := by
  sorry

/--
Erdős and Graham [ErGr80] ask this allowing $p=2$, but this is presumably an oversight, since clearly
there are infinitely many solutions when $p=2$.

Observe that this creates 1! + a = 2^k. For all k, fix a = 2^k - 1.
-/
@[category textbook, AMS 11]
theorem erdos_405.variants.nonodd_p :
    Set.Infinite { x : ℕ × ℕ × ℕ | let (a, k, p) := x; p.Prime ∧
      Nat.factorial (p - 1) + a ^ (p - 1) = p ^ k} := by
  -- Provide the infinite family of solutions
  apply Set.infinite_of_injective_forall_mem (f := fun k ↦ (2^k - 1, k, 2))
  · -- 1. Prove the function is injective
    intro x y h
    -- Simplify the tuple equality to individual components
    simp only [Prod.mk.injEq] at h
    -- The second component equality is exactly x = y
    exact h.2.1
  · -- 2. Prove all generated tuples belong to the set
    intro k
    simp only [Set.mem_setOf_eq]
    -- Split into proving p is prime and the equation holds
    refine ⟨Nat.prime_two, ?_⟩
    -- Since p = 2, 2 - 1 = 1, so the equation simplifies definitionally
    change 1 + (2^k - 1)^1 = 2^k
    rw [pow_one]
    -- Prove 2^k is strictly positive so that (2^k - 1) doesn't underflow in Nat
    have h : 0 < 2^k := by positivity
    -- omega handles the Presburger arithmetic
    omega

/--
Yu and Liu [YuLi96] showed that the only solutions to (p-1)! + a^(p-1) = p^k
for an odd prime p are:
2! + 1^2 = 3
2! + 5^2 = 3^3
4! + 1^4 = 5^2
-/
@[category research solved, AMS 11]
theorem erdos_405.variants.yu_liu :
    { x : ℕ × ℕ × ℕ | let (a, k, p) := x; p.Prime ∧ Odd p ∧
      Nat.factorial (p - 1) + a ^ (p - 1) = p ^ k } =
    {(1, 1, 3), (5, 3, 3), (1, 2, 5)} := by
  sorry

end Erdos405
