/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 397

*References:*
- [erdosproblems.com/397](https://www.erdosproblems.com/397)
- [MathOverflow] (https://mathoverflow.net/questions/138209/product-of-central-binomial-coefficients)
-/

open Nat Finset

namespace Erdos397

/-- Auxiliary: c(a) = 8a² + 8a + 1. -/
private def c (a : ℕ) : ℕ := 8 * a ^ 2 + 8 * a + 1

set_option maxHeartbeats 3200000 in
/-- Key identity: C(2a,a)·C(4a+4,2a+2)·C(2c,c) = C(2a+2,a+1)·C(4a,2a)·C(2c+2,c+1). -/
private theorem central_binom_identity (a : ℕ) (ha : a ≥ 2) :
    centralBinom a * centralBinom (2 * a + 2) * centralBinom (c a) =
    centralBinom (a + 1) * centralBinom (2 * a) * centralBinom (c a + 1) := by
  simp only [centralBinom_eq_two_mul_choose, c]
  -- Cast to ℚ
  suffices h : ((2 * a).choose a : ℚ) * ((2 * (2 * a + 2)).choose (2 * a + 2)) *
      ((2 * (8 * a ^ 2 + 8 * a + 1)).choose (8 * a ^ 2 + 8 * a + 1)) =
      ((2 * (a + 1)).choose (a + 1)) * ((2 * (2 * a)).choose (2 * a)) *
      ((2 * (8 * a ^ 2 + 8 * a + 1 + 1)).choose (8 * a ^ 2 + 8 * a + 1 + 1)) by exact_mod_cast h
  rw [Nat.cast_choose ℚ (by omega : a ≤ 2 * a),
      Nat.cast_choose ℚ (by omega : 2 * a + 2 ≤ 2 * (2 * a + 2)),
      Nat.cast_choose ℚ (by omega : 8 * a ^ 2 + 8 * a + 1 ≤ 2 * (8 * a ^ 2 + 8 * a + 1)),
      Nat.cast_choose ℚ (by omega : a + 1 ≤ 2 * (a + 1)),
      Nat.cast_choose ℚ (by omega : 2 * a ≤ 2 * (2 * a)),
      Nat.cast_choose ℚ (by omega : 8 * a ^ 2 + 8 * a + 1 + 1 ≤ 2 * (8 * a ^ 2 + 8 * a + 1 + 1))]
  -- Simplify ℕ subtraction
  have hsub1 : 2 * a - a = a := by omega
  have hsub2 : 2 * (2 * a + 2) - (2 * a + 2) = 2 * a + 2 := by omega
  have hsub3 : 2 * (8 * a ^ 2 + 8 * a + 1) - (8 * a ^ 2 + 8 * a + 1) = 8 * a ^ 2 + 8 * a + 1 := by omega
  have hsub4 : 2 * (a + 1) - (a + 1) = a + 1 := by omega
  have hsub5 : 2 * (2 * a) - 2 * a = 2 * a := by omega
  have hsub6 : 2 * (8 * a ^ 2 + 8 * a + 1 + 1) - (8 * a ^ 2 + 8 * a + 1 + 1) = 8 * a ^ 2 + 8 * a + 1 + 1 := by omega
  rw [hsub1, hsub2, hsub3, hsub4, hsub5, hsub6]
  -- Clear denominators
  field_simp
  -- Now normalize argument arithmetic
  have he1 : 2 * (a + 1) = 2 * a + 2 := by ring
  have he2 : 2 * (2 * a) = 4 * a := by ring
  have he3 : 2 * (2 * a + 2) = 4 * a + 4 := by ring
  have he4 : 2 * (8 * a ^ 2 + 8 * a + 1) = 16 * a ^ 2 + 16 * a + 2 := by ring
  have he5 : 8 * a ^ 2 + 8 * a + 1 + 1 = 8 * a ^ 2 + 8 * a + 2 := by ring
  have he6 : 2 * (8 * a ^ 2 + 8 * a + 1 + 1) = 16 * a ^ 2 + 16 * a + 4 := by ring
  rw [he1, he2, he3, he4, he5, he6]
  -- Factorial recurrences
  have hf1 : (2*a+2).factorial = (2*a+2) * (2*a+1) * (2*a).factorial := by
    rw [show 2*a+2 = (2*a+1)+1 from by omega, factorial_succ,
        show 2*a+1 = (2*a)+1 from by omega, factorial_succ]; ring
  have hf2 : (a+1).factorial = (a+1) * a.factorial := factorial_succ a
  have hf3 : (8*a^2+8*a+2).factorial = (8*a^2+8*a+2) * (8*a^2+8*a+1).factorial := by
    rw [show 8*a^2+8*a+2 = (8*a^2+8*a+1)+1 from by omega, factorial_succ]
  have hf4 : (4*a+4).factorial = (4*a+4) * (4*a+3) * (4*a+2) * (4*a+1) * (4*a).factorial := by
    rw [show 4*a+4 = (4*a+3)+1 from by omega, factorial_succ,
        show 4*a+3 = (4*a+2)+1 from by omega, factorial_succ,
        show 4*a+2 = (4*a+1)+1 from by omega, factorial_succ,
        show 4*a+1 = (4*a)+1 from by omega, factorial_succ]; ring
  have hf5 : (16*a^2+16*a+4).factorial = (16*a^2+16*a+4) * (16*a^2+16*a+3) * (16*a^2+16*a+2).factorial := by
    rw [show 16*a^2+16*a+4 = (16*a^2+16*a+3)+1 from by omega, factorial_succ,
        show 16*a^2+16*a+3 = (16*a^2+16*a+2)+1 from by omega, factorial_succ]; ring
  -- Substitute and cancel factorials, leaving polynomial identity
  rw [hf1, hf2, hf3, hf4, hf5]
  push_cast
  ring

/-- For a ≥ 2, {a, 2a+2, c(a)} and {a+1, 2a, c(a)+1} are disjoint. -/
private theorem disjoint_MN (a : ℕ) (ha : a ≥ 2) :
    Disjoint ({a, 2 * a + 2, c a} : Finset ℕ) {a + 1, 2 * a, c a + 1} := by
  simp only [c, Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- For a ≥ 2, the products of centralBinom over the two Finsets are equal. -/
private theorem prod_eq (a : ℕ) (ha : a ≥ 2) :
    ∏ i ∈ ({a, 2 * a + 2, c a} : Finset ℕ), centralBinom i =
    ∏ j ∈ ({a + 1, 2 * a, c a + 1} : Finset ℕ), centralBinom j := by
  have h1 : a ≠ 2 * a + 2 := by omega
  have h2 : a ≠ c a := by unfold c; nlinarith
  have h3 : 2 * a + 2 ≠ c a := by unfold c; nlinarith
  have h4 : a + 1 ≠ 2 * a := by omega
  have h5 : a + 1 ≠ c a + 1 := by unfold c; nlinarith
  have h6 : 2 * a ≠ c a + 1 := by unfold c; nlinarith
  rw [Finset.prod_insert (show a ∉ ({2 * a + 2, c a} : Finset ℕ) from by
        simp only [Finset.mem_insert, Finset.mem_singleton]; exact fun h => h.elim h1 h2),
      Finset.prod_insert (show 2 * a + 2 ∉ ({c a} : Finset ℕ) from by
        simp only [Finset.mem_singleton]; exact h3),
      Finset.prod_singleton,
      Finset.prod_insert (show a + 1 ∉ ({2 * a, c a + 1} : Finset ℕ) from by
        simp only [Finset.mem_insert, Finset.mem_singleton]; exact fun h => h.elim h4 h5),
      Finset.prod_insert (show 2 * a ∉ ({c a + 1} : Finset ℕ) from by
        simp only [Finset.mem_singleton]; exact h6),
      Finset.prod_singleton]
  have := central_binom_identity a ha
  linarith

/-- The family a ↦ ({a, 2a+2, c(a)}, {a+1, 2a, c(a)+1}) is injective. -/
private theorem injective_family :
    Function.Injective (fun a => (({a, 2 * a + 2, c a} : Finset ℕ),
      ({a + 1, 2 * a, c a + 1} : Finset ℕ))) := by
  intro a b hab
  simp only [Prod.mk.injEq] at hab
  have ha : a ∈ ({b, 2 * b + 2, c b} : Finset ℕ) := hab.1 ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton, c] at ha
  have hb : b ∈ ({a, 2 * a + 2, c a} : Finset ℕ) := hab.1.symm ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton, c] at hb
  rcases ha with rfl | rfl | rfl
  · rfl
  · rcases hb with h | h | h <;> nlinarith
  · rcases hb with h | h | h <;> nlinarith

/--
Are there only finitely many solutions to
$$
  \prod_i \binom{2m_i}{m_i}=\prod_j \binom{2n_j}{n_j}
$$
with the $m_i,n_j$ distinct?

Somani, using ChatGPT, has given a negative answer. In fact, for any $a\geq 2$, if $c=8a^2+8a+1$,
$\binom{2a}{a}\binom{4a+4}{2a+2}\binom{2c}{c}= \binom{2a+2}{a+1}\binom{4a}{2a}\binom{2c+2}{c+1}.$
Further families of solutions are given in the comments by SharkyKesa.

This was formalized in Lean by Wu using Aristotle.
-/
@[category research solved, AMS 11,
formal_proof using formal_conjectures at "https://github.com/XC0R/formal-conjectures/blob/3c356a50a21bcbf3543f960b0c92d7fb26228cb6/FormalConjectures/ErdosProblems/397.lean#L147"]
theorem erdos_397 :
    answer(False) ↔
      {(M, N) : Finset ℕ × Finset ℕ | Disjoint M N ∧
      ∏ i ∈ M, centralBinom i = ∏ j ∈ N, centralBinom j}.Finite := by
  constructor
  · intro h; exact h.elim
  · intro hfin
    have : Set.Infinite {(M, N) : Finset ℕ × Finset ℕ | Disjoint M N ∧
        ∏ i ∈ M, centralBinom i = ∏ j ∈ N, centralBinom j} :=
      Set.infinite_of_injective_forall_mem
        (f := fun a => (({a + 2, 2 * (a + 2) + 2, c (a + 2)} : Finset ℕ),
          ({a + 2 + 1, 2 * (a + 2), c (a + 2) + 1} : Finset ℕ)))
        (fun a b hab => Nat.add_right_cancel (injective_family hab))
        (fun n => ⟨disjoint_MN (n + 2) (by omega), prod_eq (n + 2) (by omega)⟩)
    exact this.not_finite hfin

end Erdos397
