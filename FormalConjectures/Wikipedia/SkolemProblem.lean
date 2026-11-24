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
module

public import FormalConjecturesUtil

/-!
# The Skolem problem

For a sequence $u : \mathbb{N} \to \mathbb{Z}$ satisfying a homogeneous linear recurrence
$u(n + k) = \sum_{i=0}^{k-1} c_i u(n + i)$ with integer coefficients, Thoralf Skolem (1933, 1934),
Kurt Mahler (1935), and Christer Lech (1953) established the **Skolem–Mahler–Lech** periodicity
result: the zero set $\{n \in \mathbb{N} \mid u(n) = 0\}$ is eventually periodic.

Because $p$-adic proofs of Skolem–Mahler–Lech are ineffective on isolated zeros, the **Skolem
problem** asks whether an algorithm can decide whether a given integer linear recurrence sequence
attains the value $0$. Maurice Mignotte, Tarlok Nath Shorey, and Robert Tijdeman (1984) and Nikolay
Vereshchagin (1985) proved decidability for recurrences of order at most $4$; decidability remains
open at order $5$ and in general [OW12].

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Skolem_problem)
- [Sk34] T. Skolem, *Ein Verfahren zur Behandlung gewisser exponentialer Gleichungen und
  diophantischer Gleichungen*, 8. Skand. Mat.-Kongr. Stockholm (1934), 163–188.
- [MST84] M. Mignotte, T. N. Shorey, and R. Tijdeman, *The distance between terms of an algebraic
  recurrence sequence*, J. Reine Angew. Math. 349 (1984), 63–76.
- [Ve85] N. K. Vereshchagin, *The problem of the appearance of a zero in a linear recursive
  sequence*, Mat. Zametki 38 (1985), no. 2, 177–189.
- [OW12] J. Ouaknine and J. Worrell, *Decision problems for linear recurrence sequences*, in
  Reachability Problems (RP 2012), Lecture Notes in Comput. Sci. 7550, Springer, 2012, pp. 21–28.
-/

@[expose] public section

namespace SkolemProblem

/-- Zero set $\{n \in \mathbb{N} \mid u(n) = 0\}$ of an integer sequence $u : \mathbb{N} \to
\mathbb{Z}$. -/
def skolemZeroSet (u : ℕ → ℤ) : Set ℕ :=
  {n : ℕ | u n = 0}

/-- Maximum absolute value among the recurrence coefficients `E.coeffs i` and initial values `u i`
for $0 \le i < E.\text{order}$. -/
def recurrenceHeight (E : LinearRecurrence ℤ) (u : ℕ → ℤ) : ℕ :=
  max ((List.ofFn fun i : Fin E.order ↦ (E.coeffs i).natAbs).foldr max 0)
      ((List.ofFn fun i : Fin E.order ↦ (u i.1).natAbs).foldr max 0)

/-- The zero sequence has zero set `Set.univ`, which is eventually periodic. -/
@[category test, AMS 11 68]
theorem isEventuallyPeriodic_skolemZeroSet_zero :
    SymbolicDynamics.IsEventuallyPeriodic (skolemZeroSet (0 : ℕ → ℤ)) :=
  ⟨1, Nat.one_pos, Filter.Eventually.of_forall fun _ ↦ rfl⟩

/-- For the constant sequence $u(n) = 1$, `skolemZeroSet u` is empty. -/
@[category test, AMS 11 68]
theorem skolemZeroSet_const_one :
    skolemZeroSet (fun _ : ℕ ↦ (1 : ℤ)) = ∅ := by
  ext n
  simp [skolemZeroSet]

/-- The prime indicator predicate is not eventually periodic. -/
@[category test, AMS 11 68]
theorem not_isEventuallyPeriodic_primes :
    ¬ SymbolicDynamics.IsEventuallyPeriodic {n : ℕ | n.Prime} := by
  rintro ⟨p, hp, hper⟩
  rw [Filter.eventually_atTop] at hper
  rcases hper with ⟨N₀, hper⟩
  obtain ⟨q, hq_le, hq_prime⟩ := Nat.exists_infinite_primes (N₀ + p + 2)
  have hstep : ∀ k : ℕ, (q + k * p).Prime := by
    intro k
    induction k with
    | zero => simpa using hq_prime
    | succ k ih =>
      have hqp : (q + k * p + p).Prime = (q + k * p).Prime := hper (q + k * p) (by omega)
      have hmem : (q + k * p + p).Prime := hqp.mpr ih
      rwa [Nat.succ_mul, ← add_assoc]
  have hcomp : ¬ (q + q * p).Prime := by
    have hfac : q + q * p = q * (1 + p) := by ring
    rw [hfac, Nat.prime_mul_iff]
    have hq2 : 2 ≤ q := hq_prime.two_le
    omega
  exact hcomp (hstep q)

/-- The affine sequence $u(n) = n - 3$ solves the order-$2$ recurrence
$u(n + 2) = -u(n) + 2 u(n + 1)$. -/
@[category test, AMS 11 68]
theorem isSolution_order_two_example :
    (⟨2, ![-1, 2]⟩ : LinearRecurrence ℤ).IsSolution (fun n ↦ (n : ℤ) - 3) := by
  intro n
  simp [Fin.sum_univ_two]
  ring

/-- For the order-$2$ recurrence $u(n + 2) = -u(n) + 2 u(n + 1)$ and solution $u(n) = n - 3$,
`recurrenceHeight` equals $3$. -/
@[category test, AMS 11 68]
theorem recurrenceHeight_order_two_example :
    recurrenceHeight ⟨2, ![-1, 2]⟩ (fun n ↦ (n : ℤ) - 3) = 3 := by
  decide

/-- For $u(n) = n - 3$, the zero set is $\{3\}$. -/
@[category test, AMS 11 68]
theorem skolemZeroSet_sub_three :
    skolemZeroSet (fun n ↦ (n : ℤ) - 3) = {3} := by
  ext n
  simp only [skolemZeroSet, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  omega

/-- **Skolem–Mahler–Lech Theorem** ([Sk34]; Mahler 1935; Lech 1953): For every integer linear
recurrence $E$ and solution $u : \mathbb{N} \to \mathbb{Z}$, the zero set `skolemZeroSet u` is
eventually periodic. -/
@[category research solved, AMS 11 68]
theorem skolem_mahler_lech (E : LinearRecurrence ℤ) (u : ℕ → ℤ) (hsol : E.IsSolution u) :
    SymbolicDynamics.IsEventuallyPeriodic (skolemZeroSet u) := by
  sorry

/-- **Decidability of the Skolem Problem for Order $\le 4$** ([MST84]; [Ve85]): There exists a
computable bound $B(H)$ such that every integer linear recurrence sequence of order at most $4$ and
height $H$ that attains $0$ vanishes at some index $n \le B(H)$. -/
@[category research solved, AMS 11 68]
theorem skolem_problem_order_le_four :
    ∃ B : ℕ → ℕ, Computable B ∧
      ∀ (E : LinearRecurrence ℤ) (u : ℕ → ℤ),
        E.order ≤ 4 → E.IsSolution u → (∃ n : ℕ, u n = 0) →
          ∃ n : ℕ, n ≤ B (recurrenceHeight E u) ∧ u n = 0 := by
  sorry

/-- **The Skolem Problem**: Is there an algorithm deciding whether an integer linear recurrence
sequence attains $0$?

Note: Because only finitely many integer recurrences and initial tuples share a given order $k$ and
height $H$, algorithmic decidability amounts to having a computable bound $B(k, H)$ on the smallest
index $n$ with $u(n) = 0$. -/
@[category research open, question, AMS 11 68]
theorem skolem_problem :
    ∃ B : ℕ → ℕ → ℕ, Computable₂ B ∧
      ∀ (E : LinearRecurrence ℤ) (u : ℕ → ℤ),
        E.IsSolution u → (∃ n : ℕ, u n = 0) →
          ∃ n : ℕ, n ≤ B E.order (recurrenceHeight E u) ∧ u n = 0 := by
  sorry

/-- **The Order-$5$ Skolem Problem** ([OW12]): Is the Skolem problem decidable for integer linear
recurrences of order $5$ (equivalently, does there exist a computable bound $B(H)$ on the smallest
zero index of an order-$5$ recurrence of height $H$)? -/
@[category research open, question, AMS 11 68]
theorem skolem_problem.variants.order_five :
    ∃ B : ℕ → ℕ, Computable B ∧
      ∀ (E : LinearRecurrence ℤ) (u : ℕ → ℤ),
        E.order = 5 → E.IsSolution u → (∃ n : ℕ, u n = 0) →
          ∃ n : ℕ, n ≤ B (recurrenceHeight E u) ∧ u n = 0 := by
  sorry

end SkolemProblem
