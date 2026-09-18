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

import FormalConjecturesUtil

/-!
# Erdős Problem 1209

*References:*
- [erdosproblems.com/429](https://www.erdosproblems.com/429)
- [erdosproblems.com/1102](https://www.erdosproblems.com/1102)
- [erdosproblems.com/1209](https://www.erdosproblems.com/1209)
- [Er80] Erdős, Paul, A survey of problems in combinatorial number theory. Ann. Discrete Math.
  (1980), 89-115.
-/

open Nat Set

namespace Erdos1209

/-- For every `k ≥ 1` and bound `m`, there is a prime `p > m` such that `k + p` is composite:
take a prime `q > k` and, by Dirichlet, a prime `p > max m q` with `p ≡ -k (mod q)`. -/
@[category API, AMS 11]
theorem exists_prime_gt_not_prime_add (k m : ℕ) (hk : 1 ≤ k) :
    ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime := by
  obtain ⟨q, hqk, hq⟩ := Nat.exists_infinite_primes (k + 1)
  have : NeZero q := ⟨hq.ne_zero⟩
  have hunit : IsUnit (-(k : ZMod q)) := by
    refine IsUnit.neg ?_
    rw [ZMod.isUnit_iff_coprime]
    exact (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hq).2
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))))
  obtain ⟨p, hp, hpp, hpq⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit (max m q)
  refine ⟨p, by omega, hpp, ?_⟩
  have hdvd : q ∣ k + p := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, hpq]
    ring
  exact Nat.not_prime_of_dvd_of_lt hdvd hq.two_le (by omega)

/-- The counterexample sequence: `a 0` is a prime at least `f 0`, and `a (k + 1)` is a prime
larger than `a k` and `f (k + 1)` with `(k + 1) + a (k + 1)` composite. -/
noncomputable def seq (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => Classical.choose (Nat.exists_infinite_primes (f 0))
  | k + 1 => Classical.choose (exists_prime_gt_not_prime_add (k + 1) (max (seq f k) (f (k + 1)))
      (by omega))

/-- The defining properties of `seq f 0`. -/
@[category API, AMS 11]
theorem seq_zero_spec (f : ℕ → ℕ) : f 0 ≤ seq f 0 ∧ (seq f 0).Prime :=
  Classical.choose_spec (Nat.exists_infinite_primes (f 0))

/-- The defining properties of `seq f (k + 1)`. -/
@[category API, AMS 11]
theorem seq_succ_spec (f : ℕ → ℕ) (k : ℕ) :
    max (seq f k) (f (k + 1)) < seq f (k + 1) ∧ (seq f (k + 1)).Prime ∧
      ¬ ((k + 1) + seq f (k + 1)).Prime :=
  Classical.choose_spec (exists_prime_gt_not_prime_add (k + 1) (max (seq f k) (f (k + 1)))
    (by omega))

/--
Let $A=\{a_1<a_2<\cdots\}$ be a sequence of integers which tends to infinity sufficiently fast.
If there is an $n$ such that all $n+a_k$ are primes then must there exist infinitely many such $n$?

Erdős [Er80] wrote 'unless I overlook a trivial way of getting a counterexample these questions
are quite hopeless'. There is indeed a trivial counterexample (a variant of the construction in
[erdosproblems.com/429]): define $a_1=2$ and for $k\geq 2$ let $a_k>a_{k-1}$ be a prime such that
$a_k+k\equiv 0\pmod{q_k}$, where $q_k$ is some prime not dividing $k$. This sequence can be made to
grow arbitrarily fast

See also [erdosproblems.com/429] and [erdosproblems.com/1102].
-/
@[category research solved, AMS 11]
theorem erdos_1209.parts.i :
    answer(False) ↔
      ∃ f : ℕ → ℕ, ∀ a : ℕ → ℕ, StrictMono a → (∀ k, f k ≤ a k) →
        (∃ n, ∀ k, (n + a k).Prime) →
        {n | ∀ k, (n + a k).Prime}.Infinite := by
  refine ⟨fun h => h.elim, fun ⟨f, hf⟩ => ?_⟩
  have hmono : StrictMono (seq f) :=
    strictMono_nat_of_lt_succ fun k => lt_of_le_of_lt (le_max_left _ _) (seq_succ_spec f k).1
  have hbound : ∀ k, f k ≤ seq f k := by
    intro k
    cases k with
    | zero => exact (seq_zero_spec f).1
    | succ k => exact (lt_of_le_of_lt (le_max_right _ _) (seq_succ_spec f k).1).le
  have hprime : ∀ k, (seq f k).Prime := by
    intro k
    cases k with
    | zero => exact (seq_zero_spec f).2
    | succ k => exact (seq_succ_spec f k).2.1
  have hinf := hf (seq f) hmono hbound ⟨0, fun k => by simpa using hprime k⟩
  -- but the set is contained in `{0}`
  refine hinf ((Set.finite_singleton 0).subset fun n hn => ?_)
  rw [Set.mem_singleton_iff]
  by_contra hn0
  exact (seq_succ_spec f (n - 1)).2.2 (by
    have := hn n
    rwa [show n - 1 + 1 = n by omega] )


/-- For every `k ≥ 1` and bound `m`, there is a prime `p > m` such that `k + p` is not squarefree:
take a prime `q > k` and, by Dirichlet, a prime `p > m` with `p ≡ -k (mod q ^ 2)`. -/
@[category API, AMS 11]
theorem exists_prime_gt_not_squarefree_add (k m : ℕ) (hk : 1 ≤ k) :
    ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p) := by
  obtain ⟨q, hqk, hq⟩ := Nat.exists_infinite_primes (k + 1)
  have : NeZero (q ^ 2) := ⟨pow_ne_zero 2 hq.ne_zero⟩
  have hunit : IsUnit (-(k : ZMod (q ^ 2))) := by
    refine IsUnit.neg ?_
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right 2 (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hq).2
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))))
  obtain ⟨p, hp, hpp, hpq⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit m
  refine ⟨p, hp, hpp, ?_⟩
  have hdvd : q ^ 2 ∣ k + p := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, hpq]
    ring
  rw [Nat.squarefree_iff_prime_squarefree]
  push Not
  exact ⟨q, hq, by rwa [← sq]⟩

/-- The counterexample sequence for the squarefree variant. -/
noncomputable def seq' (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => Classical.choose (Nat.exists_infinite_primes (f 0))
  | k + 1 => Classical.choose (exists_prime_gt_not_squarefree_add (k + 1)
      (max (seq' f k) (f (k + 1))) (by omega))

/-- The defining properties of `seq' f (k + 1)`. -/
@[category API, AMS 11]
theorem seq'_succ_spec (f : ℕ → ℕ) (k : ℕ) :
    max (seq' f k) (f (k + 1)) < seq' f (k + 1) ∧ (seq' f (k + 1)).Prime ∧
      ¬ Squarefree ((k + 1) + seq' f (k + 1)) :=
  Classical.choose_spec (exists_prime_gt_not_squarefree_add (k + 1) (max (seq' f k) (f (k + 1)))
    (by omega))

/--
What if we ask for $n+a_k$ to be squarefree instead of prime?

A similar construction provides a counterexample to the squarefree question.
-/
@[category research solved, AMS 11]
theorem erdos_1209.parts.ii :
    answer(False) ↔
      ∃ f : ℕ → ℕ, ∀ a : ℕ → ℕ, StrictMono a → (∀ k, f k ≤ a k) →
        (∃ n, ∀ k, Squarefree (n + a k)) →
        {n | ∀ k, Squarefree (n + a k)}.Infinite := by
  refine ⟨fun h => h.elim, fun ⟨f, hf⟩ => ?_⟩
  have h0 := Classical.choose_spec (Nat.exists_infinite_primes (f 0))
  have hmono : StrictMono (seq' f) :=
    strictMono_nat_of_lt_succ fun k => lt_of_le_of_lt (le_max_left _ _) (seq'_succ_spec f k).1
  have hbound : ∀ k, f k ≤ seq' f k := by
    intro k
    cases k with
    | zero => exact h0.1
    | succ k => exact (lt_of_le_of_lt (le_max_right _ _) (seq'_succ_spec f k).1).le
  have hprime : ∀ k, (seq' f k).Prime := by
    intro k
    cases k with
    | zero => exact h0.2
    | succ k => exact (seq'_succ_spec f k).2.1
  have hinf := hf (seq' f) hmono hbound
    ⟨0, fun k => by simpa using (hprime k).prime.squarefree⟩
  refine hinf ((Set.finite_singleton 0).subset fun n hn => ?_)
  rw [Set.mem_singleton_iff]
  by_contra hn0
  exact (seq'_succ_spec f (n - 1)).2.2 (by
    have := hn n
    rwa [show n - 1 + 1 = n by omega])


/--
Are there $n$ such that $n+2^{2^k}$ is always a prime?

ebarschkis and GPT have proved that there are no $n$ such that $n+2^{2^k}$ is always prime: let
$n\geq 3$ be any odd integer. If $k$ is chosen sufficiently large, and $p=n+2^{2^{k}}$ is prime,
then the multiplicative order of $2^{2^k}\pmod{p}$, say $m$ is odd, and hence if $l$ is chosen such
that $2^l\equiv 1\pmod{m}$ then $p\mid n+2^{2^{k+rl}}$ for all $r\geq 1$.

This was formalized in Lean by Barschkis using ChatGPT.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/ebarschkis/ErdosProblem/blob/main/Problem1209/Formalization.lean"]
theorem erdos_1209.parts.iii.a :
    answer(False) ↔ ∃ n : ℕ, ∀ k : ℕ, (n + 2 ^ (2 ^ k)).Prime := by
  sorry

/--
Are there $n$ such that $n+2^{2^k}$ is always squarefree?
-/
@[category research open, AMS 11]
theorem erdos_1209.parts.iii.b :
    answer(sorry) ↔ ∃ n : ℕ, ∀ k : ℕ, Squarefree (n + 2 ^ (2 ^ k)) := by
  sorry

/--
Are there $n$ such that $n+2^{2^k}$ is infinitely often a prime?
-/
@[category research open, AMS 11]
theorem erdos_1209.parts.iii.c :
    answer(sorry) ↔ ∃ n : ℕ, {k | (n + 2 ^ (2 ^ k)).Prime}.Infinite := by
  sorry

/--
Are there $n$ such that $n+2^{2^k}$ is infinitely often squarefree?
-/
@[category research open, AMS 11]
theorem erdos_1209.parts.iii.d :
    answer(sorry) ↔ ∃ n : ℕ, {k | Squarefree (n + 2 ^ (2 ^ k))}.Infinite := by
  sorry

end Erdos1209
