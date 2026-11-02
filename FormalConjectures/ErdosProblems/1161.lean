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
# Erdős Problem 1161

*References:*
- [erdosproblems.com/1161](https://www.erdosproblems.com/1161)
- [Be25d] Beker, Adrian, *The most probable order of a random permutation*.
  [arXiv:2510.11698](https://arxiv.org/abs/2510.11698) (2025).
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference
  "Paul Erdős and his mathematics", Budapest, July 1999 (1999).
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos1161

/-- `f k n` is $f_k(n)$, the number of elements of $S_n$ of order exactly $k$. Here $S_n$ is
`Equiv.Perm (Fin n)`. Since every element of a finite group has positive order, `f 0 n = 0`. -/
noncomputable def f (k n : ℕ) : ℕ :=
  Fintype.card {σ : Equiv.Perm (Fin n) // orderOf σ = k}

/-- `maxF n` is $\max_{k \geq 1} f_k(n)$. Only the orders that occur in $S_n$ are considered,
because `f k n = 0` for every other `k`. -/
noncomputable def maxF (n : ℕ) : ℕ :=
  (Finset.univ.image fun σ : Equiv.Perm (Fin n) ↦ orderOf σ).sup fun k ↦ f k n

/-- No element of $S_n$ has order $0$. -/
@[category API, AMS 5 20]
theorem f_zero (n : ℕ) : f 0 n = 0 := by
  unfold f
  rw [Fintype.card_eq_zero_iff]
  exact ⟨fun ⟨σ, hσ⟩ => (orderOf_pos σ).ne' hσ⟩

/-- Only the identity has order $1$. -/
@[category API, AMS 5 20]
theorem f_one (n : ℕ) : f 1 n = 1 := by
  unfold f
  rw [Fintype.card_eq_one_iff]
  exact ⟨⟨1, orderOf_one⟩, fun ⟨σ, hσ⟩ => Subtype.ext (orderOf_eq_one_iff.mp hσ)⟩

/-- The answer: the least $k\geq 1$ with $[1,\ldots,n-k]\mid k$ (as a set with one element). -/
def erdos_1161.answer (n : ℕ) : Set ℕ :=
  {k | IsLeast {m : ℕ | 0 < m ∧ Nat.lcmUpto (n - m) ∣ m} k}

set_option linter.style.formal_proof_palomar false in
/--
Let $f_k(n)$ count the number of elements of $S_n$ of order $k$. For which values of $k$ will
$f_k(n)$ be maximal? [Va99, 5.72]

Beker [Be25d, Theorem 1.2] proved that, for all large $n$, $f_k(n)$ is maximal if and only if
$k\geq 1$ is minimal such that $[1,\ldots,n-k]\mid k$, where $[\cdot]$ is the least common
multiple. The last clause on erdosproblems.com/1161 reads "$f_k(n)=(n-1)!$" instead of "$f_k(n)$
is maximal"; we follow [Be25d]. For $k > n$ we read $n-k$ as $0$, which does not change the
least such $k$, because $k = n$ qualifies.
-/
@[category research solved, question value, AMS 5 20, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1161.lean#L50"]
theorem erdos_1161 :
    ∀ᶠ n : ℕ in atTop, {k : ℕ | ∀ j : ℕ, f j n ≤ f k n} = erdos_1161.answer n := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
Beker [Be25d, Theorem 1.1] proved that
$$\max_{k\geq 1} f_k(n)\sim (n-1)!.$$
-/
@[category research solved, AMS 5 20, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1161.lean#L50"]
theorem erdos_1161.variants.max_asymptotic :
    (fun n : ℕ ↦ (maxF n : ℝ)) ~[atTop] (fun n : ℕ ↦ ((n - 1).factorial : ℝ)) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
Beker [Be25d, Theorem 1.1] also proved that, if $n$ is sufficiently large and
$f_k(n)\geq (n-1)!$, then $[1,\ldots,n-k]\mid k$. The statement also records $1\leq k\leq n$,
since [Be25d] writes such $k$ as $n-k'$ with $0\leq k'\leq n-1$.
-/
@[category research solved, AMS 5 20, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1161.lean#L50"]
theorem erdos_1161.variants.threshold :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, (n - 1).factorial ≤ f k n →
      k ≤ n ∧ 0 < k ∧ Nat.lcmUpto (n - k) ∣ k := by
  sorry

end Erdos1161
