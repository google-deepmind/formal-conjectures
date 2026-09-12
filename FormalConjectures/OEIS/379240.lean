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
# Arithmetic derivative equivalence sequence

Lexicographically earliest infinite sequence such that $a(i) = a(j) \implies f(i) = f(j)$,
where $f(n)$
is defined using the arithmetic derivative $A003415(n)$ and its iteration $A085731(n)$.

*References:*
- [A379240](https://oeis.org/A379240)
-/
open Nat List Finset

namespace OeisA379240

/--
A003415(n): The function $n \cdot \sum_{p \mid n} v_p(n)/p$, calculated as
$\sum_{p \mid n} v_p(n) \cdot \frac{n}{p}$.
-/
def A003415 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else ∑ p ∈ n.factorization.support, (n / p) * (n.factorization p)

/-- A359550(n) is 1 if $n$ is not divisible by any $p^p$, and 0 otherwise. -/
def A359550 (n : ℕ) : ℕ :=
  if n ≤ 1 then 1
  else if (Finset.filter (fun p => n.factorization p ≥ p) n.factorization.support).card > 0
  then 0 else 1

/-- A085731(n): $\gcd(\mathtt{A003415}(n), n)$. -/
def A085731 (n : ℕ) : ℕ := Nat.gcd (A003415 n) n

/--
A276085(n): Primorial base log-function.
For $n > 1$ with prime factorization $n = \prod p_i^{e_i}$,
$A276085(n) = \sum e_i \cdot \text{primorial}(p_i - 1)$.
-/
def A276085 (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else ∑ p ∈ n.factorization.support, (n.factorization p) * primorial (p - 1)

/-- Auxiliary loop for the primorial base exp-function A276086. -/
def A276086_loop : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | _fuel + 1, 0, _p => 1
  | fuel + 1, n, p =>
    (p ^ (n % p)) * A276086_loop fuel (n / p) (Nat.find (Nat.exists_infinite_primes (p + 1)))

/--
A276086(n): Primorial base exp-function.
-/
def A276086 (n : ℕ) : ℕ :=
  A276086_loop (n + 1) n 2

/--
A376418(n) = $n - A276086(A276085(n))$, where A276085 and A276086 are the primorial base log
and exp-functions.
-/
def A376418 (n : ℕ) : ℕ :=
  n - A276086 (A276085 n)

/-- Intermediate type for the values of the function $f(n)$ used in the RGS transform. -/
inductive A379240_F_val : Type
  | case_n (val : ℕ) : A379240_F_val
  | case_pair (a b : ℕ) : A379240_F_val
deriving DecidableEq

/-- The function $f(n)$ whose Restricted Growth Sequence transform is a. -/
def f (n : ℕ) : A379240_F_val :=
  if n = 0 then A379240_F_val.case_n 0
  else
    if A359550 n = 1 then
      A379240_F_val.case_pair (A003415 n) (A085731 n)
    else
      A379240_F_val.case_n n

/--
The Restricted Growth Sequence (RGS) Transform of a sequence $f: \mathbb{N}_{\ge 1} \to \alpha$.
$a(n)$ is 1 plus the index of $f(n)$ in the list of distinct values of $f(1), \dots, f(n)$,
ordered by first appearance.
-/
def rgs_transform {α : Type} [DecidableEq α] (f : ℕ → α) (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let f_prefix : List α := (List.range n).map (fun i => f (i + 1))
    let distinct_f_values : List α := f_prefix.eraseDups
    let target_f_val : α := f n
    -- List.idxOf returns the 0-based index.
    distinct_f_values.idxOf target_f_val + 1

/--
Lexicographically earliest infinite sequence preserving the equivalence relation of $f(n)$.
-/
def a (n : ℕ) : ℕ :=
  rgs_transform f n

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide +native

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide +native

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by decide +native

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by decide +native

@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by decide +native

@[category test, AMS 11]
theorem a_6 : a 6 = 4 := by decide +native

@[category test, AMS 11]
theorem a_7 : a 7 = 2 := by decide +native

@[category test, AMS 11]
theorem a_8 : a 8 = 5 := by decide +native

@[category test, AMS 11]
theorem a376418_56 : A376418 56 = 14 := by decide +native

@[category test, AMS 11]
theorem a376418_60 : A376418 60 = 15 := by decide +native

/--
Auxiliary function for the conjectured RGS triple.
-/
def A379240_conj_f_triple (n : ℕ) : ℕ × ℕ × ℕ :=
  (A003415 n, A085731 n, A376418 n)

/--
The Restricted Growth Sequence transform of the triple
$[\mathtt{A003415}(n), \mathtt{A085731}(n), \mathtt{A376418}(n)]$.
-/
def A379240_conjecture (n : ℕ) : ℕ :=
  rgs_transform A379240_conj_f_triple n

/--
It is conjectured that this is also the lexicographically earliest infinite sequence such
that a(i) = a(j) => A003415(i) = A003415(j), A085731(i) = A085731(j) and A376418(i) = A376418(j),
for all i, j >= 1, i.e., the restricted growth sequence transform of the triple
[A003415(n), A085731(n), A376418(n)]. This is true if for every pair of $i$ and $j$ for which
$i \ne j$, and $\mathtt{A376418}(i) = \mathtt{A376418}(j) > 0$, the ordered pairs
$[\mathtt{A003415}(i), \mathtt{A085731}(i)]$ and $[\mathtt{A003415}(j), \mathtt{A085731}(j)]$
differ from each other.
-/
@[category research open, AMS 11]
theorem a_eq_rgs_transform (n : ℕ) : a n = A379240_conjecture n := by
  sorry

end OeisA379240
