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

open Nat Finset

/--
A005187: Sum of $\lfloor n / 2^k \rfloor$ for $k \ge 0$.
This is $\sum_{k=0}^\infty \lfloor n / 2^k \rfloor$.
-/
noncomputable def A005187 (e : ℕ) : ℕ :=
  Finset.sum (Finset.range (e + 1)) fun k ↦ e / (2^k)

/--
A046644: Multiplicative function defined on prime powers $p^e$ as $2^{\text{A005187}(e)}$.
-/
noncomputable def A046644 (n : ℕ) : ℚ :=
  if n = 0 then 0
  else n.factorization.prod fun _ e ↦ (2 : ℚ) ^ (A005187 e)

/--
The sequence $f(n) \in \mathbb{Q}$ such that $f * f = \text{A046644}$.
Defined by well-founded recursion on $\mathbb{N}$ w.r.t. $<$.
-/
noncomputable def A317940_f : ℕ → ℚ :=
  WellFounded.fix (measure id).wf fun n IH ↦
    if n = 0 then 0
    else if n = 1 then 1
    else
      let A_n : ℚ := A046644 n

      let sum_of_products : ℚ := Finset.sum (divisors n) fun d ↦
        if h_prop : d > 1 ∧ d < n then
          -- Proofs that recursive arguments are smaller than n:
          have d_lt_n : d < n := h_prop.2
          let q := n / d
          have q_lt_n : q < n := Nat.div_lt_self (Nat.pos_of_ne_zero (by omega)) h_prop.1

          IH d d_lt_n * IH q q_lt_n
        else 0
      (A_n - sum_of_products) / 2

/--
A317940: Numerators of sequence whose Dirichlet convolution with itself yields A046644.
$a(n) = \text{numerator}(f(n))$, where $f*f = \text{A046644}$.
-/
noncomputable def A317940 (n : ℕ) : ℕ :=
  (A317940_f n).num.natAbs


theorem a_one : A317940 1 = 1 := by sorry

theorem a_two : A317940 2 = 1 := by sorry

theorem a_three : A317940 3 = 1 := by sorry

theorem a_four : A317940 4 = 7 := by sorry


/--
A317940 No negative terms among the first 2^20 terms. Is the sequence nonnegative?
Conjecture: The sequence of rational numbers $A317940\_f(n)$ is nonnegative for all $n \ge 1$.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://domthedeveloper.github.io/crl/math/a317940/proof/A317940_verified.lean"]
theorem A317940_f_nonnegative (n : ℕ) (h : n > 0) : A317940_f n ≥ 0 := by sorry
