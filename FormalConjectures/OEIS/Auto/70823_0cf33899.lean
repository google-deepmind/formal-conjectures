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

open Nat Int

/--
Helper function to calculate the number of decimal digits of $n$. For $n=0$, it returns $1$,
which is necessary for the correct concatenation behavior observed in the sequence examples.
We use the mathematical definition $\lfloor \log_{10} n \rfloor + 1$.
-/
def num_digits_base_10 (n : ℕ) : ℕ :=
  if n = 0 then 1 else (Nat.log 10 n) + 1

/-- Concatenates $x$ followed by $y$ in base 10: $x \cdot 10^{\text{num\_digits}(y)} + y$. -/
def concatenate (x y : ℕ) : ℕ :=
  x * (10 ^ (num_digits_base_10 y)) + y

/--
A070823: $a(1)=0, a(2)=1, a(n+2)=|concatenate(a(n+1),a(n))-concatenate(a(n),a(n+1))|$.
The sequence is 1-indexed.
-/
noncomputable def A070823 : ℕ → ℕ
| 0 => 0 -- Auxiliary value for total function on ℕ
| 1 => 0
| 2 => 1
| n + 3 => -- Covers indices $k \ge 4$. The terms used are $a(n+2)$ and $a(n+1)$, which are smaller indices.
  let anp1 := A070823 (n + 2) -- This corresponds to $a(k-1)$
  let an := A070823 (n + 1)   -- This corresponds to $a(k-2)$

  let cat1 := concatenate anp1 an
  let cat2 := concatenate an anp1

  -- Absolute difference: |cat1 - cat2|
  (ofNat cat1 - ofNat cat2).natAbs


theorem a_one : A070823 1 = 0 := by
  constructor

theorem a_two : A070823 2 = 1 := by
  constructor

theorem a_three : A070823 3 = 9 := by
  rw [←eq_comm, A070823]
  norm_num[concatenate, A070823]
  push_cast+decide[num_digits_base_10]

theorem a_four : A070823 4 = 72 := by
  norm_num [A070823]
  simp_all![concatenate]
  norm_num[num_digits_base_10]


/--
Conjecture: $a(n) \equiv 0 \pmod 3$ if $n>2$. Also, $a(n)$ is always of the form $2^a \cdot 3^b \cdot b'$ where $b'$ is a squarefree number.
-/
theorem A070823_conjecture : ∀ n : ℕ, 2 < n →
    (A070823 n ≡ 0 [MOD 3]) ∧
    (∃ a b b' : ℕ, A070823 n = 2^a * 3^b * b' ∧ Squarefree b') := by sorry
