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
# Pentanacci $\pi$ sequence

Start with $a(1)=a(2)=a(3)=a(4)=a(5)=1$ and
for $n>5$, $a(n) = \pi(\sum_{j=1}^5 a(n-j))$ where $\pi = A000720$.

*References:*
- [A100478](https://oeis.org/A100478)
-/

namespace OeisA100478

open scoped Nat.Prime

/--
The primary defining sequence `a`.
Pentanacci $\pi$ sequence: $a(1)=a(2)=a(3)=a(4)=a(5)=1$;
for $n>5$, $a(n) = \pi(\sum_{j=1}^5 a(n-j))$ where $\pi = A000720$.
Note on indices: for $n \ge 0$, $a(n)$ corresponds to $A_{n+1}$ in the OEIS sequence.
-/
noncomputable def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | i + 5 =>
    let sumTerms := a (i + 4) + a (i + 3) + a (i + 2) + a (i + 1) + a i
    π sumTerms

/--
A general sequence defined by the Pentanacci $\pi$ recurrence, starting with arbitrary initial
values $v: \text{Fin } 5 \to \mathbb{N}$.
The sequence $a_{\mathrm{general}}(v, n)$ is the n-th term (0-indexed).
-/
noncomputable def aGeneral (v : Fin 5 → ℕ) (n : ℕ) : ℕ :=
  match n with
  | 0 => v 0
  | 1 => v 1
  | 2 => v 2
  | 3 => v 3
  | 4 => v 4
  | i + 5 =>
    let sumTerms :=
      aGeneral v (i + 4) + aGeneral v (i + 3) + aGeneral v (i + 2) + aGeneral v (i + 1) +
        aGeneral v i
    π sumTerms

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by rfl

/--
Starting with other values of $a(1)$, $a(2)$, $a(3)$, $a(4)$, $a(5)$ what behaviors are possible?
Does the sequence always stick at a single integer after some point, or can it go into a loop,
or is there a third pattern?
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/oeis-a100478-eventual-periodicity/blob/642eed0ffee26415528ab8c48c5181826be04860/lean/OeisA100478FC.lean#L158-L168"]
theorem conjecture (v : Fin 5 → ℕ) (h : ∀ i, v i > 0) :
  answer(True) = ∃ N P : ℕ, P > 0 ∧ (∀ n, n ≥ N → aGeneral v (n + P) = aGeneral v n) := by
  sorry

end OeisA100478
