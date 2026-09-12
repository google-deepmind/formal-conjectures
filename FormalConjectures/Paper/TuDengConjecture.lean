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
# Tu-Deng Conjecture

*References:*
* [Tu, Z., Deng, Y., *A conjecture about binary strings and its applications on constructing
  Boolean functions with optimal algebraic immunity*, Des. Codes Cryptogr. **60** (2011),
  1–14](https://doi.org/10.1007/s10623-010-9413-9)
* [IACR ePrint 2009/272](https://eprint.iacr.org/2009/272)

For an integer $k \ge 2$, identify the residues modulo $2^k - 1$ with the integers
$0, 1, \dots, 2^k - 2$, and let $w(a)$ denote the binary weight of $a$ (the number of ones in
its binary expansion). The Tu-Deng conjecture states that for every residue $t \ne 0$,

$$\#\{(a, b) : a + b \equiv t \pmod{2^k - 1},\ w(a) + w(b) \le k - 1\} \le 2^{k-1}.$$

Tu and Deng showed that this combinatorial statement implies that their constructions of
Boolean functions (a bent class and a balanced class) achieve optimal algebraic immunity,
which is the motivation for the conjecture. They verified the conjecture numerically for
$k \le 29$ (Remark 3.1 of the ePrint version).
-/

namespace TuDengConjecture

/-- The binary weight of a natural number: the number of ones in its binary expansion. -/
def binaryWeight (n : ℕ) : ℕ := (Nat.digits 2 n).sum

/--
**The Tu-Deng conjecture.** For $k \ge 2$ and a nonzero residue $t$ modulo $2^k - 1$, there
are at most $2^{k-1}$ pairs of residues $(a, b)$ with $a + b = t$ whose binary weights
(of their representatives in $0, \dots, 2^k - 2$) sum to at most $k - 1$.
-/
@[category research open, AMS 5 11 94]
theorem tu_deng_conjecture (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1) := by
  sorry

end TuDengConjecture
