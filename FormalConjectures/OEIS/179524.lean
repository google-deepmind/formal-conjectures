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
# Central binomial sum $a(n) = \sum_{k=0}^n (-4)^k \binom{n}{k}^2 \binom{n-k}{k}^2$

The sequence is defined by
$$a(n) = \sum_{k=0}^n (-4)^k \binom{n}{k}^2 \binom{n-k}{k}^2.$$

*References:*
- [A179524](https://oeis.org/A179524)
- Z.-W. Sun, "Open Conjectures on Congruences", arXiv preprint
  [arXiv:0911.5665](https://arxiv.org/abs/0911.5665) [math.NT], 2009-2011.-/

namespace OeisA179524

/-- The sequence $a(n) = \sum_{k=0}^n (-4)^k \binom{n}{k}^2 \binom{n-k}{k}^2$. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-4 : ℤ) ^ k * (n.choose k : ℤ) ^ 2 * ((n - k).choose k : ℤ) ^ 2

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = -15 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = -143 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by decide

/--
If $p$ is a prime with $p \equiv 1, 9 \pmod{20}$ and $p = x^2 + 5y^2$ with $x, y$ integers,
then $\sum_{k=0}^{p-1} a(k) \equiv 4x^2 - 2p \pmod{p^2}$.
- _Zhi-Wei Sun_, Jul 01 2010
-/
@[category research open, AMS 11]
theorem conjecture1 (p : ℕ) (hp : p.Prime)
    (h_mod : (p : ℤ) ≡ 1 [ZMOD 20] ∨ (p : ℤ) ≡ 9 [ZMOD 20])
    (x y : ℤ) (h_sq : (p : ℤ) = x ^ 2 + 5 * y ^ 2) :
    ∑ k ∈ Finset.range p, a k ≡ 4 * x ^ 2 - 2 * (p : ℤ) [ZMOD (p : ℤ) ^ 2] := by
  sorry

/--
If $p$ is a prime with $p \equiv 3, 7 \pmod{20}$ and $2p = x^2 + 5y^2$ with $x, y$ integers,
then $\sum_{k=0}^{p-1} a(k) \equiv 2x^2 - 2p \pmod{p^2}$.
- _Zhi-Wei Sun_, Jul 01 2010
-/
@[category research open, AMS 11]
theorem conjecture2 (p : ℕ) (hp : p.Prime)
    (h_mod : (p : ℤ) ≡ 3 [ZMOD 20] ∨ (p : ℤ) ≡ 7 [ZMOD 20])
    (x y : ℤ) (h_sq : 2 * (p : ℤ) = x ^ 2 + 5 * y ^ 2) :
    ∑ k ∈ Finset.range p, a k ≡ 2 * x ^ 2 - 2 * (p : ℤ) [ZMOD (p : ℤ) ^ 2] := by
  sorry

/--
If $p$ is a prime with $p \equiv 11, 13, 17, 19 \pmod{20}$,
then $\sum_{k=0}^{p-1} a(k) \equiv 0 \pmod{p^2}$.
- _Zhi-Wei Sun_, Jul 01 2010
-/
@[category research open, AMS 11]
theorem conjecture3 (p : ℕ) (hp : p.Prime)
    (h_mod : (p : ℤ) ≡ 11 [ZMOD 20] ∨ (p : ℤ) ≡ 13 [ZMOD 20] ∨
      (p : ℤ) ≡ 17 [ZMOD 20] ∨ (p : ℤ) ≡ 19 [ZMOD 20]) :
    ∑ k ∈ Finset.range p, a k ≡ 0 [ZMOD (p : ℤ) ^ 2] := by
  sorry

/--
$\sum_{k=0}^{n-1}(20k+17)a(k) \equiv 0 \pmod n$ for all $n=1,2,3,\dots$.
- _Zhi-Wei Sun_, Jul 01 2010
-/
@[category research open, AMS 11]
theorem conjecture4 (n : ℕ) (hn : 1 ≤ n) :
    (n : ℤ) ∣ ∑ k ∈ Finset.range n, ((20 * (k : ℤ) + 17) * a k) := by
  sorry

/--
$\sum_{k=0}^{p-1}(20k+17)a(k) \equiv p(10(-1/p)+7) \pmod{p^2}$ for any odd prime $p$.
- _Zhi-Wei Sun_, Jul 01 2010
-/
@[category research open, AMS 11]
theorem conjecture5 (p : ℕ) [hp : Fact p.Prime] (_hp2 : p ≠ 2) :
    (∑ k ∈ Finset.range p, ((20 * (k : ℤ) + 17) * a k)) ≡
      (p : ℤ) * (10 * legendreSym p (-1) + 7) [ZMOD (p : ℤ) ^ 2] := by
  sorry

end OeisA179524
