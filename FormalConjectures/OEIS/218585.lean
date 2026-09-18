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
# Partitions $n = x + y$ with $x^2 + xy + y^2$ prime

For $n \ge 1$, $a(n)$ is the number of ways to write $n$ as $x + y$ with $0 < x \le y$ such that
$x^2 + xy + y^2$ is prime.

*References:*
- [A218585](https://oeis.org/A218585)
-/

namespace OeisA218585

/-- `a n` is the number of ways to write $n = x + y$ with $0 < x \le y$ and
$x^2 + xy + y^2$ prime. -/
def a (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.Icc 1 (n / 2),
    let y := n - x
    if Nat.Prime (x ^ 2 + x * y + y ^ 2) then 1 else 0

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by decide

@[category test, AMS 11]
theorem a_7 : a 7 = 2 := by decide

@[category test, AMS 11]
theorem a_8 : a 8 = 0 := by decide

/-- For a prime $p \equiv 1 \pmod 3$, `xp p` is the unique integer $x > 0$ such that
$p = x^2 + xy + y^2$ with $x > y > 0$. -/
noncomputable def xp (p : ℕ) : ℕ :=
  sInf {x : ℕ | ∃ y : ℕ, 0 < y ∧ y < x ∧ x ^ 2 + x * y + y ^ 2 = p}

/-- For a prime $p \equiv 1 \pmod 3$, `yp p` is the unique integer $y > 0$ such that
$p = x^2 + xy + y^2$ with $x > y > 0$. -/
noncomputable def yp (p : ℕ) : ℕ :=
  sInf {y : ℕ | 0 < y ∧ ∃ x : ℕ, y < x ∧ x ^ 2 + x * y + y ^ 2 = p}

/--
Conjecture: $a(n) > 0$ for all $n > 1$ with the only exception $n = 8$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 1 < n) (h8 : n ≠ 8) : 0 < a n := by
  sorry

/--
Conjecture: The number of primes of the form $nx + (n - x)^2$
with $0 < x < n / 3$ is positive for $n > 12$.
- Zak Seidov, Sep 25 2013
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 12 < n) :
    ∃ x : ℕ, 0 < x ∧ 3 * x < n ∧ Nat.Prime (n * x + (n - x) ^ 2) := by
  sorry

/--
Conjecture:
$$\lim_{N \to \infty} \frac{\sum_{p < N, \, p \equiv 1 \pmod 3} x(p)}{\sum_{p < N, \, p \equiv 1 \pmod 3} y(p)} = 1 + \sqrt{3},$$
where for a prime $p \equiv 1 \pmod 3$, $x(p) > y(p) > 0$ are the unique positive integers such
that $p = x(p)^2 + x(p)y(p) + y(p)^2$.
- Zhi-Wei Sun
-/
@[category research open, AMS 11]
theorem conjecture3 :
    Filter.atTop.Tendsto
      (fun N : ℕ =>
        (∑ p ∈ (Finset.range N).filter (fun p => p.Prime ∧ p % 3 = 1), (xp p : ℝ)) /
        (∑ p ∈ (Finset.range N).filter (fun p => p.Prime ∧ p % 3 = 1), (yp p : ℝ)))
      (nhds (1 + Real.sqrt 3)) := by
  sorry

/--
Conjecture:
$$\lim_{N \to \infty} \frac{\sum_{p < N, \, p \equiv 1 \pmod 3} x(p)^2}{\sum_{p < N, \, p \equiv 1 \pmod 3} y(p)^2} = \frac{52}{9},$$
where for a prime $p \equiv 1 \pmod 3$, $x(p) > y(p) > 0$ are the unique positive integers such
that $p = x(p)^2 + x(p)y(p) + y(p)^2$.
- Zhi-Wei Sun
-/
@[category research open, AMS 11]
theorem conjecture4 :
    Filter.atTop.Tendsto
      (fun N : ℕ =>
        (∑ p ∈ (Finset.range N).filter (fun p => p.Prime ∧ p % 3 = 1), ((xp p : ℝ) ^ 2)) /
        (∑ p ∈ (Finset.range N).filter (fun p => p.Prime ∧ p % 3 = 1), ((yp p : ℝ) ^ 2)))
      (nhds (52 / 9 : ℝ)) := by
  sorry

end OeisA218585
