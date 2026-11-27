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
# $[x^n]\, f(x)^n$ for $f(x) = (1 - x^5)^5/((1 - x^2)^2 (1 - x^3)^3)$

The sequence is $a(n) = [x^n]\, f(x)^n$, where
$$f(x) = \frac{(1 - x^5)^5}{(1 - x^2)^2\,(1 - x^3)^3} \in \mathbb{Z}[[x]].$$

*References:*
- [A372211](https://oeis.org/A372211), Peter Bala, 2024.
-/

@[expose] public section

namespace OeisA372211

open PowerSeries

/-- The integer power $F^k$ of a power series $F$ with constant term $1$, for $k \in \mathbb{Z}$.
For $k < 0$ it is $(F^{-1})^{-k}$, where $F^{-1}$ = `invOfUnit F 1`. -/
noncomputable def zpowSeries (F : PowerSeries ℤ) (k : ℤ) : PowerSeries ℤ :=
  if 0 ≤ k then F ^ k.toNat else invOfUnit F 1 ^ k.natAbs

/-- The series $g(x) = (1 - x^5)^5 / ((1 - x^2)^2\,(1 - x^3)^3)$, written $f$ in the entry.
`invOfUnit (1 - X ^ e) 1` is the inverse of $1 - x^e$. -/
noncomputable def g : PowerSeries ℤ :=
  (1 - X ^ 5) ^ 5 * invOfUnit (1 - X ^ 2) 1 ^ 2 * invOfUnit (1 - X ^ 3) 1 ^ 3

/-- $a(n) = [x^n]\, g(x)^n$. -/
noncomputable def a (n : ℕ) : ℤ := coeff n (g ^ n)

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  sorry

@[category test, AMS 11]
theorem a_2 : a 2 = 4 := by
  sorry

@[category test, AMS 11]
theorem a_3 : a 3 = 9 := by
  sorry

@[category test, AMS 11]
theorem a_4 : a 4 = 36 := by
  sorry

/-- Bala's $u(r,s;n) = [x^{rn}]\, g(x)^{sn}$. -/
noncomputable def b (r : ℕ) (s : ℤ) (n : ℕ) : ℤ :=
  coeff (r * n) (zpowSeries g (s * n))

/--
"We conjecture that in this case the stronger supercongruences a(n*p^r) == a(n*p^(r-1))
(mod p^(3*r)) hold for all primes p >= 5 and positive integers n and r."
- Peter Bala, Apr 22 2024.

This theorem states the supercongruences for primes $p \ge 7$; the case $p = 5$ is open.

Proved by Wentao Li, with AI assistance. The proof builds on the $p^{2k}$ towers of rbajaj5 and
R. Blanco Gómez and follows rbajaj5's proof for A351858 (October 2026).
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000017"]
theorem conjecture (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ a (n * p ^ k) - a (n * p ^ (k - 1)) := by
  sorry

/--
"More generally, if r is a positive integer and s an integer then the sequence defined by
u(r,s; n) = [x^(r*n)] f(x)^(s*n) may satisfy the same supercongruences for primes p >= 7."
- Peter Bala, Apr 22 2024.

Proved by Wentao Li, with AI assistance. The proof builds on the $p^{2k}$ towers of rbajaj5 and
R. Blanco Gómez and follows rbajaj5's proof for A351858 (October 2026).
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000017"]
theorem conjecture_rs (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) (r : ℕ) (hr : 0 < r) (s : ℤ)
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ b r s (n * p ^ k) - b r s (n * p ^ (k - 1)) := by
  sorry

/-- $f_{a,b}(x) = (1 - x^m)^m / ((1 - x^a)^a\,(1 - x^b)^b)$ with $m = a + b$. For $a, b \ge 1$,
`invOfUnit (1 - X ^ e) 1` is the inverse of $1 - x^e$. -/
noncomputable def f (a b : ℕ) : PowerSeries ℤ :=
  (1 - X ^ (a + b)) ^ (a + b) * invOfUnit (1 - X ^ a) 1 ^ a * invOfUnit (1 - X ^ b) 1 ^ b

/-- $u_{r,s}(n) = [x^{rn}]\, f_{a,b}(x)^{sn}$. -/
noncomputable def u (a b r : ℕ) (s : ℤ) (n : ℕ) : ℤ := coeff (r * n) (zpowSeries (f a b) (s * n))

/-- Let $a, b \ge 1$ and let $p \ge 5$ be a prime with $p \nmid ab(a+b)$. Then for every
$r \ge 1$, every $s \in \mathbb{Z}$ and all $n, k \ge 1$:
$u_{r,s}(np^k) \equiv u_{r,s}(np^{k-1}) \pmod{p^{3k}}$.

Proved by Wentao Li, with AI assistance. The case $(a, b) = (1, 2)$, $r = s = 1$ (A351858) is
rbajaj5's, and the proof follows its reduction. The $p^{2k}$ towers are due to rbajaj5 and
R. Blanco Gómez (October 2026). -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000017"]
theorem u_tower (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (hpab : ¬ p ∣ a * b * (a + b)) (r : ℕ) (hr : 0 < r) (s : ℤ) (n k : ℕ) (hn : 0 < n)
    (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ u a b r s (n * p ^ k) - u a b r s (n * p ^ (k - 1)) := by
  sorry

/--
"Even more generally, if a, b and m are a positive integers, with m = a + b, then the sequences
whose n-th term equals [x^n] (1 - x^m)^m/((1 - x^a)^a * (1 - x^b)^b) or
[x^n] (1 - x^m)^m/((1 + x^a)^a * (1 + x^b)^b) may both satisfy the above supercongruences for
sufficiently large primes p depending on m."
- Peter Bala, Apr 22 2024.

This theorem reads the first sequence as $[x^n]\, f_{a,b}(x)^n$, so that $a = b = 1$ gives
A000984 as the entry says, and takes a bound $P_0$ that depends only on $m$.

Proved by Wentao Li, with AI assistance. The case $(a, b) = (1, 2)$ (A351858) is rbajaj5's,
and the proof follows its reduction. The $p^{2k}$ towers are due to rbajaj5 and
R. Blanco Gómez (October 2026).
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000017"]
theorem general_tower (m : ℕ) :
    ∃ P₀ : ℕ, ∀ a b : ℕ, 0 < a → 0 < b → a + b = m → ∀ p : ℕ, p.Prime → P₀ ≤ p →
      ∀ n k : ℕ, 0 < n → 0 < k →
        (p : ℤ) ^ (3 * k) ∣ coeff (n * p ^ k) (f a b ^ (n * p ^ k)) -
          coeff (n * p ^ (k - 1)) (f a b ^ (n * p ^ (k - 1))) := by
  sorry

/-- Bala's variant $f^-_{a,b}(x) = (1 - x^m)^m / ((1 + x^a)^a\,(1 + x^b)^b)$ with $m = a + b$.
For $a, b \ge 1$, `invOfUnit (1 + X ^ e) 1` is the inverse of $1 + x^e$. -/
noncomputable def fm (a b : ℕ) : PowerSeries ℤ :=
  (1 - X ^ (a + b)) ^ (a + b) * invOfUnit (1 + X ^ a) 1 ^ a * invOfUnit (1 + X ^ b) 1 ^ b

/-- $u^-_{r,s}(n) = [x^{rn}]\, f^-_{a,b}(x)^{sn}$. -/
noncomputable def um (a b r : ℕ) (s : ℤ) (n : ℕ) : ℤ :=
  coeff (r * n) (zpowSeries (fm a b) (s * n))

/-- Let $a, b \ge 1$ and let $p \ge 5$ be a prime with $p \nmid ab(a+b)$. Then for every
$r \ge 1$, every $s \in \mathbb{Z}$ and all $n, k \ge 1$:
$u^-_{r,s}(np^k) \equiv u^-_{r,s}(np^{k-1}) \pmod{p^{3k}}$.

Proved by Wentao Li, with AI assistance. The proof builds on the $p^{2k}$ towers of rbajaj5 and
R. Blanco Gómez and follows rbajaj5's proof for A351858 (October 2026). -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000017"]
theorem um_tower (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (hpab : ¬ p ∣ a * b * (a + b)) (r : ℕ) (hr : 0 < r) (s : ℤ) (n k : ℕ) (hn : 0 < n)
    (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ um a b r s (n * p ^ k) - um a b r s (n * p ^ (k - 1)) := by
  sorry

/--
"Even more generally, if a, b and m are a positive integers, with m = a + b, then the sequences
whose n-th term equals [x^n] (1 - x^m)^m/((1 - x^a)^a * (1 - x^b)^b) or
[x^n] (1 - x^m)^m/((1 + x^a)^a * (1 + x^b)^b) may both satisfy the above supercongruences for
sufficiently large primes p depending on m."
- Peter Bala, Apr 22 2024.

This theorem reads the second sequence as $[x^n]\, f^-_{a,b}(x)^n$, like the first, and takes a
bound $P_0$ that depends only on $m$.

Proved by Wentao Li, with AI assistance. The proof builds on the $p^{2k}$ towers of rbajaj5 and
R. Blanco Gómez and follows rbajaj5's proof for A351858 (October 2026).
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000017"]
theorem general_variant_tower (m : ℕ) :
    ∃ P₀ : ℕ, ∀ a b : ℕ, 0 < a → 0 < b → a + b = m → ∀ p : ℕ, p.Prime → P₀ ≤ p →
      ∀ n k : ℕ, 0 < n → 0 < k →
        (p : ℤ) ^ (3 * k) ∣ coeff (n * p ^ k) (fm a b ^ (n * p ^ k)) -
          coeff (n * p ^ (k - 1)) (fm a b ^ (n * p ^ (k - 1))) := by
  sorry

end OeisA372211

end
