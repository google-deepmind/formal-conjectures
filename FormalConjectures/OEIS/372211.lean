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
# Bala's $p^{3k}$ supercongruences for $[x^{rn}]\, f(x)^{sn}$, $f = (1-x^m)^m/((1-x^a)^a(1-x^b)^b)$

Let $a, b \ge 1$, $m = a + b$ and
$$f_{a,b}(x) = \frac{(1 - x^m)^m}{(1 - x^a)^a\,(1 - x^b)^b} \in \mathbb{Z}[[x]].$$
For $r \ge 1$ and $s \in \mathbb{Z}$ put $u_{r,s}(n) = [x^{rn}]\, f_{a,b}(x)^{sn}$. Peter Bala
conjectures the supercongruences
$$u(np^k) \equiv u(np^{k-1}) \pmod{p^{3k}} \qquad (n, k \ge 1)$$
for these sequences:

- OEIS A372211, $(a, b) = (2, 3)$: $a(n) = [x^n]\, f(x)^n$ for all primes $p \ge 5$, and
  $u_{r,s}$ for all primes $p \ge 7$. This file states both for $p \ge 7$; the case $p = 5$ of
  $a(n)$ is not claimed here.
- OEIS A372212, $(a, b) = (2, 5)$, and OEIS A372213, $(a, b) = (3, 4)$: $a(n)$ and $u_{r,s}$
  for all primes $p \ge 11$. For A372213 this file states both for every prime $p \ge 5$ with
  $p \ne 7$, which includes Bala's range.
- OEIS A351859: $a(n) = [x^n]\, (1 + x + x^2 + x^3)^{4n}/(1 + x + x^2)^{3n}$ and
  $a(r,s;n) = [x^{rn}]\, G_3(x)^{sn}$ with $G_3 = (1 + x + x^2 + x^3)^4/(1 + x + x^2)^3$, for
  all primes $p \ge 5$. Here $G_3 = f_{1,3}$.
- A372211 also asks about the general family and about the variant
  $f^-_{a,b} = (1-x^m)^m/((1+x^a)^a(1+x^b)^b)$, for "sufficiently large primes $p$ depending on
  $m$" (`general_tower`, `general_variant_tower`). The entry writes $[x^n]$ of the series
  without the power $n$; we read it as $[x^n]\, f(x)^n$, the reading under which A000984 is the
  case $a = b = 1$, as the entry says. Read literally, the variant clause is false: for
  $(a, b) = (1, 2)$ the coefficients give $a(7) - a(1) = -6 \not\equiv 0 \pmod 7$.
  The theorems `u_tower` and `um_tower` state the towers for every prime $p \ge 5$ with
  $p \nmid abm$.

The inverse of a power series $F$ with constant term $1$ is `invOfUnit F 1`. The integer power
$F^k$ for $k < 0$ is the power of that inverse (`zpowSeries`).

*References:*
- Peter Bala, [A372211](https://oeis.org/A372211), [A372212](https://oeis.org/A372212) and
  [A372213](https://oeis.org/A372213), April 22, 2024.
- Peter Bala, [A351859](https://oeis.org/A351859), March 1, 2022.
-/

@[expose] public section

namespace OeisA372211

open PowerSeries

/-- The integer power $F^k$ of a power series $F$ with constant term $1$, for $k \in \mathbb{Z}$.
For $k < 0$ it is $(F^{-1})^{-k}$, where $F^{-1}$ = `invOfUnit F 1`. -/
noncomputable def zpowSeries (F : PowerSeries ℤ) (k : ℤ) : PowerSeries ℤ :=
  if 0 ≤ k then F ^ k.toNat else invOfUnit F 1 ^ k.natAbs

/-- $f_{a,b}(x) = (1 - x^m)^m / ((1 - x^a)^a\,(1 - x^b)^b)$ with $m = a + b$. For $a, b \ge 1$,
`invOfUnit (1 - X ^ e) 1` is the inverse of $1 - x^e$. -/
noncomputable def f (a b : ℕ) : PowerSeries ℤ :=
  (1 - X ^ (a + b)) ^ (a + b) * invOfUnit (1 - X ^ a) 1 ^ a * invOfUnit (1 - X ^ b) 1 ^ b

/-- $u_{r,s}(n) = [x^{rn}]\, f_{a,b}(x)^{sn}$. -/
noncomputable def u (a b r : ℕ) (s : ℤ) (n : ℕ) : ℤ := coeff (r * n) (zpowSeries (f a b) (s * n))

/-- **The general family.** Let $a, b \ge 1$ and let $p \ge 5$ be a prime with $p \nmid ab(a+b)$.
Then for every $r \ge 1$, every $s \in \mathbb{Z}$ and all $n, k \ge 1$:
$u_{r,s}(np^k) \equiv u_{r,s}(np^{k-1}) \pmod{p^{3k}}$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000017"]
theorem u_tower (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (hpab : ¬ p ∣ a * b * (a + b)) (r : ℕ) (hr : 0 < r) (s : ℤ) (n k : ℕ) (hn : 0 < n)
    (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ u a b r s (n * p ^ k) - u a b r s (n * p ^ (k - 1)) := by
  sorry

/-- **A372211, the general clause** for $f_{a,b}$, read as $[x^n]\, f_{a,b}(x)^n$: for every
$m$ there is $P_0$ such that for all $a, b \ge 1$ with $a + b = m$, every prime $p \ge P_0$ and
all $n, k \ge 1$: $[x^{np^k}]\, f^{np^k} \equiv [x^{np^{k-1}}]\, f^{np^{k-1}} \pmod{p^{3k}}$. -/
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

/-- **The variant family.** Let $a, b \ge 1$ and let $p \ge 5$ be a prime with
$p \nmid ab(a+b)$. Then for every $r \ge 1$, every $s \in \mathbb{Z}$ and all $n, k \ge 1$:
$u^-_{r,s}(np^k) \equiv u^-_{r,s}(np^{k-1}) \pmod{p^{3k}}$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000017"]
theorem um_tower (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (hpab : ¬ p ∣ a * b * (a + b)) (r : ℕ) (hr : 0 < r) (s : ℤ) (n k : ℕ) (hn : 0 < n)
    (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ um a b r s (n * p ^ k) - um a b r s (n * p ^ (k - 1)) := by
  sorry

/-- **A372211, the general clause** for $f^-_{a,b}$, read as $[x^n]\, f^-_{a,b}(x)^n$: for every
$m$ there is $P_0$ such that for all $a, b \ge 1$ with $a + b = m$, every prime $p \ge P_0$ and
all $n, k \ge 1$: $[x^{np^k}]\, (f^-)^{np^k} \equiv [x^{np^{k-1}}]\, (f^-)^{np^{k-1}}
\pmod{p^{3k}}$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000017"]
theorem general_variant_tower (m : ℕ) :
    ∃ P₀ : ℕ, ∀ a b : ℕ, 0 < a → 0 < b → a + b = m → ∀ p : ℕ, p.Prime → P₀ ≤ p →
      ∀ n k : ℕ, 0 < n → 0 < k →
        (p : ℤ) ^ (3 * k) ∣ coeff (n * p ^ k) (fm a b ^ (n * p ^ k)) -
          coeff (n * p ^ (k - 1)) (fm a b ^ (n * p ^ (k - 1))) := by
  sorry

/-- The series of A372211: $f(x) = (1 - x^5)^5 / ((1 - x^2)^2\,(1 - x^3)^3)$. -/
noncomputable def f372211 : PowerSeries ℤ :=
  (1 - X ^ 5) ^ 5 * invOfUnit (1 - X ^ 2) 1 ^ 2 * invOfUnit (1 - X ^ 3) 1 ^ 3

/-- OEIS A372211: $a(n) = [x^n]\, f(x)^n$. -/
noncomputable def A372211 (n : ℕ) : ℤ := coeff n (f372211 ^ n)

/-- Bala's $u(r,s;n) = [x^{rn}]\, f(x)^{sn}$ for A372211. -/
noncomputable def u372211 (r : ℕ) (s : ℤ) (n : ℕ) : ℤ :=
  coeff (r * n) (zpowSeries f372211 (s * n))

/-- **A372211**, the main conjecture for primes $p \ge 7$:
$a(np^k) \equiv a(np^{k-1}) \pmod{p^{3k}}$ for all $n, k \ge 1$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000017"]
theorem a372211_tower (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ A372211 (n * p ^ k) - A372211 (n * p ^ (k - 1)) := by
  sorry

/-- **A372211**, the conjecture for $u(r,s;n)$: for every prime $p \ge 7$, every $r \ge 1$,
every $s \in \mathbb{Z}$ and all $n, k \ge 1$:
$u(r,s;np^k) \equiv u(r,s;np^{k-1}) \pmod{p^{3k}}$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000017"]
theorem u372211_tower (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) (r : ℕ) (hr : 0 < r) (s : ℤ)
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ u372211 r s (n * p ^ k) - u372211 r s (n * p ^ (k - 1)) := by
  sorry

/-- The series of A372212: $f(x) = (1 - x^7)^7 / ((1 - x^2)^2\,(1 - x^5)^5)$. -/
noncomputable def f372212 : PowerSeries ℤ :=
  (1 - X ^ 7) ^ 7 * invOfUnit (1 - X ^ 2) 1 ^ 2 * invOfUnit (1 - X ^ 5) 1 ^ 5

/-- OEIS A372212: $a(n) = [x^n]\, f(x)^n$. -/
noncomputable def A372212 (n : ℕ) : ℤ := coeff n (f372212 ^ n)

/-- Bala's $u(r,s;n) = [x^{rn}]\, f(x)^{sn}$ for A372212. -/
noncomputable def u372212 (r : ℕ) (s : ℤ) (n : ℕ) : ℤ :=
  coeff (r * n) (zpowSeries f372212 (s * n))

/-- **A372212**, the main conjecture: for every prime $p \ge 11$ and all $n, k \ge 1$:
$a(np^k) \equiv a(np^{k-1}) \pmod{p^{3k}}$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000017"]
theorem a372212_tower (p : ℕ) (hp : p.Prime) (h11 : 11 ≤ p) (n k : ℕ) (hn : 0 < n)
    (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ A372212 (n * p ^ k) - A372212 (n * p ^ (k - 1)) := by
  sorry

/-- **A372212**, the conjecture for $u(r,s;n)$: for every prime $p \ge 11$, every $r \ge 1$,
every $s \in \mathbb{Z}$ and all $n, k \ge 1$:
$u(r,s;np^k) \equiv u(r,s;np^{k-1}) \pmod{p^{3k}}$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000017"]
theorem u372212_tower (p : ℕ) (hp : p.Prime) (h11 : 11 ≤ p) (r : ℕ) (hr : 0 < r) (s : ℤ)
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ u372212 r s (n * p ^ k) - u372212 r s (n * p ^ (k - 1)) := by
  sorry

/-- The series of A372213: $f(x) = (1 - x^7)^7 / ((1 - x^3)^3\,(1 - x^4)^4)$. -/
noncomputable def f372213 : PowerSeries ℤ :=
  (1 - X ^ 7) ^ 7 * invOfUnit (1 - X ^ 3) 1 ^ 3 * invOfUnit (1 - X ^ 4) 1 ^ 4

/-- OEIS A372213: $a(n) = [x^n]\, f(x)^n$. -/
noncomputable def A372213 (n : ℕ) : ℤ := coeff n (f372213 ^ n)

/-- Bala's $u(r,s;n) = [x^{rn}]\, f(x)^{sn}$ for A372213. -/
noncomputable def u372213 (r : ℕ) (s : ℤ) (n : ℕ) : ℤ :=
  coeff (r * n) (zpowSeries f372213 (s * n))

/-- **A372213**, the main conjecture: for every prime $p \ge 5$ with $p \ne 7$ (Bala asks for
$p \ge 11$) and all $n, k \ge 1$: $a(np^k) \equiv a(np^{k-1}) \pmod{p^{3k}}$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000017"]
theorem a372213_tower (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (h7 : p ≠ 7) (n k : ℕ) (hn : 0 < n)
    (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ A372213 (n * p ^ k) - A372213 (n * p ^ (k - 1)) := by
  sorry

/-- **A372213**, the conjecture for $u(r,s;n)$: for every prime $p \ge 5$ with $p \ne 7$ (Bala
asks for $p \ge 11$), every $r \ge 1$, every $s \in \mathbb{Z}$ and all $n, k \ge 1$:
$u(r,s;np^k) \equiv u(r,s;np^{k-1}) \pmod{p^{3k}}$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000017"]
theorem u372213_tower (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (h7 : p ≠ 7) (r : ℕ) (hr : 0 < r)
    (s : ℤ) (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ u372213 r s (n * p ^ k) - u372213 r s (n * p ^ (k - 1)) := by
  sorry

/-- $G_3(x) = (1 + x + x^2 + x^3)^4 / (1 + x + x^2)^3$. -/
noncomputable def G3 : PowerSeries ℤ :=
  (1 + X + X ^ 2 + X ^ 3) ^ 4 * invOfUnit (1 + X + X ^ 2) 1 ^ 3

/-- OEIS A351859: $a(n) = [x^n]\, (1 + x + x^2 + x^3)^{4n} / (1 + x + x^2)^{3n}$. -/
noncomputable def A351859 (n : ℕ) : ℤ :=
  coeff n ((1 + X + X ^ 2 + X ^ 3) ^ (4 * n) * invOfUnit (1 + X + X ^ 2) 1 ^ (3 * n))

/-- Bala's $a(r,s;n) = [x^{rn}]\, G_3(x)^{sn}$ for A351859. -/
noncomputable def a351859 (r : ℕ) (s : ℤ) (n : ℕ) : ℤ := coeff (r * n) (zpowSeries G3 (s * n))

/-- **A351859**, the main conjecture: for every prime $p \ge 5$ and all $n, k \ge 1$:
$a(np^k) \equiv a(np^{k-1}) \pmod{p^{3k}}$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000017"]
theorem a351859_tower (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ A351859 (n * p ^ k) - A351859 (n * p ^ (k - 1)) := by
  sorry

/-- **A351859**, the conjecture for $a(r,s;n)$: for every prime $p \ge 5$, every $r \ge 1$,
every $s \in \mathbb{Z}$ and all $n, k \ge 1$:
$a(r,s;np^k) \equiv a(r,s;np^{k-1}) \pmod{p^{3k}}$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000017"]
theorem a351859_rs_tower (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (r : ℕ) (hr : 0 < r) (s : ℤ)
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ a351859 r s (n * p ^ k) - a351859 r s (n * p ^ (k - 1)) := by
  sorry

end OeisA372211

end
