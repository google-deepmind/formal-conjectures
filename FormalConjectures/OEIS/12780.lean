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
# Expansion of $\arcsin(\tan x)$

The sequence lists the coefficients of the odd powers in the exponential generating function
$\arcsin(\tan x)$: $a(n) = (2n+1)!\,[x^{2n+1}] \arcsin(\tan x)$ for $n \ge 0$.

*References:*
- [A012780](https://oeis.org/A012780), Patrick Demichel.
-/

@[expose] public section

namespace OeisA12780

open PowerSeries

/-- The Maclaurin series $\arcsin u = \sum_{k \ge 0} \binom{2k}{k} \frac{u^{2k+1}}{4^k (2k+1)}$. -/
noncomputable def arcsin : ℚ⟦X⟧ :=
  PowerSeries.mk fun n =>
    if n % 2 = 1 then ((n / 2).centralBinom : ℚ) / (4 ^ (n / 2) * n) else 0

/-- The Maclaurin series $\tan x = \sin x / \cos x$. -/
noncomputable def tan : ℚ⟦X⟧ := sin ℚ * (cos ℚ)⁻¹

/-- $a(n) = (2n+1)!\,[x^{2n+1}] \arcsin(\tan x)$, where `arcsin.subst tan` is the composition
$\arcsin(\tan x)$. The values lie in $\mathbb{Q}$, so the theorems below state integrality with
an integer sequence $b$ such that $b(n) = a(n)$ for all $n$. -/
noncomputable def a (n : ℕ) : ℚ := (2 * n + 1).factorial * coeff (2 * n + 1) (arcsin.subst tan)

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by
  sorry

@[category test, AMS 11]
theorem a_2 : a 2 = 45 := by
  sorry

@[category test, AMS 11]
theorem a_3 : a 3 = 1743 := by
  sorry

@[category test, AMS 11]
theorem a_4 : a 4 = 133305 := by
  sorry

/--
"Conjecture: the sequence {a(n)} reduced modulo a positive integer k is eventually periodic
with the period dividing phi(k)."
- Peter Bala, Feb 15 2026.

The theorem states that for every $k \ge 1$ there is $N$ with
$a(n + \varphi(k)) \equiv a(n) \pmod k$ for all $n \ge N$. This is equivalent, since the least
eventual period divides every eventual period. The theorem also states that every $a(n)$ is an
integer.

Proved by Wentao Li, with AI assistance, using known methods of Y. Nishibuchi, A. Kallat and
R. Blanco Gómez.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000023"]
theorem conjecture :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n ≥ N, b (n + k.totient) ≡ b n [ZMOD k] := by
  sorry

/-- The conjecture with an explicit pre-period: $a(n + \varphi(k)) \equiv a(n) \pmod k$ for every
$k \ge 1$ and every $n$ such that $2n$ is at least the exponent of each odd prime in $k$.

Proved by Wentao Li, with AI assistance, using known methods of Y. Nishibuchi, A. Kallat and
R. Blanco Gómez. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000023"]
theorem conjecture_explicit :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k n : ℕ, 1 ≤ k →
        (∀ p : ℕ, p.Prime → p ≠ 2 → k.factorization p ≤ 2 * n) →
        b (n + k.totient) ≡ b n [ZMOD k] := by
  sorry

/-- The prime $2$: $a(n + 2^{e-1}) \equiv a(n) \pmod{2^e}$ for every $e \ge 1$ and every $n$.

Proved by Wentao Li, with AI assistance, using a form of Y. Nishibuchi's criterion. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000023"]
theorem period_two_pow :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ e n : ℕ, 1 ≤ e → b (n + 2 ^ (e - 1)) ≡ b n [ZMOD 2 ^ e] := by
  sorry

/-- Odd primes: $a(n + \varphi(p^e)) \equiv a(n) \pmod{p^e}$ for every odd prime $p$, every
$e \ge 1$ and every $n \ge e/2$.

Proved by Wentao Li, with AI assistance, using the $p$-local form of the method of A. Kallat and
R. Blanco Gómez. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000023"]
theorem period_odd_prime_pow :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ p e n : ℕ, p.Prime → p ≠ 2 → 1 ≤ e → e ≤ 2 * n →
        b (n + (p ^ e).totient) ≡ b n [ZMOD p ^ e] := by
  sorry

/-- Modulo $8$, the shift $2 = \lambda(8)$ is not an eventual period:
$a(n + 2) \not\equiv a(n) \pmod 8$ for every $n$. So the Carmichael function $\lambda(k)$ cannot
replace $\varphi(k)$ in `conjecture`.

Proved by Wentao Li, with AI assistance. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000023"]
theorem not_period_two_mod_eight :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧ ∀ n, ¬ b (n + 2) ≡ b n [ZMOD 8] := by
  sorry

end OeisA12780

end
