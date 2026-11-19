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
# OEIS A012780, Bala's periodicity conjecture for $\arcsin(\tan x)$

OEIS A012780 is "Expansion of e.g.f. arcsin(tan(x)) (odd powers only)", with offset 0:
$a(n) = (2n+1)!\,[x^{2n+1}] \arcsin(\tan x)$, so $a = 1, 3, 45, 1743, 133305, \dots$.
Peter Bala conjectured (February 15, 2026): "the sequence {a(n)} reduced modulo a positive integer
k is eventually periodic with the period dividing phi(k)." It is stated here as: for every
$k \ge 1$ there is $N$ with $a(n + \varphi(k)) \equiv a(n) \pmod k$ for all $n \ge N$. Then
$\varphi(k)$ is an eventual period, and the least eventual period divides every eventual period.

The file also states the results behind the conjecture: the congruences modulo $2^e$ and modulo
odd prime powers $p^e$, with their pre-periods, and the conjecture with an explicit pre-period.
It also states that $\lambda(8) = 2$ is not an eventual period modulo $8$, so $\varphi(k)$
cannot be replaced by the Carmichael function $\lambda(k)$ in general.

In Lean, $\arcsin$ is its Maclaurin series
$\sum_{k \ge 0} \binom{2k}{k} u^{2k+1} / (4^k (2k+1))$, $\tan$ is `sin ℚ * (cos ℚ)⁻¹`, and
$\arcsin(\tan x)$ is the substitution `arcsin.subst tan`. Each theorem also states that every
$a(n)$ is an integer: it provides an integer sequence `b` with `b n = a n` for all `n`.

*References:*
- Patrick Demichel, [A012780](https://oeis.org/A012780); the conjecture is Peter Bala's comment
  of February 15, 2026.
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

/-- OEIS A012780: $a(n) = (2n+1)!\,[x^{2n+1}] \arcsin(\tan x)$. -/
noncomputable def a (n : ℕ) : ℚ := (2 * n + 1).factorial * coeff (2 * n + 1) (arcsin.subst tan)

/-- Bala's conjecture for OEIS A012780: every $a(n)$ is an integer, and for every $k \ge 1$ the
sequence $a(n) \bmod k$ is eventually periodic with period dividing $\varphi(k)$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000023"]
theorem bala_conjecture :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n ≥ N, b (n + k.totient) ≡ b n [ZMOD k] := by
  sorry

/-- The conjecture with an explicit pre-period: $a(n + \varphi(k)) \equiv a(n) \pmod k$ for every
$k \ge 1$ and every $n$ such that $2n$ is at least the exponent of each odd prime in $k$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000023"]
theorem bala_explicit :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k n : ℕ, 1 ≤ k →
        (∀ p : ℕ, p.Prime → p ≠ 2 → k.factorization p ≤ 2 * n) →
        b (n + k.totient) ≡ b n [ZMOD k] := by
  sorry

/-- The prime $2$: $a(n + 2^{e-1}) \equiv a(n) \pmod{2^e}$ for every $e \ge 1$ and every $n$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000023"]
theorem period_two_pow :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ e n : ℕ, 1 ≤ e → b (n + 2 ^ (e - 1)) ≡ b n [ZMOD 2 ^ e] := by
  sorry

/-- Odd primes: $a(n + \varphi(p^e)) \equiv a(n) \pmod{p^e}$ for every odd prime $p$, every
$e \ge 1$ and every $n \ge e/2$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000023"]
theorem period_odd_prime_pow :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ p e n : ℕ, p.Prime → p ≠ 2 → 1 ≤ e → e ≤ 2 * n →
        b (n + (p ^ e).totient) ≡ b n [ZMOD p ^ e] := by
  sorry

/-- Modulo $8$, the shift $2 = \lambda(8)$ is not an eventual period:
$a(n + 2) \not\equiv a(n) \pmod 8$ for every $n$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000023"]
theorem not_period_two_mod_eight :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧ ∀ n, ¬ b (n + 2) ≡ b n [ZMOD 8] := by
  sorry

end OeisA12780

end
