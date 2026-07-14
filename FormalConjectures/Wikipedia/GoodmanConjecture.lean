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

/-!
# Goodman's conjecture on coefficients of $p$-valent functions

A regular (analytic) function is **$p$-valent** on the unit disk if it assumes each value at most
$p$ times there, and some value exactly $p$ times. For such a function normalised as
$f(z) = z + \sum_{n \ge 2} b_n z^n$, **Goodman's conjecture** (1948) asserts that its coefficients
satisfy
$$|b_n| \le \sum_{k=1}^{p} \frac{2k (n+p)!}{(p-k)!\,(p+k)!\,(n-p-1)!\,(n^2-k^2)} |b_k|
\qquad (n > p).$$
This generalises the classical coefficient bounds for univalent functions (the case $p = 1$,
where the bound reads $|b_n| \le n$) to $p$-valent functions. It has been verified in several
special cases, including $p$-valent typically-real functions.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Goodman%27s_conjecture)
- Goodman, A. W., *On some determinants related to $p$-valent functions*,
  Trans. Amer. Math. Soc. 63 (1948), 175–192.
-/

open Complex Set

namespace GoodmanConjecture

/-- The open unit disk $\mathbb{D} = \{z : |z| < 1\}$ in the complex plane. -/
def unitDisk : Set ℂ := {z | ‖z‖ < 1}

/-- A function `f : ℂ → ℂ` is **`p`-valent** on the unit disk if it is analytic there, attains
every value at most `p` times, and attains some value exactly `p` times. Here `p ≥ 1`. -/
structure IsPValent (f : ℂ → ℂ) (p : ℕ) : Prop where
  one_le_p   : 1 ≤ p
  analyticOn : AnalyticOn ℂ f unitDisk
  /-- Every value `w` is attained at most `p` times on the disk. -/
  atMost     : ∀ w : ℂ, {z ∈ unitDisk | f z = w}.ncard ≤ p
  /-- Some value `w` is attained exactly `p` times on the disk. -/
  exactly    : ∃ w : ℂ, {z ∈ unitDisk | f z = w}.ncard = p

/-- The `n`-th Taylor coefficient of `f` at `0`, i.e. `b_n = f⁽ⁿ⁾(0) / n!`. With the normalisation
`f z = z + ∑_{n ≥ 2} b_n zⁿ` used below, `coeff f 1 = 1`. -/
noncomputable def coeff (f : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n f 0 / n.factorial

/-- Goodman's normalisation `f z = z + ∑_{n ≥ 2} b_n zⁿ`, i.e. `f 0 = 0` and `f'(0) = 1`. -/
structure IsNormalized (f : ℂ → ℂ) : Prop where
  map_zero   : f 0 = 0
  deriv_zero : deriv f 0 = 1

/-- The Goodman bound
$$\sum_{k=1}^{p} \frac{2k (n+p)!}{(p-k)!\,(p+k)!\,(n-p-1)!\,(n^2-k^2)} |b_k|,$$
the conjectured upper bound for $|b_n|$. -/
noncomputable def goodmanBound (f : ℂ → ℂ) (p n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 p,
    (2 * k * (n + p).factorial : ℝ) /
      ((p - k).factorial * (p + k).factorial * (n - p - 1).factorial * ((n : ℝ) ^ 2 - k ^ 2)) *
      ‖coeff f k‖

/--
**Goodman's conjecture.** For every `p`-valent normalised function `f` on the unit disk and every
`n > p`, the `n`-th coefficient is bounded by the Goodman bound:
$$|b_n| \le \sum_{k=1}^{p} \frac{2k (n+p)!}{(p-k)!\,(p+k)!\,(n-p-1)!\,(n^2-k^2)} |b_k|.$$
-/
@[category research open, AMS 30]
theorem goodman_conjecture (f : ℂ → ℂ) (p n : ℕ) (hf : IsPValent f p)
    (hf' : IsNormalized f) (hn : p < n) :
    ‖coeff f n‖ ≤ goodmanBound f p n := by
  sorry

/--
Sanity check: in the univalent case `p = 1`, the Goodman bound reduces to the classical
Bieberbach-type bound `|b_n| ≤ n` (using `b_1 = 1`). Concretely the single `k = 1` summand is
$$\frac{2 (n+1)!}{0!\,2!\,(n-2)!\,(n^2-1)} = \frac{(n+1)!}{(n-2)!\,(n^2-1)} = n,$$
so `goodmanBound f 1 n = n * ‖coeff f 1‖`.
-/
@[category test, AMS 30]
theorem goodmanBound_one (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n) :
    goodmanBound f 1 n = n * ‖coeff f 1‖ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [goodmanBound, Finset.Icc_self, Finset.sum_singleton]
  congr 1
  have e3 : (m + 2 - 1 - 1 : ℕ) = m := by omega
  have e4 : (m + 2 + 1 : ℕ) = m + 3 := by omega
  rw [e3, e4]
  have hfact : ((m + 3).factorial : ℝ) = (m + 3) * (m + 2) * (m + 1) * (m.factorial : ℝ) := by
    have h1 : (m + 3).factorial = (m + 3) * (m + 2).factorial := rfl
    have h2 : (m + 2).factorial = (m + 2) * (m + 1).factorial := rfl
    have h3 : (m + 1).factorial = (m + 1) * m.factorial := rfl
    rw [h1, h2, h3]; push_cast; ring
  rw [hfact]
  have hmf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hm3 : ((m : ℝ) + 3) ≠ 0 := by positivity
  have hsq : ((m : ℝ) + 2) ^ 2 - (1 : ℝ) ^ 2 = ((m : ℝ) + 1) * ((m : ℝ) + 3) := by ring
  push_cast
  rw [hsq]
  field_simp
  ring

end GoodmanConjecture
