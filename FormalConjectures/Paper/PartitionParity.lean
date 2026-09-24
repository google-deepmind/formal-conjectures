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
# Parities of partition numbers

There are several conjectures on parities of partition numbers. The most famous conjecture is the
Parkin-Shanks conjecture, which states that the natural density of `n` where the partition number
`p(n)` is even (resp. odd) exists and equals `1/2`.

There are several related (weaker) results toward the conjecture. Kolberg showed that `p(n)` takes
each parity infinitely often. Subbarao conjectured that every arithmetic progression `r (mod t)`
contains infinitely many `n` with `p(n)` even and infinitely many `n` with `p(n)` odd; the even
case was proved by Ono and the odd case by Radu. Quantitative lower bounds for the number of
`n ≤ X` with `p(n)` even (resp. odd) have also been studied. The best known bounds are
`≫ √X log log X` for even values (Bellaïche–Nicolas) and `≫ √X` for odd values (Zheng, in an
appendix to Ono–Swaminathan). Ono–Swaminathan also proved that both parities occur infinitely often
along the quadratic progressions `(D m² + 1) / 24`, and Ono conjectured the same for every nonconstant
integer-valued polynomial that is eventually positive.

*References:*
* [On the distribution of parity in the partition function](https://www.jstor.org/stable/2003251),
  T. R. Parkin, D. Shanks, Math. Comp. 21 (1967), 466–480.
* [Note on the parity of the partition function](https://doi.org/10.7146/math.scand.a-10584),
  O. Kolberg, Math. Scand. 7 (1959), 377–378.
* Some remarks on the partition function, M. V. Subbarao, Amer. Math. Monthly 73 (1966), 851–854.
* [Parity of the partition function in arithmetic progressions](https://doi.org/10.1515/crll.1996.472.1),
  K. Ono, J. Reine Angew. Math. 472 (1996), 1–15.
* [Distribution of parity of the partition function in arithmetic progressions](https://doi.org/10.1016/S0019-3577(99)80014-7),
  S. Ahlgren, Indag. Math. (N.S.) 10 (1999), 173–181.
* [Parity of the partition function](https://doi.org/10.1016/j.aim.2010.02.023), K. Ono,
  Adv. Math. 225 (2010), 349–366.
* [A proof of Subbarao's conjecture](https://doi.org/10.1515/CRELLE.2011.165), C.-S. Radu,
  J. Reine Angew. Math. 672 (2012), 161–175.
* [Parité des coefficients de formes modulaires](https://doi.org/10.1007/s11139-014-9645-9),
  J. Bellaïche, J.-L. Nicolas, Ramanujan J. 40 (2016), 1–44.
* [Nonzero coefficients of half-integral weight modular forms mod ℓ](https://arxiv.org/abs/1704.07440),
  J. Bellaïche, B. Green, K. Soundararajan, Res. Math. Sci. 5 (2018), Paper No. 6.
* [Parity of the partition function in quadratic progressions](https://arxiv.org/abs/2509.09553)
  (with an appendix by Q.-Y. Zheng), K. Ono, A. Swaminathan, arXiv:2509.09553.
-/

@[expose] public section

namespace PartitionParity

open Nat Real Filter Topology Asymptotics Polynomial

/-- `p(n)` is even for infinitely many `n` and odd for infinitely many `n`. (Kolberg) -/
@[category research solved, AMS 11]
theorem kolberg :
    {n : ℕ | Even (partitionNumber n)}.Infinite ∧ {n : ℕ | Odd (partitionNumber n)}.Infinite := by
  sorry

/-- The natural density of `n` where the partition number `p(n)` is even (resp. odd) exists and
equals `1/2`. -/
@[category research open, AMS 11]
theorem parkin_shanks :
    {n : ℕ | Even (partitionNumber n)}.HasDensity (1 / 2) ∧
    {n : ℕ | Odd (partitionNumber n)}.HasDensity (1 / 2) := by
  sorry

/-- Every arithmetic progression contains infinitely many `n` where `p(n)` is even.
Conjectured by Subbarao and proved by Ono. -/
@[category research solved, AMS 11]
theorem subbarao.even : ∀ r t, 0 < t →
    {n : ℕ | n ≡ r [MOD t] ∧ Even (partitionNumber n)}.Infinite := by
  sorry

/-- Every arithmetic progression contains infinitely many `n` where `p(n)` is odd.
Conjectured by Subbarao; Ono proved it for every progression containing at least one `n` with
`p(n)` odd, and Radu showed that every progression contains such an `n`. -/
@[category research solved, AMS 11]
theorem subbarao.odd : ∀ r t, 0 < t →
    {n : ℕ | n ≡ r [MOD t] ∧ Odd (partitionNumber n)}.Infinite := by
  sorry

/-- For every arithmetic progression `r (mod t)`, the number of `n ≤ X` with `n ≡ r (mod t)` and
`p(n)` even is `≫ √X`. (Ahlgren) -/
@[category research solved, AMS 11]
theorem ahlgren.even : ∀ r t, 0 < t →
    (fun X : ℝ ↦ √X) =O[atTop]
      fun X : ℝ ↦ ({n : ℕ | n ≤ X ∧ n ≡ r [MOD t] ∧ Even (partitionNumber n)}.ncard : ℝ) := by
  sorry

/-- For every arithmetic progression `r (mod t)`, the number of `n ≤ X` with `n ≡ r (mod t)` and
`p(n)` odd is `≫ √X / log X`. Ahlgren proved this for every progression containing at least one
`n` with `p(n)` odd; by Radu's theorem every progression does. -/
@[category research solved, AMS 11]
theorem ahlgren.odd : ∀ r t, 0 < t →
    (fun X : ℝ ↦ √X / X.log) =O[atTop]
      fun X : ℝ ↦ ({n : ℕ | n ≤ X ∧ n ≡ r [MOD t] ∧ Odd (partitionNumber n)}.ncard : ℝ) := by
  sorry

/-- The number of `n ≤ X` with `p(n)` even is `≫ √X log log X`. (Bellaïche–Nicolas) -/
@[category research solved, AMS 11]
theorem bellaiche_nicolas.even :
    (fun X : ℝ ↦ √X * X.log.log) =O[atTop]
      fun X : ℝ ↦ ({n : ℕ | n ≤ X ∧ Even (partitionNumber n)}.ncard : ℝ) := by
  sorry

/-- The number of `n ≤ x` with `p(n)` even is at least `0.069 √x log log x` for every `x > 1`.
(Bellaïche–Nicolas) -/
@[category research solved, AMS 11]
theorem bellaiche_nicolas.even_explicit : ∀ x : ℝ, 1 < x →
    0.069 * √x * x.log.log ≤ ({n : ℕ | n ≤ x ∧ Even (partitionNumber n)}.ncard : ℝ) := by
  sorry

/-- The number of `n ≤ x` with `p(n)` odd is at least `0.037 √x / (log x)^(7/8)` for every `x > 1`.
(Bellaïche–Nicolas) -/
@[category research solved, AMS 11]
theorem bellaiche_nicolas.odd_explicit : ∀ x : ℝ, 1 < x →
    0.037 * √x / (x.log) ^ (7 / 8 : ℝ) ≤ ({n : ℕ | n ≤ x ∧ Odd (partitionNumber n)}.ncard : ℝ) := by
  sorry

/-- The number of `n ≤ X` with `p(n)` odd is `≫ √X / log log X`.
(Bellaïche–Green–Soundararajan) -/
@[category research solved, AMS 11]
theorem bellaiche_green_soundararajan.odd :
    (fun X : ℝ ↦ √X / X.log.log) =O[atTop]
      fun X : ℝ ↦ ({n : ℕ | n ≤ X ∧ Odd (partitionNumber n)}.ncard : ℝ) := by
  sorry

/-- For square-free `D > 1` with `D ≡ 23 (mod 24)`, both parities occur infinitely often among
`p((D m² + 1) / 24)` as `m` ranges over the positive integers coprime to `6`. Note that
`24 ∣ D m² + 1` for such `m`. Conjectured by Ono and proved by Ono–Swaminathan. -/
@[category research solved, AMS 11]
theorem ono_swaminathan.quadratic : ∀ D : ℕ, 1 < D → Squarefree D → D % 24 = 23 →
    {m : ℕ | m.Coprime 6 ∧ Even (partitionNumber ((D * m ^ 2 + 1) / 24))}.Infinite ∧
    {m : ℕ | m.Coprime 6 ∧ Odd (partitionNumber ((D * m ^ 2 + 1) / 24))}.Infinite := by
  sorry

/-- The odd half of Theorem 1 of Ono–Swaminathan, with its effective bound: for square-free `D > 1`
with `D ≡ 23 (mod 24)` there is an `m` coprime to `6` with `m ≤ 12 h(-D) + 2` such that
`p((D m² + 1) / 24)` is odd, where `h(-D)` is the class number of `ℚ(√-D)`. Here `ℚ(√-D)` is
`AdjoinRoot (X ^ 2 + D)`, a number field since `X ^ 2 + D` is irreducible over `ℚ` for `D > 0`. -/
@[category research solved, AMS 11]
theorem ono_swaminathan.odd_bound (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24)) := by
  sorry

/-- Zheng's explicit lower bound: `liminf_{X → ∞} N_odd(X) / √X ≥ 243 / (64 √6 π⁵)`, where
`N_odd(X)` is the number of `n ≤ X` with `p(n)` odd. -/
@[category research solved, AMS 11,
  conditional formal_proof using lean4 at
    "https://github.com/AxiomMath/PartitionZheng/blob/9bfb4326c4ea1e00016a842d7cc145e5c4e0684a/Challenge/Basic.lean#L79"
    assuming ono_swaminathan.odd_bound]
theorem zheng.liminf :
    ((243 / (64 * √6 * π ^ 5) : ℝ) : EReal) ≤
      liminf (fun X : ℝ ↦
        ((({n : ℕ | n ≤ X ∧ Odd (partitionNumber n)}.ncard : ℝ) / √X : ℝ) : EReal)) atTop := by
  sorry

/-- The number of `n ≤ X` with `p(n)` odd is `≫ √X`. -/
@[category research solved, AMS 11]
theorem zheng.odd :
    (fun X : ℝ ↦ √X) =O[atTop]
      fun X : ℝ ↦ ({n : ℕ | n ≤ X ∧ Odd (partitionNumber n)}.ncard : ℝ) := by
  sorry

/-- Ono's conjecture: If `g` is a nonconstant integer-valued polynomial that is eventually
positive, then `p(g(n))` is even for infinitely many `n` and odd for infinitely many `n`. -/
@[category research open, AMS 11]
theorem ono.polynomial (g : ℚ[X]) (hg : 0 < g.natDegree)
    (hint : ∀ n : ℕ, ∃ k : ℤ, g.eval (n : ℚ) = k)
    (hpos : ∀ᶠ n : ℕ in atTop, 0 < g.eval (n : ℚ)) :
    {n : ℕ | Even (partitionNumber ⌊g.eval (n : ℚ)⌋₊)}.Infinite ∧
    {n : ℕ | Odd (partitionNumber ⌊g.eval (n : ℚ)⌋₊)}.Infinite := by
  sorry

end PartitionParity
