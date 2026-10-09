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
# Normality of Irrational Algebraic Numbers

It is unknown whether every irrational algebraic real number is normal in any integer base.
Here a real number is *normal in base* $b$ if, for every $k \ge 1$, every string of $k$ digits
appears in its base-$b$ expansion with asymptotic frequency $1/b^k$.
The stronger conjecture that every irrational algebraic real number is absolutely normal is stated
separately: normality in one base and normality in every base are not equivalent definitions.

In a 1950 note on the decimal digits of $\sqrt{2}$, Borel [Bor50] conjectured that every
irrational algebraic number is normal in every base. This was the first publication to address
the expansion of an irrational algebraic number [AB07].

A real number $x$ is normal in base $b$ if and only if the sequence $(b^n x)_{n \ge 0}$ is
uniformly distributed modulo $1$. This was proved by Wall [Wal49]; see also [Bug12, Theorem 4.14]
and [EvdPSW03, p. 127].

*References:*
- [Wikipedia: Normal number](https://en.wikipedia.org/wiki/Normal_number)
- [Bor50] Borel, Émile. "Sur les chiffres décimaux de $\sqrt{2}$ et divers problèmes de
  probabilités en chaîne." C. R. Acad. Sci. Paris 230 (1950): 591-593.
- [AB07] Adamczewski, Boris, and Yann Bugeaud. "On the complexity of algebraic numbers I.
  Expansions in integer bases." Annals of Mathematics 165.2 (2007): 547-565.
- [Wal49] Wall, Donald Dines. "Normal numbers." Ph.D. thesis, University of California, Berkeley,
  1949.
- [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
  Cambridge Tracts in Mathematics 193. Cambridge University Press, 2012.
- [EvdPSW03] Everest, Graham, Alf van der Poorten, Igor Shparlinski, and Thomas Ward.
  "Recurrence sequences." Mathematical Surveys and Monographs 104. American Mathematical
  Society, Providence, RI, 2003.
- [BC01] Bailey, David H., and Richard E. Crandall. "On the random character of fundamental constant
  expansions." Experimental Mathematics 10.2 (2001): 175-190.
  https://projecteuclid.org/journals/experimental-mathematics/volume-10/issue-2/On-the-random-character-of-fundamental-constant-expansions/em/999188630.full
-/

@[expose] public section

open NormalNumber

namespace AlgebraicNormality

/-- A real number is irrational algebraic if it is algebraic over `ℚ` but not rational. -/
def IsIrrationalAlgebraic (x : ℝ) : Prop :=
  IsAlgebraic ℚ x ∧ Irrational x

/-- A real number $x$ is normal in base $b$ if and only if $(b^n x)_{n \ge 0}$ is uniformly
distributed modulo $1$ [Wal49], [Bug12, Theorem 4.14]. -/
@[category research solved, AMS 11]
theorem isNormalInBase_iff_isEquidistributedModuloOne (b : ℕ) (hb : 2 ≤ b) (x : ℝ) :
    IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x := by
  sorry

/-- Borel's normality conjecture [Bor50]: every irrational algebraic real is absolutely normal. -/
@[category research open, AMS 11 12 41]
theorem irrational_algebraic_absolutely_normal :
    answer(sorry) ↔ ∀ x : ℝ, IsIrrationalAlgebraic x → IsAbsolutelyNormal x := by
  sorry

/-- The weaker normality conjecture: every irrational algebraic real is normal in at least one
integer base `b ≥ 2`. -/
@[category research open, AMS 11 12 41]
theorem irrational_algebraic_normal_in_some_base :
    answer(sorry) ↔
      ∀ x : ℝ, IsIrrationalAlgebraic x → ∃ b : ℕ, 2 ≤ b ∧ IsNormalInBase b x := by
  sorry

/-- Absolute normality implies normality in at least one base. -/
@[category API, AMS 11]
theorem normal_in_some_base_of_absolutely_normal {x : ℝ} (hx : IsAbsolutelyNormal x) :
    ∃ b : ℕ, 2 ≤ b ∧ IsNormalInBase b x :=
  ⟨2, le_rfl, hx 2 le_rfl⟩

end AlgebraicNormality
