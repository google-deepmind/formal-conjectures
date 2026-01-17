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
# Erdős Problem 978

*Reference:*
 - [erdosproblems.com/978](https://www.erdosproblems.com/978)
 - [Ho67] Hooley, C., On the power free values of polynomials. Mathematika (1967), 21--26.
 - [Br11] Browning, T. D., Power-free values of polynomials. Arch. Math. (Basel) (2011), 139--150.
 - [Er53] Erdős, P., Arithmetical properties of polynomials. J. London Math. Soc. (1953), 416--425.
-/

open Polynomial Set

namespace Erdos978

/-- Let `f ∈ ℤ[X]` be an irreducible polynomial. Suppose that the degree `k` of `f` is larger than
`2` and is not equal to a power of `2`. Also suppose that the leading coefficient of `f` is
positive. Then the set of `n` such that `f n` is `(k - 1)`-th power free is infinite, and this is
proved in [Er53]. -/
@[category research solved, AMS 11]
theorem erdos_978.sub_one {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree > 2)
    (hp : ¬ ∃ l : ℕ, f.natDegree = 2 ^ l) (hc : f.leadingCoeff > 0) :
    {n : ℕ | Powerfree (f.eval (n : ℤ)) (f.natDegree - 1)}.Infinite := by
  sorry

/-- Let `f ∈ ℤ[X]` be an irreducible polynomial. Suppose that the degree `k` of `f` is larger than
`2`, and `f n` have no fixed `(k - 1)`-th power divisors other than `1`. Also suppose that the
leading coefficient of `f` is positive. Then the set of `n` such that `f n` is `(k - 1)`-th power
free has positive density, and this is proved in [Ho67]. -/
@[category research solved, AMS 11]
theorem erdos_978.sub_one_density {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree > 2)
    (hp : ¬ ∃ p : ℕ, p.Prime ∧ ∀ n : ℕ, p ^ (f.natDegree - 1) ∣ (f.eval (n : ℤ)).toNat)
    (hc : f.leadingCoeff > 0) :
    HasPosDensity {n : ℕ | Powerfree (f.eval (n : ℤ)) (f.natDegree - 1)} := by
  sorry

/-- If the degree `k` of `f` is larger than or equal to `9`, then the set of `n` such that `f n` is
`(k - 2)`-th power free has infinitely many elements. This result is proved in [Br11]. -/
@[category research solved, AMS 11]
theorem erdos_978.sub_two {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree ≥ 9)
    (hp : ¬ ∃ p : ℕ, p.Prime ∧ ∀ n : ℕ, p ^ (f.natDegree - 2) ∣ (f.eval (n : ℤ)).toNat)
    (hc : f.leadingCoeff > 0) :
    {n : ℕ | Powerfree (f.eval (n : ℤ)) (f.natDegree - 2)}.Infinite := by
  sorry

/-- The set of `n` such that `f n` is `(k - 2)`-th power free has infinitely many elements. This
result is proved in [Br11]. -/
@[category research solved, AMS 11]
theorem erdos_978.sub_two' : answer(True) ↔ ∀ {f : ℤ[X]}, Irreducible f →
    f.natDegree > 2 → f.leadingCoeff > 0 →
    (¬ ∃ p : ℕ, p.Prime ∧ ∀ n : ℕ, p ^ (f.natDegree - 2) ∣ (f.eval (n : ℤ)).toNat) →
    {n : ℕ | Powerfree (f.eval (n : ℤ)) (f.natDegree - 2)}.Infinite := by
  sorry

/-- Does `n ^ 4 + 2` represent infinitely many squarefree numbers? -/
@[category research open, AMS 11]
theorem erdos_978.squarefree : answer(sorry) ↔ {n : ℕ | Squarefree (n ^ 4 + 2)}.Infinite := by
  sorry

end Erdos978
