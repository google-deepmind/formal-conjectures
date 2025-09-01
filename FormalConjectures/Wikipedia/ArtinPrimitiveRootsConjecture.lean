/-
Copyright 2025 The Formal Conjectures Authors.

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
# Artin's conjecture on primitive roots

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Artin%27s_conjecture_on_primitive_roots)
-/

open scoped Topology Nat

namespace ArtinPrimitiveRootsConjecture

/--Let `S(a)` be the set of primes such that `a` is a primitive root modulo `p`-/
private abbrev S (a : ℤ) : Set ℕ :=
  {p : ℕ | p.Prime ∧ orderOf (a : ZMod p) = (p-1 : ℕ)}

/--
**Artin's Constant** is defined to be the product
`∏_{p prime}, (1 - 1/(p*(p-1)))`
-/
private noncomputable def ArtinConstant : ℝ :=
  ∏' p : {n : ℕ // n.Prime}, (1 - 1 / (p*(p-1)) : ℝ)

/--
**Artin's Conjecture on Primitive Roots**, first half.
Let a be an integer that is not a square number and not −1. Then the set `S(a)`
of primes `p` such that `a` is a primitive root modulo `p` has a positive asymptotic
density inside the set of primes. In particular, `S(a)` is infinite.
-/
@[category research open, AMS 11]
theorem artin_primitive_roots.parts.i (a : ℤ)
    (ha : ¬ IsSquare a) (ha' : a ≠ -1) :
    ∃ x > 0, (S a).HasDensity x {p | p.Prime} := by
  sorry

/--
**Artin's Conjecture on Primitive Roots**, second half.
Write `a = a_0 b^2` where `a_0` is squarefree. Under the conditions that `a` is not a perfect power and `a_0` is not congruent to `1` modulo `4`
(sequence A085397 in the OEIS), the density of the set `S(a)` of primes `p` such that `a` is a primitive root modulo `p`
is independent of `a` and equals Artin's constant,
-/
@[category research open, AMS 11]
theorem artin_primitive_roots.parts.ii
    (a a_0 b : ℤ) (ha : a = a_0 * b^2)
    (ha' : ∀ n m, m ≠ 1 → a ≠ n^m) (ha_0 : Squarefree a_0)
    (ha_0' : ¬ a_0 ≡ 1 [ZMOD 4]):
    (S a).HasDensity ArtinConstant {p | p.Prime} := by
  sorry

/--
**Artin's Conjecture on Primitive Roots**, second half, different residue version
If `a` is a square number or `a = −1`, then the density of the set `S(a)` of primes `p` such that `a` is a primitive root modulo `p` is `0`.
-/
@[category research solved, AMS 11] --Note: this is too easy to still be open!
--See https://math.stackexchange.com/questions/2780014/prove-that-a-perfect-square-is-not-a-primitive-root-modulo-p-for-any-prime-p
theorem artin_primitive_roots.variants.part_ii_square_or_minus_one
    (a : ℤ) (ha : IsSquare a ∨ a = -1) :
    (S a).HasDensity 0 {p | p.Prime} := by
  sorry

/--
**Artin's Conjecture on Primitive Roots**, second half, power version
If `a` is a perfect pth power for prime `p`, then the density of the set `S(a)` of
primes `p` such that `a` is a primitive root modulo `p`
is given by `p(p-2) / (p^2 - p - 1) * C` where `C` is Artin's constant. If there are
more than one such prime `p`, then the number needs to be multiplied by
``p(p-2) / (p^2 - p - 1)` for all such primes `p`.
-/
@[category research open, AMS 11]
theorem artin_primitive_roots.variants.part_ii_prime_power
    (a m b : ℕ) (ha : a = b^m) (hb : ∀ u v, 1 < u → b ≠ v^u) (hm₁ : 1 < m)
    (hm₂ : m.primeFactorsList.Nodup)  :
    (S a).HasDensity
      (ArtinConstant * ∏ p ∈ m.primeFactors, p * (p-2 : ℝ) / (p^2 - p - 1))
      {p | p.Prime} := by
  sorry

/--
**Artin's Conjecture on Primitive Roots**, second half, perfect prime power version
Write `a = a_0 b^2` where `a_0` is squarefree.
If `a_0` is congruent to `1 mod 4`, then the density of the set `S(a)` of primes `p` such that `a` is a primitive root modulo `p`
is given by `C * ∏_p, p(p-1) / (p^2 - p - 1)` where `C` is Artin's constant and the product is taken over the prime factors `p` of `a_0`
-/
@[category research open, AMS 11]
theorem artin_primitive_roots.variants.part_ii
    (a a_0 b : ℕ) (ha : a = a_0 * b^2) (ha' : ∀ n m, m ≠ 1 → a ≠ n^m)
    (ha' : Squarefree a) (ha_0' : a_0 ≡ 1 [MOD 4]):
    (S a).HasDensity
      (ArtinConstant * ∏ p ∈ a_0.primeFactors, p * (p-1 : ℝ) / (p^2 - p - 1))
      {p | p.Prime} := by
  sorry

end ArtinPrimitiveRootsConjecture
