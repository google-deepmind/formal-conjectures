import FormalConjectures.Util.ProblemImports

/-!
# Conjecture relating two characterizations of a set of integers.

Informal Statement:
For an integer k ≥ 2, the following are equivalent:

(1) The greatest common divisor of the binomial coefficients
    C(2k,k), C(3k,k),.....,C((k+1)k,k) is equal to 1.

(2) Writing prime factorization of k as 
    k = ∏ pᵢ^{eᵢ}, and let
    P = max pᵢ^{eᵢ},
    one has k / P > P.

This conjecture asserts that the integers satisfying (1)
are exactly those satisfying (2).

*Reference:* 
- [A080170](https://oeis.org/A080170)
- [A051283](https://oeis.org/A051283)
-/

namespace OeisA080170

/-- 
List of binomial coefficients: C(2k,k), C(3k,k), ..., C((k+1)k,k) 
-/
def binom_sequence (k : ℕ) : List ℕ :=
  (List.range k).map (fun i => Nat.choose ((i + 2) * k) k)

/-- 
Condition: gcd of the binomial sequence is 1 
-/
def gcd_condition (k : ℕ) : Prop :=
  (binom_sequence k).foldr Nat.gcd 0 = 1

/-- 
Maximum prime power in the factorization of k 
-/
def max_prime_power (k : ℕ) : ℕ :=
  k.factorization.sup (fun p e => p ^ e)

/-- 
Condition: k divided by the maximum prime power is greater than the max prime power 
-/
def max_prime_condition (k : ℕ) : Prop :=
  k / max_prime_power k > max_prime_power k

/-- 
Conjecture: The gcd condition is equivalent to the max prime power condition
-/
@[category research open, AMS 11]
conjecture A080170_A051283_equiv (k : ℕ) (hk : 2 ≤ k) : 
  gcd_condition k ↔ max_prime_condition k


end OeisA080170