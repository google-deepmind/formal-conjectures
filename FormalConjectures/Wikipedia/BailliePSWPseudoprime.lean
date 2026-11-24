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
# Composite Baillie–PSW pseudoprimes

The Baillie–PSW test (Baillie and Wagstaff 1980; Pomerance, Selfridge, and Wagstaff 1980)
certifies an odd non-square integer $n \ge 3$ as a probable prime when $n$ satisfies both the
base-$2$ strong Fermat criterion (OEIS A001262) and the strong Lucas criterion (OEIS A217255) for
$P = 1$ and $Q = (1 - D) / 4$, taking the earliest $D \in \{5, -7, 9, -11, 13, \dots\}$ with
Jacobi symbol $(D / n) = -1$ while rejecting $n$ if an earlier $D_i$ or $Q$ reveals a proper
divisor. Exhaustive computation rules out composite examples below $2^{64}$, whereas a heuristic
of Pomerance (1984) predicts infinitely many composite Baillie–PSW pseudoprimes.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Baillie%E2%80%93PSW_primality_test)
- [OEIS A001262](https://oeis.org/A001262)
- [OEIS A217255](https://oeis.org/A217255)
- R. Baillie and S. S. Wagstaff Jr., *Lucas pseudoprimes*, Math. Comp. **35** (1980), no. 152,
  1391–1417.
- C. Pomerance, J. L. Selfridge, and S. S. Wagstaff Jr., *The pseudoprimes to $25 \cdot 10^9$*,
  Math. Comp. **35** (1980), no. 151, 1003–1026.
- C. Pomerance, *Are there counterexamples to the Baillie–PSW primality test?*, unpublished
  manuscript (1984).
-/

@[expose] public section

namespace BailliePSWPseudoprime

/-- Selfridge's $j$-th candidate discriminant $D_j = (-1)^j (2j + 5) \in \{5, -7, 9, -11, \dots\}$
for $j \ge 0$. -/
def selfridgeD (j : ℕ) : ℤ :=
  (-1 : ℤ) ^ j * (2 * (j : ℤ) + 5)

/-- Strong Selfridge–Lucas probable prime predicate on an odd non-square integer $n \ge 3$:
at the least index $j$ with Jacobi symbol $(D_j / n) = -1$, every earlier $D_i$ ($i < j$) either
satisfies $(D_i / n) = 1$ or is divisible by $n$ (so $\gcd(|D_i|, n) \in \{1, n\}$),
$Q = (1 - D_j) / 4$ satisfies $\gcd(|Q|, n) = 1$, and for $n + 1 = 2^s d$ with $d$ odd either
$n \mid U_d(1, Q)$ or $n \mid V_{2^r d}(1, Q)$ for some $0 \le r < s$. -/
def IsStrongSelfridgeLucasPRP (n : ℕ) : Prop :=
  3 ≤ n ∧ Odd n ∧ ¬ IsSquare n ∧
    ∃ j : ℕ,
      jacobiSym (selfridgeD j) n = -1 ∧
      (∀ i < j, jacobiSym (selfridgeD i) n = 1 ∨ (n : ℤ) ∣ selfridgeD i) ∧
      Nat.Coprime ((1 - selfridgeD j) / 4).natAbs n ∧
      let Q := (1 - selfridgeD j) / 4
      ∃ s d : ℕ, Odd d ∧ n + 1 = 2 ^ s * d ∧
        ((n : ℤ) ∣ LucasSequence.U 1 Q d ∨
          ∃ r < s, (n : ℤ) ∣ LucasSequence.V 1 Q (2 ^ r * d))

/-- An integer $n$ is a composite Baillie–PSW pseudoprime when $n$ is composite and satisfies both
`IsStrongBaseTwoPRP` and `IsStrongSelfridgeLucasPRP`. -/
def IsBailliePSWPseudoprime (n : ℕ) : Prop :=
  n.Composite ∧ IsStrongBaseTwoPRP n ∧ IsStrongSelfridgeLucasPRP n

/-- Prime $n = 5$ passes `IsStrongSelfridgeLucasPRP` at $j = 1$ ($D_0 = 5$ is divisible by $5$,
$D_1 = -7$, $Q = 2$, $5 \mid V_3(1, 2) = -5$). -/
@[category test, AMS 11]
theorem isStrongSelfridgeLucasPRP_five : IsStrongSelfridgeLucasPRP 5 := by
  refine ⟨by omega, by decide, ?_, 1, by norm_num [selfridgeD], ?_, by norm_num [selfridgeD],
    1, 3, by decide, by omega, Or.inr ⟨0, by omega, by norm_num [selfridgeD, LucasSequence.V]⟩⟩
  · rintro ⟨k, hk⟩; have : k ≤ 2 := by nlinarith
    interval_cases k <;> omega
  · intro i hi; interval_cases i; exact Or.inr (by norm_num [selfridgeD])

/-- Prime $n = 7$ passes `IsStrongBaseTwoPRP`. -/
@[category test, AMS 11]
theorem isStrongBaseTwoPRP_seven : IsStrongBaseTwoPRP 7 :=
  ⟨by omega, by decide, 1, 3, by decide, by omega, Or.inl (by decide)⟩

/-- Prime $n = 7$ passes `IsStrongSelfridgeLucasPRP` at $j = 0$ ($D_0 = 5$). -/
@[category test, AMS 11]
theorem isStrongSelfridgeLucasPRP_seven : IsStrongSelfridgeLucasPRP 7 := by
  refine ⟨by omega, by decide, ?_, 0, by norm_num [selfridgeD], by intro i hi; omega,
    by norm_num [selfridgeD], 3, 1, by decide, by omega,
    Or.inr ⟨2, by omega, by norm_num [selfridgeD, LucasSequence.V]⟩⟩
  rintro ⟨k, hk⟩; have : k ≤ 2 := by nlinarith
  interval_cases k <;> omega

/-- Prime $n = 7$ is not a composite Baillie–PSW pseudoprime. -/
@[category test, AMS 11]
theorem not_isBailliePSWPseudoprime_seven : ¬ IsBailliePSWPseudoprime 7 :=
  fun ⟨h, _, _⟩ => h.2 (by decide)

/-- Composite $n = 9$ fails `IsStrongBaseTwoPRP`. -/
@[category test, AMS 11]
theorem not_isStrongBaseTwoPRP_nine : ¬ IsStrongBaseTwoPRP 9 := by
  rintro ⟨_, _, s, d, ⟨k, rfl⟩, hsd, h9⟩
  have hs3 : s ≤ 3 := Nat.le_of_not_lt fun hgt => by
    have := Nat.pow_le_pow_right (by omega : 0 < 2) hgt; nlinarith
  interval_cases s <;> try omega
  have hk0 : k = 0 := by omega
  subst hk0
  rcases h9 with h1 | ⟨r, hr, h2⟩
  · revert h1; decide
  · interval_cases r <;> (revert h2; decide)

/-- Evaluates the first four Selfridge discriminants $(5, -7, 9, -11)$. -/
@[category test, AMS 11]
theorem selfridgeD_small_values :
    [selfridgeD 0, selfridgeD 1, selfridgeD 2, selfridgeD 3] = [5, -7, 9, -11] := by
  decide

/-- Evaluates the first four Lucas pairs $(U_k(1, -1), V_k(1, -1))$ for $0 \le k \le 3$. -/
@[category test, AMS 11]
theorem lucas_small_values :
    [(LucasSequence.U 1 (-1) 0, LucasSequence.V 1 (-1) 0),
      (LucasSequence.U 1 (-1) 1, LucasSequence.V 1 (-1) 1),
      (LucasSequence.U 1 (-1) 2, LucasSequence.V 1 (-1) 2),
      (LucasSequence.U 1 (-1) 3, LucasSequence.V 1 (-1) 3)] =
      [(0, 2), (1, 1), (1, 3), (2, 4)] := by
  decide

/-- Every Baillie–PSW pseudoprime satisfies $3 \le n$. -/
@[category API, AMS 11]
theorem three_le_of_isBailliePSWPseudoprime {n : ℕ} (h : IsBailliePSWPseudoprime n) : 3 ≤ n :=
  h.2.1.1

/-- Every Baillie–PSW pseudoprime is odd. -/
@[category API, AMS 11]
theorem odd_of_isBailliePSWPseudoprime {n : ℕ} (h : IsBailliePSWPseudoprime n) : Odd n :=
  h.2.1.2.1

/-- No Baillie–PSW pseudoprime is a perfect square. -/
@[category API, AMS 11]
theorem not_isSquare_of_isBailliePSWPseudoprime {n : ℕ} (h : IsBailliePSWPseudoprime n) :
    ¬ IsSquare n :=
  h.2.2.2.2.1

/-- No integer $n < 3$ is a Baillie–PSW pseudoprime. -/
@[category API, AMS 11]
theorem not_isBailliePSWPseudoprime_of_lt_three {n : ℕ} (hn : n < 3) :
    ¬ IsBailliePSWPseudoprime n :=
  fun h => Nat.not_lt.mpr h.2.1.1 hn

/--
Does there exist a composite Baillie–PSW pseudoprime?
-/
@[category research open, question, AMS 11]
theorem exists_baillie_psw_pseudoprime :
    ∃ n : ℕ, IsBailliePSWPseudoprime n := by
  sorry

/--
Pomerance (1984) conjectured that infinitely many composite Baillie–PSW pseudoprimes exist.
-/
@[category research open, AMS 11]
theorem exists_baillie_psw_pseudoprime.variants.infinite :
    {n : ℕ | IsBailliePSWPseudoprime n}.Infinite := by
  sorry

end BailliePSWPseudoprime
