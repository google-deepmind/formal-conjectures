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
# Higgs Primes

Fix an exponent $a \ge 1$. Starting from $Hp_1 = 2$, Denis Higgs defined $Hp_{k+1}$ recursively as
the minimal prime $q > Hp_k$ whose totient $\varphi(q)$ divides $\prod_{i=1}^k Hp_i^a$. At $a = 1$,
this greedy construction stops at $[2, 3, 7, 43]$. Whether any exponent $a \ge 2$—in particular
$a = 2$ (`A007459`, studied by Burris and Lee in 1993)—yields an infinite sequence remains open.

*References:*
- [Wikipedia: Higgs prime](https://en.wikipedia.org/wiki/Higgs_prime)
- [OEIS A007459](https://oeis.org/A007459)
- S. Burris and S. Lee, *Tarski's high school identities*, Amer. Math. Monthly **100** (1993),
  no. 3, 231–236.
-/

@[expose] public section

namespace HiggsPrime

/-- Predicate asserting that $p$ is the least prime above every entry of `L` whose Euler totient
`p.totient` divides `L.prod ^ a`. -/
def IsNextGreedyHiggsPrime (a : ℕ) (L : List ℕ) (p : ℕ) : Prop :=
  IsLeast {q : ℕ | q.Prime ∧ (∀ r ∈ L, r < q) ∧ q.totient ∣ L.prod ^ a} p

/-- Finite prefixes of the Higgs prime sequence for exponent $a$, starting at $[2]$. -/
inductive IsGreedyHiggsPrefix (a : ℕ) : List ℕ → Prop
  | single : IsGreedyHiggsPrefix a [2]
  | snoc {L : List ℕ} {p : ℕ} :
      IsGreedyHiggsPrefix a L → IsNextGreedyHiggsPrime a L p →
      IsGreedyHiggsPrefix a (L ++ [p])

/-- At $a = 1$, $3$ is the next term after $[2]$. -/
@[category test, AMS 11]
theorem isNextGreedyHiggsPrime_one_two_three :
    IsNextGreedyHiggsPrime 1 [2] 3 := by
  refine ⟨⟨by decide, ?_, by decide⟩, ?_⟩
  · intro r hr
    simp at hr
    omega
  · rintro q ⟨_, hgt, _⟩
    have := hgt 2 (by simp)
    omega

/-- At $a = 2$, $[2, 3, 5]$ is a valid prefix. -/
@[category test, AMS 11]
theorem isGreedyHiggsPrefix_two_two_three_five :
    IsGreedyHiggsPrefix 2 [2, 3, 5] := by
  have h23 : IsGreedyHiggsPrefix 2 [2, 3] := by
    refine IsGreedyHiggsPrefix.snoc IsGreedyHiggsPrefix.single ⟨⟨by decide, ?_, by decide⟩, ?_⟩
    · intro r hr; simp at hr; omega
    · rintro q ⟨_, hgt, _⟩
      have := hgt 2 (by simp)
      omega
  refine IsGreedyHiggsPrefix.snoc h23 ⟨⟨by decide, ?_, by decide⟩, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> omega
  · rintro q ⟨hq, hgt, _⟩
    have h3 : 3 < q := hgt 3 (by simp)
    by_contra hlt
    have hq4 : q = 4 := by omega
    subst hq4
    exact absurd hq (by decide)

/-- At $a = 1$, $[2, 3, 7, 43]$ is a valid Higgs prime prefix. -/
@[category test, AMS 11]
theorem isGreedyHiggsPrefix_one_full : IsGreedyHiggsPrefix 1 [2, 3, 7, 43] := by
  have h23 : IsGreedyHiggsPrefix 1 [2, 3] :=
    IsGreedyHiggsPrefix.snoc IsGreedyHiggsPrefix.single isNextGreedyHiggsPrime_one_two_three
  have h237 : IsGreedyHiggsPrefix 1 [2, 3, 7] := by
    refine IsGreedyHiggsPrefix.snoc h23 ⟨⟨by decide, fun r hr => by simp at hr; omega, by decide⟩,
      fun q ⟨hq, hgt, hdvd⟩ => ?_⟩
    have := hgt 3 (by simp); by_contra hlt
    interval_cases q <;> exact absurd (And.intro hq hdvd) (by decide)
  refine IsGreedyHiggsPrefix.snoc h237 ⟨⟨by decide, fun r hr => by simp at hr; omega, by decide⟩,
    fun q ⟨hq, hgt, hdvd⟩ => ?_⟩
  have := hgt 7 (by simp); by_contra hlt
  interval_cases q <;> exact absurd (And.intro hq hdvd) (by decide)

/-- At $a = 1$, $[2, 3, 7, 43]$ is a valid prefix and admits no prime extension. -/
@[category textbook, AMS 11]
theorem higgs_primes_exponent_one_terminates :
    IsGreedyHiggsPrefix 1 [2, 3, 7, 43] ∧
      ¬ ∃ p : ℕ, IsNextGreedyHiggsPrime 1 [2, 3, 7, 43] p := by
  refine ⟨isGreedyHiggsPrefix_one_full, ?_⟩
  have hdiv : ∀ k ∈ Finset.Icc 1 42, 1806 % k = 0 →
      k ∈ ([1, 2, 3, 6, 7, 14, 21, 42] : List ℕ) := by decide
  rintro ⟨p, ⟨hp, hgt, hdvd⟩, _⟩
  have h43 : 43 ≤ p - 1 := by have := hgt 43 (by simp); omega
  obtain ⟨k, hk⟩ : (p - 1) ∣ 1806 := by simpa [Nat.totient_prime hp] using hdvd
  have hk_list := hdiv k (Finset.mem_Icc.mpr ⟨by nlinarith, by nlinarith⟩)
    (Nat.mod_eq_zero_of_dvd ⟨p - 1, by linarith⟩)
  have hp_eq : p = 1806 / k + 1 := by
    have : 1806 / k = p - 1 := by rw [hk, Nat.mul_div_cancel _ (by nlinarith)]
    omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk_list
  rcases hk_list with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (rw [hp_eq] at hp; norm_num at hp)

/-- Does exponent $a = 2$ admit Higgs prime prefixes of every positive length? -/
@[category research open, question, AMS 11]
theorem higgs_primes_squares_infinite :
    ∀ k : ℕ, 1 ≤ k → ∃ L : List ℕ, L.length = k ∧ IsGreedyHiggsPrefix 2 L := by
  sorry

/-- Does there exist at least one integer exponent $a \ge 2$ admitting arbitrarily long Higgs prime
prefixes? -/
@[category research open, question, AMS 11]
theorem higgs_primes_exists_higher_exponent_infinite :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ k : ℕ, 1 ≤ k → ∃ L : List ℕ, L.length = k ∧ IsGreedyHiggsPrefix a L := by
  sorry

/-- Stronger universal variant: does every integer exponent $a \ge 2$ admit arbitrarily long Higgs
prime prefixes? -/
@[category research open, question, AMS 11]
theorem higgs_primes_squares_infinite.variants.all_higher_exponents :
    ∀ a : ℕ, 2 ≤ a → ∀ k : ℕ, 1 ≤ k → ∃ L : List ℕ, L.length = k ∧ IsGreedyHiggsPrefix a L := by
  sorry

end HiggsPrime
