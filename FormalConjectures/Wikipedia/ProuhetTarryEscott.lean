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
# Ideal Prouhet–Tarry–Escott Multisets

Given $n, k \ge 1$, two disjoint $n$-element integer multisets $A$ and $B$ form an equal-power-sum
pair of degree $k$ when $\sum_{a \in A} a^i = \sum_{b \in B} b^i$ holds for $1 \le i \le k$. Any
nonempty pair satisfies $n \ge k + 1$, and pairs achieving $n = k + 1$ are termed *ideal*.
Wikipedia lists known nontrivial ideal pairs for $3 \le n \le 10$ ($2 \le k \le 9$, omitting
trivial $n = 2$) and $n = 12$ ($k = 11$), and notes that none is known for $n = 11$ ($k = 10$) or
$n \ge 13$ ($k \ge 12$); Borwein (2002) and Wright (Hardy and Wright 2008) conjecture that ideal
pairs exist for every degree $k \ge 1$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Prouhet%E2%80%93Tarry%E2%80%93Escott_problem)
- E. M. Wright, *Prouhet's 1851 solution of the Tarry–Escott problem of 1910*, The American
  Mathematical Monthly **66** (1959), 199–201.
- P. Borwein, *Computational Excursions in Analysis and Number Theory*, CMS Books in Mathematics,
  Springer, 2002, Chapter 11, pp. 85–96.
- G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, 6th ed., Oxford
  University Press, 2008, Section 21.9.
-/

@[expose] public section

namespace ProuhetTarryEscott

/-- Two integer multisets $A$ and $B$ form a Prouhet–Tarry–Escott solution of size $n$ and degree
$k$ if they are disjoint, each has cardinality $n$, and $\sum_{a \in A} a^i = \sum_{b \in B} b^i$
for every $1 \le i \le k$. -/
def IsPTESolution (n k : ℕ) (A B : Multiset ℤ) : Prop :=
  Disjoint A B ∧
    A.card = n ∧
    B.card = n ∧
    ∀ i ∈ Finset.Icc 1 k, (A.map (· ^ i)).sum = (B.map (· ^ i)).sum

/-- An ideal Prouhet–Tarry–Escott solution of degree $k$ is a solution of size $n = k + 1$ and
degree $k$. -/
def IsIdealPTESolution (k : ℕ) (A B : Multiset ℤ) : Prop :=
  IsPTESolution (k + 1) k A B

/-- Integers in $\{0, \dots, 2^{k+1} - 1\}$ with an even binary digit sum (Thue–Morse class $0$). -/
def prouhetEven (k : ℕ) : Multiset ℤ :=
  (((Finset.range (2 ^ (k + 1))).filter fun m => Even (Nat.digits 2 m).sum).val).map Int.ofNat

/-- Integers in $\{0, \dots, 2^{k+1} - 1\}$ with an odd binary digit sum (Thue–Morse class $1$). -/
def prouhetOdd (k : ℕ) : Multiset ℤ :=
  (((Finset.range (2 ^ (k + 1))).filter fun m => Odd (Nat.digits 2 m).sum).val).map Int.ofNat

instance instDecidableIsPTESolution (n k : ℕ) (A B : Multiset ℤ) :
    Decidable (IsPTESolution n k A B) :=
  decidable_of_iff
    ((∀ a ∈ A, a ∉ B) ∧
      A.card = n ∧
      B.card = n ∧
      ∀ i ∈ Finset.Icc 1 k, (A.map (· ^ i)).sum = (B.map (· ^ i)).sum)
    ⟨fun ⟨hd, hA, hB, hs⟩ => ⟨Multiset.disjoint_left.mpr fun {a} ha => hd a ha, hA, hB, hs⟩,
     fun ⟨hd, hA, hB, hs⟩ => ⟨fun _ ha => Multiset.disjoint_left.mp hd ha, hA, hB, hs⟩⟩

instance instDecidableIsIdealPTESolution (k : ℕ) (A B : Multiset ℤ) :
    Decidable (IsIdealPTESolution k A B) := by
  unfold IsIdealPTESolution
  infer_instance

/-- `IsPTESolution n k` is symmetric in the two multisets. -/
@[category API, AMS 11]
theorem IsPTESolution.symm {n k : ℕ} {A B : Multiset ℤ} (h : IsPTESolution n k A B) :
    IsPTESolution n k B A :=
  ⟨h.1.symm, h.2.1.symm ▸ h.2.2.1, h.2.1, fun i hi => (h.2.2.2 i hi).symm⟩

/-- No multiset can form an ideal Prouhet–Tarry–Escott solution with itself because its size
$k + 1$ is positive, violating disjointness. -/
@[category API, AMS 11]
theorem not_isIdealPTESolution_self (k : ℕ) (A : Multiset ℤ) :
    ¬ IsIdealPTESolution k A A := by
  rintro ⟨hdisj, hcard, -, -⟩
  have hne : A ≠ 0 := by
    intro h0
    rw [h0, Multiset.card_zero] at hcard
    omega
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
  exact Multiset.disjoint_left.mp hdisj hx hx

/-- The multisets $\{0, 5, 6, 16, 17, 22\}$ and $\{1, 2, 10, 12, 20, 21\}$ form an ideal solution of
degree $k = 5$ (size $n = 6$). -/
@[category test, AMS 11]
theorem isIdealPTESolution_five_example :
    IsIdealPTESolution 5 ({0, 5, 6, 16, 17, 22} : Multiset ℤ)
      ({1, 2, 10, 12, 20, 21} : Multiset ℤ) := by
  decide

/-- At $k = 3$, Prouhet's Thue–Morse partition (`prouhetEven 3` and `prouhetOdd 3`, namely
$\{0, 3, 5, 6, 9, 10, 12, 15\}$ and $\{1, 2, 4, 7, 8, 11, 13, 14\}$) forms a solution of size
$n = 8$ and degree $k = 3$. -/
@[category test, AMS 11]
theorem isPTESolution_prouhet_three :
    IsPTESolution 8 3 (prouhetEven 3) (prouhetOdd 3) := by
  decide

/--
For any nonempty Prouhet–Tarry–Escott solution of size $n \ge 1$ and degree $k$, the size strictly
exceeds the degree ($k < n$). The hypothesis $1 \le n$ excludes the empty multiset pair $A = B = 0$
at $n = 0$, which satisfies `IsPTESolution 0 k 0 0` for every $k$.
-/
@[category textbook, AMS 11]
theorem card_gt_degree_of_isPTESolution {n k : ℕ} {A B : Multiset ℤ} (hn : 1 ≤ n)
    (h : IsPTESolution n k A B) : k < n := by
  sorry

/--
Prouhet (1851; see Wright 1959) proved that for every $k \ge 1$, partitioning
$\{0, \dots, 2^{k+1} - 1\}$ into `prouhetEven k` and `prouhetOdd k` by binary digit-sum parity
yields a Prouhet–Tarry–Escott solution of size $n = 2^k$ and degree $k$.
-/
@[category research solved, AMS 11]
theorem prouhet_two_pow_solution (k : ℕ) (hk : 1 ≤ k) :
    IsPTESolution (2 ^ k) k (prouhetEven k) (prouhetOdd k) := by
  sorry

/--
Explicit ideal Prouhet–Tarry–Escott pairs exist for degrees $1 \le k \le 9$ ($2 \le n \le 10$) and
$k = 11$ ($n = 12$, found by Kuosa, Meyrignac, and Shuwen in 1999).
-/
@[category research solved, AMS 11]
theorem known_ideal_prouhet_tarry_escott :
    ∀ k ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 11} : Finset ℕ),
      ∃ A B : Multiset ℤ, IsIdealPTESolution k A B := by
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨{0, 2}, {1, 1}, by decide⟩
  · exact ⟨{0, 4, 5}, {1, 2, 6}, by decide⟩
  · exact ⟨{0, 4, 7, 11}, {1, 2, 9, 10}, by decide⟩
  · exact ⟨{1, 5, 9, -8, -7}, {-1, -5, -9, 8, 7}, by decide⟩
  · exact ⟨{0, 5, 6, 16, 17, 22}, {1, 2, 10, 12, 20, 21}, by decide⟩
  · exact ⟨{7, 13, 38, 50, -24, -33, -51}, {-7, -13, -38, -50, 24, 33, 51}, by decide⟩
  · exact ⟨{-24, -23, -14, -5, 5, 14, 23, 24}, {-25, -21, -16, -2, 2, 16, 21, 25}, by decide⟩
  · exact ⟨{-98, -82, -58, -34, 13, 16, 69, 75, 99},
      {98, 82, 58, 34, -13, -16, -69, -75, -99}, by decide⟩
  · exact ⟨{-313, -301, -188, -100, -99, 99, 100, 188, 301, 313},
      {-308, -307, -180, -131, -71, 71, 131, 180, 307, 308}, by decide⟩
  · exact ⟨{-151, -140, -127, -86, -61, -22, 22, 61, 86, 127, 140, 151},
      {-148, -146, -121, -94, -47, -35, 35, 47, 94, 121, 146, 148}, by decide⟩

/--
Ideal **Prouhet–Tarry–Escott conjecture** (Borwein 2002, Chapter 11, p. 85, Conjecture 1; Hardy and
Wright 2008, Section 21.9): an ideal solution of degree $k$ (size $n = k + 1$) exists for every
integer $k \ge 1$. Wikipedia records that $n = 11$ ($k = 10$) and $n \ge 13$ ($k \ge 12$) remain
without known ideal pairs.
-/
@[category research open, AMS 11]
theorem ideal_prouhet_tarry_escott_conjecture (k : ℕ) (hk : 1 ≤ k) :
    ∃ A B : Multiset ℤ, IsIdealPTESolution k A B := by
  sorry

/--
Smallest unresolved case highlighted on Wikipedia ($n = 11$, $k = 10$; Borwein 2002, p. 85): there
exists an ideal solution of degree $10$ consisting of two disjoint multisets of $11$ integers.
-/
@[category research open, AMS 11]
theorem ideal_prouhet_tarry_escott_conjecture.variants.degree_ten :
    ∃ A B : Multiset ℤ, IsIdealPTESolution 10 A B := by
  sorry

end ProuhetTarryEscott
