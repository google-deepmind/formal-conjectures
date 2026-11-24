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
# Waring's Problem and the Ideal Waring Formula

For $k \ge 1$, Waring's invariant $g(k)$ is the minimum order $s$ at which nonnegative $k$-th
powers form an additive basis of $\mathbb{N}$, and $G(k)$ is the minimum order $s$ at which they
form an asymptotic additive basis. J. A. Euler (c. 1772) proved the lower bound
$g(k) \ge 2^k + \lfloor (3/2)^k \rfloor - 2$, and equality is conjectured for every $k \ge 1$
(OEIS A002804).

*References:*
- [Wikipedia: Waring's problem](https://en.wikipedia.org/wiki/Waring%27s_problem)
- [OEIS: A002804](https://oeis.org/A002804)
- D. Hilbert, *Beweis für die Darstellbarkeit der ganzen Zahlen durch eine feste Anzahl $n$-ter
  Potenzen (Waringsches Problem)*, Mathematische Annalen **67** (1909), no. 3, 281–300.
- L. E. Dickson, *Solution of Waring's Problem*, American Journal of Mathematics **58** (1936),
  no. 3, 530–535.
- S. S. Pillai, *On Waring's Problem*, Journal of the Indian Mathematical Society **2** (1936),
  16–44.
- H. Davenport, *On Waring's Problem for Fourth Powers*, Annals of Mathematics **40** (1939),
  no. 4, 731–747.
- I. M. Niven, *An unsolved case of the Waring problem*, American Journal of Mathematics **66**
  (1944), no. 1, 137–143.
- K. Mahler, *On the fractional parts of the powers of a rational number II*, Mathematika **4**
  (1957), no. 2, 122–124.
- M. B. Nathanson, *Additive Number Theory: The Classical Bases*, Graduate Texts in Mathematics
  **164**, Springer, 1996, p. 71.
-/

@[expose] public section

namespace WaringProblem

/-- The set $\{m^k : m \in \mathbb{N}\}$ of nonnegative $k$-th powers. -/
def kthPowers (k : ℕ) : Set ℕ :=
  Set.range (· ^ k)

/-- Waring's invariant $g(k)$, the least $s$ for which `kthPowers k` forms an order-$s$ additive
basis of $\mathbb{N}$. For $k \ge 1$, $0 = 0^k \in \mathrm{kthPowers}\,k$, so exact $s$-term sums
agree with sums of $\le s$ $k$-th powers. -/
noncomputable def waringG (k : ℕ) : ℕ :=
  sInf {s : ℕ | (kthPowers k).IsAddBasisOfOrder s}

/-- Waring's invariant $G(k)$, the least $s$ for which `kthPowers k` forms an order-$s$ asymptotic
additive basis of $\mathbb{N}$. For $k \ge 1$, $0 = 0^k \in \mathrm{kthPowers}\,k$, so exact
$s$-term sums agree with sums of $\le s$ positive $k$-th powers on large integers. -/
noncomputable def waringBigG (k : ℕ) : ℕ :=
  sInf {s : ℕ | (kthPowers k).IsAsymptoticAddBasisOfOrder s}

/-- J. A. Euler's formula $2^k + \lfloor (3/2)^k \rfloor - 2$ for $g(k)$ (OEIS A002804). -/
def eulerWaringBound (k : ℕ) : ℕ :=
  2 ^ k + 3 ^ k / 2 ^ k - 2

/-- For $k = 1$, every natural number is a single first power, so $g(1) = 1$. -/
@[category test, AMS 11]
theorem waringG_one : waringG 1 = 1 := by
  have h1 : (kthPowers 1).IsAddBasisOfOrder 1 := by
    rw [Set.isAddBasisOfOrder_iff]
    intro n
    exact ⟨fun _ => n, fun _ => ⟨n, pow_one n⟩, by simp⟩
  refine le_antisymm (Nat.sInf_le h1) (le_csInf ⟨1, h1⟩ fun s hs => ?_)
  dsimp at hs
  by_contra! hlt
  have hs0 : s = 0 := by omega
  rw [hs0] at hs
  exact Set.not_isAddBasisOfOrder_zero hs

/-- Three natural-number squares never add up to $7$, so squares do not form an order-$3$ additive
basis. -/
@[category test, AMS 11]
theorem not_squares_isAddBasisOfOrder_three : ¬ (kthPowers 2).IsAddBasisOfOrder 3 := by
  rw [Set.isAddBasisOfOrder_iff]
  intro h
  obtain ⟨f, hf, hsum⟩ := h 7
  choose x hx using hf
  rw [Fin.sum_univ_three, ← hx 0, ← hx 1, ← hx 2] at hsum
  have h0 : x 0 < 3 := by nlinarith
  have h1 : x 1 < 3 := by nlinarith
  have h2 : x 2 < 3 := by nlinarith
  have hfin : ∀ a b c : Fin 3, a.1 ^ 2 + b.1 ^ 2 + c.1 ^ 2 ≠ 7 := by decide
  exact hfin ⟨x 0, h0⟩ ⟨x 1, h1⟩ ⟨x 2, h2⟩ hsum

/-- Evaluates `eulerWaringBound 1 = 1` (OEIS A002804). -/
@[category test, AMS 11]
theorem eulerWaringBound_one : eulerWaringBound 1 = 1 := by decide

/-- Evaluates `eulerWaringBound 2 = 4` (OEIS A002804). -/
@[category test, AMS 11]
theorem eulerWaringBound_two : eulerWaringBound 2 = 4 := by decide

/-- Evaluates `eulerWaringBound 3 = 9` (OEIS A002804). -/
@[category test, AMS 11]
theorem eulerWaringBound_three : eulerWaringBound 3 = 9 := by decide

/-- Evaluates `eulerWaringBound 4 = 19` (OEIS A002804). -/
@[category test, AMS 11]
theorem eulerWaringBound_four : eulerWaringBound 4 = 19 := by decide

/-- Evaluates `eulerWaringBound 5 = 37` (OEIS A002804). -/
@[category test, AMS 11]
theorem eulerWaringBound_five : eulerWaringBound 5 = 37 := by decide

/-- Lagrange's four-square theorem (`Nat.sum_four_squares`) together with the obstruction $7$ gives
$g(2) = 4$. -/
@[category textbook, AMS 11]
theorem waringG_two : waringG 2 = 4 := by
  have h4 : (kthPowers 2).IsAddBasisOfOrder 4 := by
    rw [Set.isAddBasisOfOrder_iff]
    intro n
    obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
    refine ⟨![a ^ 2, b ^ 2, c ^ 2, d ^ 2], fun i => ?_, ?_⟩
    · fin_cases i <;> exact ⟨_, rfl⟩
    · simp [Fin.sum_univ_four, h]
  refine le_antisymm (Nat.sInf_le h4) (le_csInf ⟨4, h4⟩ fun s hs => ?_)
  dsimp at hs
  by_contra! hlt
  interval_cases s
  · exact Set.not_isAddBasisOfOrder_zero hs
  · rw [Set.isAddBasisOfOrder_iff] at hs
    obtain ⟨f, hf, hsum⟩ := hs 2
    choose x hx using hf
    dsimp only at hx
    rw [Fin.sum_univ_one, ← hx 0] at hsum
    have h0 : x 0 < 2 := by nlinarith
    interval_cases x 0 <;> norm_num at hsum
  · rw [Set.isAddBasisOfOrder_iff] at hs
    obtain ⟨f, hf, hsum⟩ := hs 3
    choose x hx using hf
    dsimp only at hx
    rw [Fin.sum_univ_two, ← hx 0, ← hx 1] at hsum
    have h0 : x 0 < 2 := by nlinarith
    have h1 : x 1 < 2 := by nlinarith
    interval_cases x 0 <;> interval_cases x 1 <;> norm_num at hsum
  · exact not_squares_isAddBasisOfOrder_three hs

/--
The **ideal Waring conjecture**: for every integer $k \ge 1$, Waring's invariant equals
$$g(k) = 2^k + \left\lfloor \left(\frac{3}{2}\right)^k \right\rfloor - 2.$$
-/
@[category research open, AMS 11]
theorem waring_ideal_conjecture (k : ℕ) (hk : 1 ≤ k) :
    waringG k = eulerWaringBound k := by
  sorry

/--
Fractional-part conjecture for Waring's problem: for every integer $k \ge 1$, writing
$3^k = 2^k q + r$ with $q = \lfloor (3/2)^k \rfloor$ and $0 \le r < 2^k$, one has $q + r \le 2^k$.
-/
@[category research open, AMS 11]
theorem waring_ideal_conjecture.variants.quotient_add_rem_le (k : ℕ) (hk : 1 ≤ k) :
    3 ^ k / 2 ^ k + 3 ^ k % 2 ^ k ≤ 2 ^ k := by
  sorry

/--
Asymptotic Waring conjecture for cubes (see Nathanson 1996, p. 71): $G(3) = 4$, meaning every
sufficiently large natural number is a sum of four nonnegative cubes.
-/
@[category research open, AMS 11]
theorem waringBigG_three : waringBigG 3 = 4 := by
  sorry

/--
The **Hilbert–Waring theorem** (Hilbert, 1909): for every integer $k \ge 1$, the nonnegative $k$-th
powers form an additive basis of $\mathbb{N}$.
-/
@[category research solved, AMS 11]
theorem hilbert_waring (k : ℕ) (hk : 1 ≤ k) :
    (kthPowers k).IsAddBasis := by
  sorry

/--
Combined results of Lagrange (1770, $k = 2$), Wieferich (1909) and Kempner (1912, $k = 3$),
Balasubramanian, Deshouillers, and Dress (1986, $k = 4$), Chen (1964) and Conway ($k = 5$), Pillai
(1940, $k = 6$), and Dickson (1936), Pillai (1936), Rubugunday (1942), and Niven (1944, $k \ge 7$)
prove that $g(k) = 2^k + \lfloor (3/2)^k \rfloor - 2$ holds whenever
$\lfloor (3/2)^k \rfloor + (3^k \bmod 2^k) \le 2^k$.
-/
@[category research solved, AMS 11]
theorem waringG_eq_eulerWaringBound_of_le (k : ℕ) (hk : 1 ≤ k)
    (hqr : 3 ^ k / 2 ^ k + 3 ^ k % 2 ^ k ≤ 2 ^ k) :
    waringG k = eulerWaringBound k := by
  sorry

/--
Mahler (1957) proved that at most finitely many natural numbers $k$ satisfy
$\lfloor (3/2)^k \rfloor + (3^k \bmod 2^k) > 2^k$, and hence at most finitely many $k \ge 1$ can
violate `waring_ideal_conjecture`.
-/
@[category research solved, AMS 11]
theorem mahler_finite_exceptions :
    {k : ℕ | 2 ^ k < 3 ^ k / 2 ^ k + 3 ^ k % 2 ^ k}.Finite := by
  sorry

/--
Davenport (1939) proved that $G(4) = 16$: every sufficiently large natural number is a sum of $16$
fourth powers, while $31 \cdot 16^m$ ($m \in \mathbb{N}$) always requires $16$.
-/
@[category research solved, AMS 11]
theorem davenport_waringBigG_four : waringBigG 4 = 16 := by
  sorry

end WaringProblem
