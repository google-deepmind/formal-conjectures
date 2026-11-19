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
# Refining Lagrange's four-square theorem with $(5x^2 + 7y^2 + 9z^2)yz$ a square

Number of ordered ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $(5x^2 + 7y^2 + 9z^2)yz$
a square, where $x, y, z, w$ are nonnegative integers with $z > 0$.

*References:*
- [A261876](https://oeis.org/A261876)
- [Refining Lagrange's four-square theorem](https://arxiv.org/abs/1604.06723)
  by *Zhi-Wei Sun*, arXiv:1604.06723 (2016)
- [arXiv:2608.11941](https://arxiv.org/abs/2608.11941)
-/

@[expose] public section

namespace OeisA261876

/-- Whether a natural number $k$ is a perfect square. -/
def isSquare (k : ℕ) : Bool :=
  Nat.sqrt k ^ 2 == k

/--
Number of ordered ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $(5x^2 + 7y^2 + 9z^2)yz$
a square, where $x, y, z, w$ are nonnegative integers with $z > 0$.
-/
def a (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (n + 1),
    ∑ y ∈ Finset.range (n + 1),
      ∑ z ∈ Finset.Ico 1 (n + 1),
        ∑ w ∈ Finset.range (n + 1),
          if x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 == n &&
             isSquare ((5 * x ^ 2 + 7 * y ^ 2 + 9 * z ^ 2) * y * z) then
            1
          else 0

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by decide +kernel

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by decide +kernel

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by decide +kernel

@[category test, AMS 11]
theorem a_5 : a 5 = 4 := by decide +kernel

/-- The set of base integers $m$ for which $a(n) = 1$ when $n = 4^k m$. -/
def specialSet : Finset ℕ :=
  {1, 7, 23, 647, 863}

/--
Conjecture (i): $a(n) > 0$ for all $n > 0$.
-/
@[category research open, AMS 11]
theorem conjecture_1 (n : ℕ) (hn : 0 < n) : 0 < a n := by
  sorry

/--
Conjecture (i): $a(n) = 1$ only for $n = 4^k m$ ($k = 0, 1, 2, \dots$ and
$m \in \{1, 7, 23, 647, 863\}$).

Disproved in [arXiv:2608.11941](https://arxiv.org/abs/2608.11941) at $n = 69383$, where
$(x, y, z, w) = (187, 147, 6, 113)$ is the unique representation, so $a(69383) = 1$.
-/
@[category research solved, AMS 11]
theorem conjecture_2 :
    ¬ ∀ n : ℕ, (a n = 1 ↔ ∃ k : ℕ, ∃ m ∈ specialSet, n = 4 ^ k * m) := by
  sorry

/-- The set of coefficient triples $(c_1, c_2, c_3)$ for part (ii) of the conjecture. -/
def triples : Finset (ℕ × ℕ × ℕ) :=
  {(1, 8, 20), (3, 5, 15), (6, 14, 4), (7, 29, 5), (18, 38, 18), (39, 81, 51), (42, 98, 14)}

/-- Pairs `(m, mask)` where bit `r` of `mask` is set iff `r` is a square modulo `m`. -/
private def qrMasks : List (ℕ × ℕ) :=
  [(64, 144680414395695635), (63, 288872697407275667), (25, 19483219), (11, 571),
   (13, 5659), (17, 107287), (19, 199411), (23, 340831), (29, 332473075),
   (31, 303908791), (37, 96068509339), (41, 1870503675703), (43, 3678700564051),
   (47, 4626135339999)]

/-- Certify that every square residue modulo `m` has its bit set in `mask`. -/
private def masksValid : Bool :=
  qrMasks.all fun p =>
    0 < p.1 && (List.range p.1).all fun u => (p.2 / 2 ^ (u * u % p.1)) % 2 == 1

/-- Modular non-residue test certifying that $xy(42x^2 + 98y^2 + 14z^2)$ is not a square. -/
private def ok3 (x y z : ℕ) : Bool :=
  let k := x * y * (42 * x ^ 2 + 98 * y ^ 2 + 14 * z ^ 2)
  qrMasks.any fun p => (p.2 / 2 ^ (k % p.1)) % 2 == 0

/-- Check `f` across all $6$ permutations of $(a, b, c)$. -/
private def okSub (f : ℕ → ℕ → ℕ → Bool) (a b c : ℕ) : Bool :=
  f a b c && f a c b && f b a c && f b c a && f c a b && f c b a

/-- Check `f` across all $24$ ordered triples drawn from $(a, b, c, d)$. -/
private def ok4 (f : ℕ → ℕ → ℕ → Bool) (a b c d : ℕ) : Bool :=
  okSub f a b c && okSub f a b d && okSub f a c d && okSub f b c d

/-- Single binary-search step for integer square root without kernel recursion. -/
private def isqrtStep (b n r : ℕ) : ℕ :=
  if (r + b) * (r + b) ≤ n then r + b else r

/-- Non-recursive integer square root exact on $n < 65536$. -/
private def isqrt255 (n : ℕ) : ℕ :=
  isqrtStep 1 n <| isqrtStep 2 n <| isqrtStep 4 n <| isqrtStep 8 n <|
    isqrtStep 16 n <| isqrtStep 32 n <| isqrtStep 64 n <| isqrtStep 128 n 0

/-- Exhaustive check over sorted four-square decompositions $a \le b \le c \le d$ of $56271$. -/
private def checkRange (dLo dLen : ℕ) : Bool :=
  (List.range' dLo dLen).all fun d => d % 4 == 0 ||
    let r1 := 56271 - d * d
    let cLo := isqrt255 (r1 / 3)
    let cHi := min d (isqrt255 r1)
    (List.range' cLo (cHi + 1 - cLo)).all fun c =>
      c % 4 == 0 || (d % 2 == 0 && c % 2 == 0) ||
        let r2 := r1 - c * c
        let bLo := isqrt255 (r2 / 2)
        let bHi := min c (isqrt255 r2)
        (List.range' bLo (bHi + 1 - bLo)).all fun b =>
          b % 4 == 0 || ((d % 2 == 0 || c % 2 == 0) && b % 2 == 0) ||
            let r3 := r2 - b * b
            let a := isqrt255 r3
            a * a != r3 || ok4 ok3 a b c d

@[category API, AMS 11]
private lemma masksValid_eq_true : masksValid = true := by decide +kernel

@[category API, AMS 11]
private lemma checkRange_1 : checkRange 119 40 = true := by decide +kernel

@[category API, AMS 11]
private lemma checkRange_2 : checkRange 159 40 = true := by decide +kernel

@[category API, AMS 11]
private lemma checkRange_3 : checkRange 199 39 = true := by decide +kernel

/--
Conjecture (ii): For each triple $(c_1, c_2, c_3) \in \{(1,8,20), (3,5,15), (6,14,4), (7,29,5),
(18,38,18), (39,81,51), (42,98,14)\}$, any natural number can be written as
$x^2 + y^2 + z^2 + w^2$ with $x, y, z, w$ nonnegative integers such that
$xy(c_1 x^2 + c_2 y^2 + c_3 z^2)$ is a square.

Disproved for $(c_1, c_2, c_3) = (42, 98, 14)$ at $n = 56271$.
-/
@[category research solved, AMS 11]
theorem conjecture_3 :
    ¬ ∀ t ∈ triples, ∀ n : ℕ, ∃ x y z w : ℕ, n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧
      IsSquare (x * y * (t.1 * x ^ 2 + t.2.1 * y ^ 2 + t.2.2 * z ^ 2)) := by
  intro h
  obtain ⟨a, b, c, d, hs, r, hr⟩ := h (42, 98, 14) (by decide) 56271
  have hvalid := masksValid_eq_true
  simp only [masksValid, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hvalid
  have hok3 : ok3 a b c = false := by
    simp only [ok3, hr, List.any_eq_false]
    intro p hp
    obtain ⟨hm, hmask⟩ := hvalid p hp
    have hu := hmask (r % p.1) (Nat.mod_lt r hm)
    rw [← Nat.mul_mod] at hu
    rw [hu]
    decide
  have hok : ok4 ok3 a b c d = false := by simp [ok4, okSub, hok3]
  clear hok3 hr r h hvalid
  have sSub12 : ∀ (f : ℕ → ℕ → ℕ → Bool) u v w, okSub f v u w = okSub f u v w := by
    intro f u v w; simp only [okSub, Bool.and_comm, Bool.and_left_comm]
  have sSub23 : ∀ (f : ℕ → ℕ → ℕ → Bool) u v w, okSub f u w v = okSub f u v w := by
    intro f u v w; simp only [okSub, Bool.and_comm, Bool.and_left_comm]
  have s12 : ∀ (f : ℕ → ℕ → ℕ → Bool) u v w t, ok4 f v u w t = ok4 f u v w t := by
    intro f u v w t; simp only [ok4, sSub12 f v u, Bool.and_assoc, Bool.and_comm]
  have s34 : ∀ (f : ℕ → ℕ → ℕ → Bool) u v w t, ok4 f u v t w = ok4 f u v w t := by
    intro f u v w t; simp only [ok4, sSub23 f _ t w, Bool.and_assoc, Bool.and_comm]
  have s23 : ∀ (f : ℕ → ℕ → ℕ → Bool) u v w t, ok4 f u w v t = ok4 f u v w t := by
    intro f u v w t; simp only [ok4, sSub23 f u w v, sSub12 f w v t, Bool.and_assoc, Bool.and_comm]
  wlog hab : a ≤ b generalizing a b
  · exact this b a (by linarith) (by rwa [s12]) (by omega)
  wlog hcd : c ≤ d generalizing c d
  · exact this d c (by linarith) (by rwa [s34]) (by omega)
  wlog hac : a ≤ c generalizing a b c d
  · refine this c d hcd a b (by linarith) ?_ hab (by omega)
    rw [s23, s12, s34, s23]; exact hok
  wlog hbd : b ≤ d generalizing b d
  · refine this d (by omega) b (by linarith) ?_ (by omega) (by omega)
    rw [s23, s34, s23]; exact hok
  wlog hbc : b ≤ c generalizing b c
  · exact this b hab c (by omega) (by linarith) (by rwa [s23]) hbd hcd (by omega)
  have sq8 : ∀ k : ℕ, (k ^ 2 % 8 = 0 ∧ k % 4 = 0) ∨ (k ^ 2 % 8 = 4 ∧ k % 4 = 2) ∨
      (k ^ 2 % 8 = 1 ∧ k % 2 = 1) := by
    intro k
    have hk : ∀ u ∈ List.range 8, (u ^ 2 % 8 = 0 ∧ u % 4 = 0) ∨
        (u ^ 2 % 8 = 4 ∧ u % 4 = 2) ∨ (u ^ 2 % 8 = 1 ∧ u % 2 = 1) := by decide
    simpa [Nat.pow_mod, Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 8),
      Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 8)] using hk (k % 8) (List.mem_range.mpr (by omega))
  have ha8 := sq8 a; have hb8 := sq8 b; have hc8 := sq8 c; have hd8 := sq8 d
  have hmod : d % 4 ≠ 0 ∧ c % 4 ≠ 0 ∧ b % 4 ≠ 0 ∧ ¬ (d % 2 = 0 ∧ c % 2 = 0) ∧
      ¬ ((d % 2 = 0 ∨ c % 2 = 0) ∧ b % 2 = 0) := by omega
  clear ha8 hb8 hc8 hd8 sq8 sSub12 sSub23 s12 s34 s23
  have hs' : a * a + b * b + c * c + d * d = 56271 := by linarith [sq a, sq b, sq c, sq d]
  have hab2 : a * a ≤ b * b := Nat.mul_le_mul hab hab
  have hac2 : a * a ≤ c * c := Nat.mul_le_mul hac hac
  have hbc2 : b * b ≤ c * c := Nat.mul_le_mul hbc hbc
  have hcd2 : c * c ≤ d * d := Nat.mul_le_mul hcd hcd
  have mono_sq : ∀ x y : ℕ, x * x ≤ y * y → x ≤ y := fun x y _ => by nlinarith
  have lt_sq : ∀ x y : ℕ, x * x < y * y → x < y := fun x y _ => by nlinarith
  have hstep : ∀ s n u, u * u ≤ n ∧ n < (u + 2 * s) * (u + 2 * s) →
      isqrtStep s n u * isqrtStep s n u ≤ n ∧
        n < (isqrtStep s n u + s) * (isqrtStep s n u + s) := by
    intro s n u ⟨h1, h2⟩; dsimp [isqrtStep]; split_ifs with h3
    · exact ⟨h3, by simpa [Nat.add_assoc, Nat.two_mul] using h2⟩
    · exact ⟨h1, by nlinarith⟩
  have hisqrt : ∀ n < 65536,
      isqrt255 n * isqrt255 n ≤ n ∧ n < (isqrt255 n + 1) * (isqrt255 n + 1) := by
    intro n hn
    exact hstep 1 n _ <| hstep 2 n _ <| hstep 4 n _ <| hstep 8 n _ <|
      hstep 16 n _ <| hstep 32 n _ <| hstep 64 n _ <| hstep 128 n 0 ⟨by omega, hn⟩
  have hc1 : isqrt255 ((56271 - d * d) / 3) ≤ c :=
    mono_sq _ _ (le_trans (hisqrt ((56271 - d * d) / 3) (by omega)).1 (by omega))
  have hc2 : c ≤ min d (isqrt255 (56271 - d * d)) := by
    have : c < isqrt255 (56271 - d * d) + 1 :=
      lt_sq _ _ (lt_of_le_of_lt (by omega) (hisqrt (56271 - d * d) (by omega)).2)
    omega
  have hb1 : isqrt255 ((56271 - d * d - c * c) / 2) ≤ b :=
    mono_sq _ _ (le_trans (hisqrt ((56271 - d * d - c * c) / 2) (by omega)).1 (by omega))
  have hb2 : b ≤ min c (isqrt255 (56271 - d * d - c * c)) := by
    have : b < isqrt255 (56271 - d * d - c * c) + 1 :=
      lt_sq _ _ (lt_of_le_of_lt (by omega) (hisqrt (56271 - d * d - c * c) (by omega)).2)
    omega
  have ha : isqrt255 (56271 - d * d - c * c - b * b) = a := by
    obtain ⟨h1, h2⟩ := hisqrt (56271 - d * d - c * c - b * b) (by omega)
    have hle : isqrt255 (56271 - d * d - c * c - b * b) ≤ a := mono_sq _ _ (by omega)
    have hlt : a < isqrt255 (56271 - d * d - c * c - b * b) + 1 := lt_sq _ _ (by omega)
    omega
  have hd_lo : 119 ≤ d := lt_sq 118 d (by omega)
  have hd_hi : d < 238 := lt_sq d 238 (by omega)
  have hd_ok : (d % 4 == 0 ||
      let r1 := 56271 - d * d
      let cLo := isqrt255 (r1 / 3)
      let cHi := min d (isqrt255 r1)
      (List.range' cLo (cHi + 1 - cLo)).all fun c =>
        c % 4 == 0 || (d % 2 == 0 && c % 2 == 0) ||
          let r2 := r1 - c * c
          let bLo := isqrt255 (r2 / 2)
          let bHi := min c (isqrt255 r2)
          (List.range' bLo (bHi + 1 - bLo)).all fun b =>
            b % 4 == 0 || ((d % 2 == 0 || c % 2 == 0) && b % 2 == 0) ||
              let r3 := r2 - b * b
              let a := isqrt255 r3
              a * a != r3 || ok4 ok3 a b c d) = true := by
    by_cases h159 : d < 159
    · exact List.all_eq_true.mp checkRange_1 d (List.mem_range'_1.mpr ⟨hd_lo, by omega⟩)
    by_cases h199 : d < 199
    · exact List.all_eq_true.mp checkRange_2 d (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp checkRange_3 d (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  simp only [List.all_eq_true, List.mem_range'_1, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, bne_iff_ne, or_assoc] at hd_ok
  rcases hd_ok with hd4 | hc_all
  · exact hmod.1 hd4
  rcases hc_all c ⟨hc1, by omega⟩ with hc4 | hdc2 | hb_all
  · exact hmod.2.1 hc4
  · exact hmod.2.2.2.1 hdc2
  rcases hb_all b ⟨hb1, by omega⟩ with hb4 | hpar | hne | htrue
  · exact hmod.2.2.1 hb4
  · exact hmod.2.2.2.2 hpar
  · exact hne (by rw [ha]; omega)
  · rw [ha, hok] at htrue; exact Bool.false_ne_true htrue

end OeisA261876
