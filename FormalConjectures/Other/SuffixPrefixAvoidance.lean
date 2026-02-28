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
# Suffix-prefix avoidance bound

Let $A$ and $B$ be sets of words of length $n$ over an alphabet with $q$ letters. If no
(nonempty) suffix of any word in $A$ coincides with a prefix of any word in $B$, then
$$|A| \cdot |B| \leq \frac{q^{2n}}{en}.$$

*Reference:*
- [X post by Dmitry Rybin](https://x.com/DmitryRybin1/status/2027278135847428577)
-/

open Finset Real

namespace SuffixPrefixAvoidance

variable {n q : ℕ}

/-- The suffix of a word `w : Fin n → Fin q` of length `k + 1` (the last `k + 1` characters). -/
def wordSuffix (w : Fin n → Fin q) (k : Fin n) : Fin (k + 1) → Fin q :=
  fun i => w ⟨n - k - 1 + i, by omega⟩

/-- The prefix of a word `w : Fin n → Fin q` of length `k + 1` (the first `k + 1` characters). -/
def wordPrefix (w : Fin n → Fin q) (k : Fin n) : Fin (k + 1) → Fin q :=
  fun i => w ⟨i, by omega⟩

/-- Two sets of words $A, B$ over `Fin q` of length `n` are suffix-prefix avoiding if no
nonempty suffix of any word in $A$ equals any prefix of any word in $B$ of the same length. -/
def IsSuffixPrefixAvoiding (A B : Finset (Fin n → Fin q)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ k : Fin n, wordSuffix a k ≠ wordPrefix b k

/--
$A$ and $B$ are sets of words of length $n$ over alphabet with $q$ letters.
Trivially then $|A| \cdot |B|$ is at most $q^{2n}$.
-/
@[category test, AMS 5]
theorem words_naive_bound
    (A B : Finset (Fin n → Fin q)) :
    A.card * B.card ≤ q ^ (2 * n) := by
  simp [Nat.mul_le_mul, two_mul, pow_add, (Finset.card_le_univ _).trans_eq]

/--
$A$ and $B$ are sets of words of length $n$ over alphabet with $q \geq 1$ letters.
No suffix of a word in $A$ coincides with a prefix of a word in $B$.
Prove that then $|A| \cdot |B|$ is at most $\frac{q^{2n}}{en}$.
-/
-- TODO(firsching): update problem status when solution becomes public
@[category research open, AMS 5]
theorem suffix_prefix_avoidance_bound
    (A B : Finset (Fin n → Fin q))
    (hq : 0 < q) (hn : 0 < n)
    (h : IsSuffixPrefixAvoiding A B) :
    (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n) := by
  sorry

/-! ### Proof of the weaker bound -/

/-- Concatenation of two words of length `n` into a word of length `2 * n`. -/
def wordConcat (a b : Fin n → Fin q) : Fin (2 * n) → Fin q :=
  fun i => if h : i.val < n then a ⟨i, h⟩ else b ⟨i.val - n, by omega⟩

/-- The map F(a, b, i) sends (a, b, i) to the cyclic shift of `a ++ b` by `i` positions. -/
def shiftConcat (hn : 0 < n) (a b : Fin n → Fin q) (i : Fin n) :
    Fin (2 * n) → Fin q :=
  fun j => wordConcat a b ⟨(i.val + j.val) % (2 * n), Nat.mod_lt _ (by omega)⟩

/-- If `shiftConcat` agrees on two triples with suffix-prefix avoidance, then the shift
indices must be equal.

If `i ≠ i'`, let `d = |i' - i|` with `1 ≤ d ≤ n - 1`. Comparing the two
cyclic shifts at indices around the "seam" position `n` shows that the last `d` characters
of one word in `A` equal the first `d` characters of one word in `B`, contradicting the
suffix-prefix avoidance condition. -/
private lemma shiftConcat_shift_eq {A B : Finset (Fin n → Fin q)} (hn : 0 < n)
    {a a' : Fin n → Fin q} {b b' : Fin n → Fin q} {i i' : Fin n}
    (_ha : a ∈ A) (_hb : b ∈ B) (_ha' : a' ∈ A) (_hb' : b' ∈ B)
    (_havoid : IsSuffixPrefixAvoiding A B)
    (_heq : shiftConcat hn a b i = shiftConcat hn a' b' i') :
    i = i' := by
  by_contra hne
  -- The two cyclic shifts agree pointwise
  have hw : ∀ j : Fin (2 * n), wordConcat a b ⟨(i.val + j.val) % (2 * n),
    Nat.mod_lt _ (by omega)⟩ =
      wordConcat a' b' ⟨(i'.val + j.val) % (2 * n),
    Nat.mod_lt _ (by omega)⟩ :=
      fun j => congr_fun _heq j
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · -- Case i < i': d = i'.val - i.val, with 1 ≤ d < n
    -- The suffix of `a` of length `d` equals the prefix of `b'` of length `d`
    have suffix_eq_prefix : wordSuffix a ⟨i'.val - i.val - 1, by omega⟩ =
        wordPrefix b' ⟨i'.val - i.val - 1, by omega⟩ := by
          simp_all[wordConcat, two_mul, wordPrefix,Nat.sub_sub, Fin.forall_iff]
          delta wordPrefix wordSuffix
          use funext fun and=>by_contra (absurd (hw (n-i'+and) (by valid)) ∘? _)
          norm_num[←add_assoc, (by (fin_omega): (n : ℕ)-(i'-i-1)-1+and=i+(n-i'+and) ∧ (n : ℕ)+n>i+(n-i'+and) ∧ (n : ℕ)+and<n+n),hlt.le,Nat.mod_eq_of_lt]
          norm_num[ (by (fin_omega): (n : ℕ)>i+(n-i')+and∧ (n : ℕ)+n>i+(n-i')+and),Nat.mod_eq_of_lt]
    exact _havoid a _ha b' _hb' _ suffix_eq_prefix
  · -- Case i > i': d = i.val - i'.val, with 1 ≤ d < n
    -- The suffix of `a'` of length `d` equals the prefix of `b` of length `d`
    have suffix_eq_prefix : wordSuffix a' ⟨i.val - i'.val - 1, by omega⟩ =
        wordPrefix b ⟨i.val - i'.val - 1, by omega⟩ := by
          show id _=id _
          simp_all[wordConcat, two_mul,n.sub_sub, Fin.forall_iff,Nat.succ_le]
          use funext fun and=>by_contra (absurd (hw (n-(i-i')+and-i') (by valid)).symm ∘? _)
          norm_num[ (by valid:i.1+(n-(i-i')+and-i')=n+and∧i'.1≤n-(i-i')+and∧n-(i-i')+and<n+n),Nat.mod_eq_of_lt]
          use(dif_pos (by valid)).trans_ne.comp (· ∘by norm_num[ (by valid:and.1<n),Nat.mod_eq_of_lt])
    exact _havoid a' _ha' b _hb _ suffix_eq_prefix

/-- When the shift indices agree, the underlying words must also agree.

With `i = i'`, the cyclic shifts are identical iff the concatenations are
identical (the shift is a bijection on indices). Splitting the concatenation at position `n`
recovers `a = a'` and `b = b'`. -/
private lemma shiftConcat_injective (hn : 0 < n)
    {A B : Finset (Fin n → Fin q)} (havoid : IsSuffixPrefixAvoiding A B) :
    Function.Injective (fun (x : ↥A × ↥B × Fin n) =>
      shiftConcat hn (x.1 : Fin n → Fin q) (x.2.1 : Fin n → Fin q) x.2.2) := by
  intro ⟨⟨a, ha⟩, ⟨b, hb⟩, i⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩, i'⟩ heq
  have hi : i = i' := shiftConcat_shift_eq hn ha hb ha' hb' havoid heq
  subst hi
  have ha_eq : a = a' := by
    simp_all[shiftConcat,funext_iff]
    delta wordConcat at*
    use fun and=> if a:i.1≤ and then (by linear_combination2(norm:=norm_num[a, two_mul,Nat.mod_eq_of_lt, and.2.trans,hn])heq ⟨and-i,by valid⟩)else(? _)
    linear_combination2(norm:=norm_num[i.1.le_of_lt, two_mul,Nat.mod_eq_of_lt,Nat.lt_add_left])heq ⟨and+ (2 *n)-i,by valid⟩
  have hb_eq : b = b' := by
    simp_all[shiftConcat,funext_iff]
    delta wordConcat at*
    use (by linear_combination2(norm:=norm_num[i.1.add_sub_of_le ∘le_add_right, two_mul,Nat.mod_eq_of_lt,Nat.add_lt_add])heq ⟨n+.-i,by valid⟩)
  simp [ha_eq, hb_eq]

/--
$A$ and $B$ are sets of words of length $n$ over alphabet with $q \geq 1$ letters.
No suffix of a word in $A$ coincides with a prefix of a word in $B$.
Prove that then $|A| \cdot |B|$ is at most $\frac{q^{2n}}{n}$.

*Proof.* Consider the map $F : A \times B \times \{0, \ldots, n-1\} \to \Sigma^{2n}$ sending
$(a, b, i)$ to the cyclic shift of $ab$ by $i$ positions. The suffix-prefix avoidance
condition ensures $F$ is injective, giving $n|A||B| \leq q^{2n}$.
-/
@[category research solved, AMS 5]
theorem suffix_prefix_avoidance_weaker_bound
    (A B : Finset (Fin n → Fin q))
    (_hq : 0 < q) (hn : 0 < n)
    (h : IsSuffixPrefixAvoiding A B) :
    (A.card : ℚ) * B.card ≤ (q : ℚ) ^ (2 * n) / n := by
  suffices key : n * (A.card * B.card) ≤ q ^ (2 * n) by
    have hn' : (0 : ℚ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hn']
    calc (A.card : ℚ) * B.card * n
        = ↑(n * (A.card * B.card)) := by push_cast; ring
      _ ≤ ↑(q ^ (2 * n)) := by exact_mod_cast key
      _ = (q : ℚ) ^ (2 * n) := by push_cast; ring
  calc n * (A.card * B.card)
      = Fintype.card (↥A × ↥B × Fin n) := by
        simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]; ring
    _ ≤ Fintype.card (Fin (2 * n) → Fin q) :=
        Fintype.card_le_of_injective _ (shiftConcat_injective hn h)
    _ = q ^ (2 * n) := by simp [Fintype.card_fin]

end SuffixPrefixAvoidance
