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

import FormalConjecturesUtil

/-!
# Scholz conjecture on addition chains

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Scholz_conjecture)
- [MathWorld](https://mathworld.wolfram.com/ScholzConjecture.html)
- [Tall22](https://arxiv.org/abs/2210.13812) Amadou Tall. "The Scholz conjecture on addition
  chain is true for infinitely many integers with $\ell(2n) = \ell(n)$." _arXiv:2210.13812_ (2022).
  Also available as [ePrint 2023/020](https://eprint.iacr.org/2023/020).
- [OEIS A003313](https://oeis.org/A003313)
-/

namespace ScholzConjecture

/-- An *addition chain* is a strictly increasing sequence
$1 = a_0 < a_1 < \cdots < a_r$ in which every entry after the first is the sum of two
(not necessarily distinct) earlier entries.

`IsAdditionChain c` asserts that the list $c$ is such a chain: it starts at $1$, is
strictly increasing, and every entry other than $1$ is a sum of two entries of $c$. -/
def IsAdditionChain (c : List ℕ) : Prop :=
  c.head? = some 1 ∧
  c.Pairwise (· < ·) ∧
  ∀ x ∈ c, x ≠ 1 → ∃ y ∈ c, ∃ z ∈ c, x = y + z

/-- The *length* $\ell(n)$ of $n$: the minimal number of addition steps (the number of
entries minus one) over all addition chains ending at $n$. -/
noncomputable def additionChainLength (n : ℕ) : ℕ :=
  sInf { r | ∃ c : List ℕ, IsAdditionChain c ∧ c.getLast? = some n ∧ c.length = r + 1 }

/-- Every quantifier in `IsAdditionChain` is bounded by the list, so membership is decidable
and a concrete chain can be checked by `decide`. -/
instance (c : List ℕ) : Decidable (IsAdditionChain c) := by
  unfold IsAdditionChain; infer_instance

local notation "ℓ(" n ")" => additionChainLength n

@[category API, AMS 11 68]
private lemma le_getLast {c : List ℕ} (h : c.Pairwise (· < ·)) {x : ℕ} (hx : x ∈ c) (hne : c ≠ []) :
    x ≤ c.getLast hne := by
  induction c using List.reverseRecOn with
  | nil => simp at hne
  | append_singleton ys y ih =>
    rw [List.getLast_append_singleton]
    rcases List.mem_append.mp hx with hy | hy
    · exact le_of_lt ((List.pairwise_append.mp h).2.2 _ hy _ (by simp))
    · simp only [List.mem_singleton] at hy; omega
@[category API, AMS 11 68]
private lemma one_le_of_mem {c : List ℕ} (h : IsAdditionChain c) {x : ℕ} (hx : x ∈ c) : 1 ≤ x := by
  obtain ⟨hhead, hsorted, -⟩ := h
  cases c with
  | nil => simp at hx
  | cons a t =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_rfl
    · exact le_of_lt ((List.pairwise_cons.mp hsorted).1 _ hx)
@[category API, AMS 11 68]
private lemma IsAdditionChain.dropLast {ys : List ℕ} {y : ℕ} (h : IsAdditionChain (ys ++ [y]))
    (hys : ys ≠ []) : IsAdditionChain ys := by
  obtain ⟨hhead, hsorted, hsum⟩ := h
  refine ⟨?_, (List.pairwise_append.mp hsorted).1, ?_⟩
  · cases ys with
    | nil => simp at hys
    | cons a t => simpa using hhead
  · intro x hx hx1
    obtain ⟨a, ha, b, hb, rfl⟩ := hsum x (List.mem_append_left _ hx) hx1
    have hxy := (List.pairwise_append.mp hsorted).2.2 _ hx _ (List.mem_singleton_self y)
    have ha1 := one_le_of_mem ⟨hhead, hsorted, hsum⟩ ha
    have hb1 := one_le_of_mem ⟨hhead, hsorted, hsum⟩ hb
    have hay : a ≠ y := by rintro rfl; omega
    have hby : b ≠ y := by rintro rfl; omega
    refine ⟨a, ?_, b, ?_, rfl⟩
    · rcases List.mem_append.mp ha with h | h
      · exact h
      · exact absurd (List.mem_singleton.mp h) hay
    · rcases List.mem_append.mp hb with h | h
      · exact h
      · exact absurd (List.mem_singleton.mp h) hby
/-- Every step at most doubles, so a chain of `r` steps cannot reach past `2 ^ r`. -/
@[category API, AMS 11 68]
private lemma getLast_le_two_pow {c : List ℕ} (h : IsAdditionChain c) (hne : c ≠ []) :
    c.getLast hne ≤ 2 ^ (c.length - 1) := by
  induction c using List.reverseRecOn with
  | nil => simp at hne
  | append_singleton ys y ih =>
    rw [List.getLast_append_singleton]
    rcases eq_or_ne ys [] with rfl | hys
    · obtain ⟨hhead, -, -⟩ := h
      simp only [List.nil_append, List.head?_cons, Option.some.injEq] at hhead
      simp [hhead]
    · have hchain := h.dropLast hys
      obtain ⟨hhead, hsorted, hsum⟩ := h
      have hy1 : y ≠ 1 := by
        rintro rfl
        obtain ⟨a, hays⟩ := List.exists_mem_of_ne_nil ys hys
        have := (List.pairwise_append.mp hsorted).2.2 _ hays _ (List.mem_singleton_self 1)
        have := one_le_of_mem ⟨hhead, hsorted, hsum⟩ (List.mem_append_left _ hays)
        omega
      obtain ⟨a, ha, b, hb, hyab⟩ := hsum y (by simp) hy1
      have ha1 := one_le_of_mem ⟨hhead, hsorted, hsum⟩ ha
      have hb1 := one_le_of_mem ⟨hhead, hsorted, hsum⟩ hb
      have hays : a ∈ ys := by
        rcases List.mem_append.mp ha with h' | h'
        · exact h'
        · exact absurd (List.mem_singleton.mp h') (by rintro rfl; omega)
      have hbys : b ∈ ys := by
        rcases List.mem_append.mp hb with h' | h'
        · exact h'
        · exact absurd (List.mem_singleton.mp h') (by rintro rfl; omega)
      have hla := le_getLast (List.pairwise_append.mp hsorted).1 hays hys
      have hlb := le_getLast (List.pairwise_append.mp hsorted).1 hbys hys
      have hih := ih hchain hys
      have hlen : (ys ++ [y]).length - 1 = ys.length := by simp
      rw [hlen]
      have hyl : ys.length = (ys.length - 1) + 1 := by
        cases ys with
        | nil => simp at hys
        | cons _ t => simp
      rw [hyl, pow_succ]
      omega


/-- The set of step counts realised by chains ending at `n`. -/
private def chainSteps (n : ℕ) : Set ℕ :=
  { r | ∃ c : List ℕ, IsAdditionChain c ∧ c.getLast? = some n ∧ c.length = r + 1 }

@[category API, AMS 11 68]
private lemma additionChainLength_eq_sInf (n : ℕ) :
    additionChainLength n = sInf (chainSteps n) := rfl

/-- The doubling bound, transported to `ℓ`: reaching `n` takes at least `log₂ n` steps. -/
@[category API, AMS 11 68]
private lemma le_two_pow_additionChainLength {n : ℕ} (hne : (chainSteps n).Nonempty) :
    n ≤ 2 ^ additionChainLength n := by
  obtain ⟨c, hc, hlast, hlen⟩ := Nat.sInf_mem hne
  have hcne : c ≠ [] := by rintro rfl; simp at hlast
  have : c.getLast hcne = n := by
    rw [List.getLast?_eq_some_getLast (l := c) (h := hcne)] at hlast
    exact Option.some.inj hlast
  have := getLast_le_two_pow hc hcne
  rw [‹c.getLast hcne = n›, hlen] at this
  simpa [additionChainLength_eq_sInf] using this

/-- The lower-bound tool: `r` steps cannot reach past `2 ^ r`. -/
@[category API, AMS 11 68]
private lemma lt_additionChainLength_of_two_pow_lt {n r : ℕ} (hne : (chainSteps n).Nonempty)
    (h : 2 ^ r < n) : r < additionChainLength n := by
  by_contra hcon
  push_neg at hcon
  have h1 := le_two_pow_additionChainLength hne
  have h2 : (2 : ℕ) ^ additionChainLength n ≤ 2 ^ r := Nat.pow_le_pow_right two_pos hcon
  omega

/--
The Scholz conjecture, also known as the Scholz-Brauer conjecture, asserts that
for every positive integer $n$, the addition-chain length of $2^n - 1$ is at most
$n - 1 + \ell(n)$.
-/
@[category research open, AMS 11 68]
theorem scholz_conjecture :
    answer(sorry) ↔ ∀ (n : ℕ), 0 < n → ℓ(2 ^ n - 1) ≤ n - 1 + ℓ(n) := by
  sorry

-- TODO(eyang07): add solved variants. See Wikipedia reference.

/-- Exhibiting a chain bounds `ℓ` above. -/
@[category API, AMS 11 68]
private lemma additionChainLength_le {n r : ℕ} (c : List ℕ) (hc : IsAdditionChain c)
    (hlast : c.getLast? = some n) (hlen : c.length = r + 1) : additionChainLength n ≤ r :=
  Nat.sInf_le ⟨c, hc, hlast, hlen⟩

@[category API, AMS 11 68]
private lemma chainSteps_nonempty {n r : ℕ} (c : List ℕ) (hc : IsAdditionChain c)
    (hlast : c.getLast? = some n) (hlen : c.length = r + 1) : (chainSteps n).Nonempty :=
  ⟨r, c, hc, hlast, hlen⟩

/-- `7` is the first value where the doubling bound is not sharp: it gives `ℓ(7) ≥ 3`, and no
four-entry chain ends at `7`. Every entry of such a chain lies strictly between `1` and `7`, so
there are only finitely many to rule out. -/
@[category API, AMS 11 68]
private lemma three_notMem_chainSteps_seven : 3 ∉ chainSteps 7 := by
  rintro ⟨c, ⟨hhead, hsorted, hsum⟩, hlast, hlen⟩
  match c, hlen with
  | [w, x, y, z], _ =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hlast
    subst hhead; subst hlast
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at hsorted
    obtain ⟨⟨h1x, h1y, -⟩, ⟨hxy, hx7⟩, hy7, -⟩ := hsorted
    interval_cases x <;> interval_cases y <;> simp_all [List.mem_cons]

/-- The first few values of $\ell(n)$. See [OEIS A003313](https://oeis.org/A003313). -/
@[category test, AMS 11]
theorem additionChainLength_first_values :
    [ℓ(1), ℓ(2), ℓ(3), ℓ(4), ℓ(5), ℓ(6), ℓ(7), ℓ(8), ℓ(9), ℓ(10)] =
    [0, 1, 2, 2, 3, 3, 4, 3, 4, 4] := by
  have h1 : ℓ(1) = 0 := Nat.le_zero.mp (additionChainLength_le [1] (by decide) rfl rfl)
  have key : ∀ (n r : ℕ) (c : List ℕ), IsAdditionChain c → c.getLast? = some n →
      c.length = r + 1 → 2 ^ (r - 1) < n → 1 ≤ r → ℓ(n) = r := by
    intro n r c hc hlast hlen hlow hr
    refine le_antisymm (additionChainLength_le c hc hlast hlen) ?_
    have := lt_additionChainLength_of_two_pow_lt (chainSteps_nonempty c hc hlast hlen) hlow
    omega
  have h2 := key 2 1 [1, 2] (by decide) rfl rfl (by norm_num) (by norm_num)
  have h3 := key 3 2 [1, 2, 3] (by decide) rfl rfl (by norm_num) (by norm_num)
  have h4 := key 4 2 [1, 2, 4] (by decide) rfl rfl (by norm_num) (by norm_num)
  have h5 := key 5 3 [1, 2, 4, 5] (by decide) rfl rfl (by norm_num) (by norm_num)
  have h6 := key 6 3 [1, 2, 3, 6] (by decide) rfl rfl (by norm_num) (by norm_num)
  have h8 := key 8 3 [1, 2, 4, 8] (by decide) rfl rfl (by norm_num) (by norm_num)
  have h9 := key 9 4 [1, 2, 4, 8, 9] (by decide) rfl rfl (by norm_num) (by norm_num)
  have h10 := key 10 4 [1, 2, 4, 5, 10] (by decide) rfl rfl (by norm_num) (by norm_num)
  have h7 : ℓ(7) = 4 := by
    have hne := chainSteps_nonempty (n := 7) (r := 4) [1, 2, 3, 4, 7] (by decide) rfl rfl
    have hub := additionChainLength_le (n := 7) (r := 4) [1, 2, 3, 4, 7] (by decide) rfl rfl
    have hlb := lt_additionChainLength_of_two_pow_lt (n := 7) (r := 2) hne (by norm_num)
    have hne3 : ℓ(7) ≠ 3 := fun h => three_notMem_chainSteps_seven (h ▸ Nat.sInf_mem hne)
    omega
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  
end ScholzConjecture
