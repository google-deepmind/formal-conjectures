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

public import Mathlib.Data.Nat.Lattice
public import Mathlib.Data.List.Sort

@[expose] public section

/-!
# Addition chains

An *addition chain* for $n$ is a strictly increasing sequence
$1 = a_0 < a_1 < \cdots < a_r = n$ in which every entry after the first is the sum of two
earlier entries. Its length is $r$, the number of additions, and $\ell(n)$ is the least
length over all chains ending at $n$.

`additionChainLength` is an infimum over `List ℕ`, so an explicit chain bounds it above
(`additionChainLength_le`) but nothing bounds it below until the search is confined. The
confinement here is that an addition step at most doubles, so `r` steps cannot reach past
`2 ^ r` (`getLast_le_two_pow`), giving `lt_additionChainLength_of_two_pow_lt`.
-/

/-- An *addition chain* is a strictly increasing sequence
$1 = a_0 < a_1 < \cdots < a_r$ in which every entry after the first is the sum of two
(not necessarily distinct) earlier entries.

`IsAdditionChain c` asserts that the list $c$ is such a chain: it starts at $1$, is
strictly increasing, and every entry other than $1$ is a sum of two entries of $c$. -/
def IsAdditionChain (c : List ℕ) : Prop :=
  c.head? = some 1 ∧
  c.Pairwise (· < ·) ∧
  ∀ x ∈ c, x ≠ 1 → ∃ y ∈ c, ∃ z ∈ c, x = y + z

/-- Every quantifier in `IsAdditionChain` is bounded by the list, so membership is decidable
and a concrete chain can be checked by `decide`. -/
instance (c : List ℕ) : Decidable (IsAdditionChain c) := by
  unfold IsAdditionChain; infer_instance

/-- The *length* $\ell(n)$ of $n$: the minimal number of addition steps (the number of
entries minus one) over all addition chains ending at $n$. -/
noncomputable def additionChainLength (n : ℕ) : ℕ :=
  sInf { r | ∃ c : List ℕ, IsAdditionChain c ∧ c.getLast? = some n ∧ c.length = r + 1 }

/-- The set of step counts realised by chains ending at `n`. -/
def additionChainSteps (n : ℕ) : Set ℕ :=
  { r | ∃ c : List ℕ, IsAdditionChain c ∧ c.getLast? = some n ∧ c.length = r + 1 }

theorem additionChainLength_eq_sInf (n : ℕ) :
    additionChainLength n = sInf (additionChainSteps n) := rfl

/-- Exhibiting a chain bounds `ℓ` above. -/
theorem additionChainLength_le {n r : ℕ} (c : List ℕ) (hc : IsAdditionChain c)
    (hlast : c.getLast? = some n) (hlen : c.length = r + 1) : additionChainLength n ≤ r :=
  Nat.sInf_le ⟨c, hc, hlast, hlen⟩

theorem additionChainSteps_nonempty {n r : ℕ} (c : List ℕ) (hc : IsAdditionChain c)
    (hlast : c.getLast? = some n) (hlen : c.length = r + 1) : (additionChainSteps n).Nonempty :=
  ⟨r, c, hc, hlast, hlen⟩

theorem IsAdditionChain.one_le_of_mem {c : List ℕ} (h : IsAdditionChain c) {x : ℕ}
    (hx : x ∈ c) : 1 ≤ x := by
  obtain ⟨hhead, hsorted, -⟩ := h
  cases c with
  | nil => simp at hx
  | cons a t =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_rfl
    · exact le_of_lt ((List.pairwise_cons.mp hsorted).1 _ hx)

/-- Dropping the last entry of a chain leaves a chain. The entries are positive, so a summand
of the last entry is never the last entry itself and so survives the drop. -/
theorem IsAdditionChain.dropLast {ys : List ℕ} {y : ℕ} (h : IsAdditionChain (ys ++ [y]))
    (hys : ys ≠ []) : IsAdditionChain ys := by
  obtain ⟨hhead, hsorted, hsum⟩ := h
  refine ⟨?_, (List.pairwise_append.mp hsorted).1, ?_⟩
  · cases ys with
    | nil => simp at hys
    | cons a t => simpa using hhead
  · intro x hx hx1
    obtain ⟨a, ha, b, hb, rfl⟩ := hsum x (List.mem_append_left _ hx) hx1
    have hxy := (List.pairwise_append.mp hsorted).2.2 _ hx _ (List.mem_singleton_self y)
    have ha1 := IsAdditionChain.one_le_of_mem ⟨hhead, hsorted, hsum⟩ ha
    have hb1 := IsAdditionChain.one_le_of_mem ⟨hhead, hsorted, hsum⟩ hb
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
theorem IsAdditionChain.getLast_le_two_pow {c : List ℕ} (h : IsAdditionChain c) (hne : c ≠ []) :
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
        have := IsAdditionChain.one_le_of_mem ⟨hhead, hsorted, hsum⟩ (List.mem_append_left _ hays)
        omega
      obtain ⟨a, ha, b, hb, hyab⟩ := hsum y (by simp) hy1
      have ha1 := IsAdditionChain.one_le_of_mem ⟨hhead, hsorted, hsum⟩ ha
      have hb1 := IsAdditionChain.one_le_of_mem ⟨hhead, hsorted, hsum⟩ hb
      have hays : a ∈ ys := by
        rcases List.mem_append.mp ha with h' | h'
        · exact h'
        · exact absurd (List.mem_singleton.mp h') (by rintro rfl; omega)
      have hbys : b ∈ ys := by
        rcases List.mem_append.mp hb with h' | h'
        · exact h'
        · exact absurd (List.mem_singleton.mp h') (by rintro rfl; omega)
      have hsub := (List.pairwise_append.mp hsorted).1.imp le_of_lt
      have hla := hsub.rel_getLast hays
      have hlb := hsub.rel_getLast hbys
      have hih := ih hchain hys
      have hlen : (ys ++ [y]).length - 1 = ys.length := by simp
      rw [hlen]
      have hyl : ys.length = (ys.length - 1) + 1 := by
        cases ys with
        | nil => simp at hys
        | cons _ t => simp
      rw [hyl, pow_succ]
      omega

/-- The doubling bound, transported to `ℓ`: reaching `n` takes at least `log₂ n` steps. -/
theorem le_two_pow_additionChainLength {n : ℕ} (hne : (additionChainSteps n).Nonempty) :
    n ≤ 2 ^ additionChainLength n := by
  obtain ⟨c, hc, hlast, hlen⟩ := Nat.sInf_mem hne
  have hcne : c ≠ [] := by rintro rfl; simp at hlast
  have : c.getLast hcne = n := by
    rw [List.getLast?_eq_some_getLast (l := c) (h := hcne)] at hlast
    exact Option.some.inj hlast
  have := hc.getLast_le_two_pow hcne
  rw [‹c.getLast hcne = n›, hlen] at this
  simpa [additionChainLength_eq_sInf] using this

/-- The lower-bound tool: `r` steps cannot reach past `2 ^ r`. -/
theorem lt_additionChainLength_of_two_pow_lt {n r : ℕ} (hne : (additionChainSteps n).Nonempty)
    (h : 2 ^ r < n) : r < additionChainLength n := by
  by_contra! hcon
  have h1 := le_two_pow_additionChainLength hne
  have h2 : (2 : ℕ) ^ additionChainLength n ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hcon
  omega
