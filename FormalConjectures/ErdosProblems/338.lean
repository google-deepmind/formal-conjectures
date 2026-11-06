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
# Erdős Problem 338

*References:*
- [erdosproblems.com/338](https://www.erdosproblems.com/338)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [ErGr80b] Erdős, P. and Graham, R. L., *On bases with an exact order*. Acta Arith. (1980),
  201-207.
- [HHP07] Hegyvári, Norbert and Hennecart, François and Plagne, Alain, *Answer to a question by
  Burr and Erdős on restricted addition, and related results*. Combin. Probab. Comput. (2007),
  747--756.
- [He05] Hennecart, François, *On the restricted order of asymptotic bases of order two*.
  Ramanujan J. (2005), 123--130.
- [Ke57] Kelly, John B., *Restricted bases*. Amer. J. Math. (1957), 258-264.
- [Pa33] Pall, Gordon, *On Sums of Squares*. Amer. Math. Monthly (1933), 10-18.
- [Sc54] Schinzel, A., *Sur la décomposition des nombres naturels en sommes de nombres
  triangulaires distincts*. Bull. Acad. Polon. Sci. Cl. III. (1954), 409-410.
-/

@[expose] public section

namespace Erdos338

open Filter

/-- `HasOrder A h` means that $A$ is a basis of order $h$: every sufficiently large natural number
is a sum of at most $h$ elements of $A$, with repetition allowed.

The summands form a `Multiset`, so repetition is allowed. Allowing at most $h$ summands makes the
notion independent of whether $0 \in A$. With exactly $h$ summands, as in
`Set.IsAsymptoticAddBasisOfOrder`, this notion is `(insert 0 A).IsAsymptoticAddBasisOfOrder h`. -/
def HasOrder (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ᶠ m in atTop, ∃ S : Multiset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ h ∧ S.sum = m

/-- `HasRestrictedOrder A t` means that every sufficiently large natural number is a sum of at most
$t$ distinct elements of $A$.

The summands form a `Finset`, so they are distinct. A summand $0$ never helps, so the notion does
not depend on whether $0 \in A$. -/
def HasRestrictedOrder (A : Set ℕ) (t : ℕ) : Prop :=
  ∀ᶠ m in atTop, ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ t ∧ ∑ x ∈ S, x = m

/-- The order of $A$: the least $h$ with `HasOrder A h`, or `⊤` if $A$ is not a basis. -/
noncomputable def basisOrder (A : Set ℕ) : ℕ∞ :=
  ⨅ (h : ℕ) (_ : HasOrder A h), (h : ℕ∞)

/-- The restricted order of $A$: the least $t$ with `HasRestrictedOrder A t`, or `⊤` if no such
$t$ exists. -/
noncomputable def restrictedOrder (A : Set ℕ) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : HasRestrictedOrder A t), (t : ℕ∞)

def erdos_338.answer : Set ℕ → Prop := sorry

/--
The restricted order of a basis $A$ is the least integer $t$ (if it exists) such that every large
integer is the sum of at most $t$ distinct summands from $A$. What are necessary and sufficient
conditions that this exists?

A solution must fill in `Erdos338.erdos_338.answer` with the condition and prove the
equivalence. Whether a condition is a satisfactory answer is up to human judgement.
-/
@[category research open, question value, AMS 11]
theorem erdos_338 :
    ∀ A : Set ℕ, (∃ h, HasOrder A h) → ((∃ t, HasRestrictedOrder A t) ↔ erdos_338.answer A) := by
  sorry

/--
Can the restricted order of a basis be bounded (when it exists) in terms of the order of the
basis?

`HasOrder A h` only says that the order of $A$ is at most $h$. This gives the same question,
since $f$ can be replaced by its running maximum. Kelly [Ke57] showed that $f(2) = 4$ works, and
Hennecart [He05] showed that $4$ is optimal. Hegyvári, Hennecart and Plagne [HHP07] showed that
any such $f$ has $f(k) \geq 2^{k-2}+k-1$ for $k \geq 3$.
-/
@[category research open, question, AMS 11]
theorem erdos_338.variants.bounded_by_order :
    ∃ f : ℕ → ℕ, ∀ (A : Set ℕ) (h : ℕ), HasOrder A h →
      (∃ t, HasRestrictedOrder A t) → HasRestrictedOrder A (f h) := by
  sorry

def erdos_338.variants.eq_order.answer : Set ℕ → Prop := sorry

/--
What are necessary and sufficient conditions that the restricted order of a basis $A$ is equal to
the order of $A$?

For a basis, `basisOrder A` is finite, so the equality also says that the restricted order exists.
The condition is `Erdos338.erdos_338.variants.eq_order.answer`, as in `Erdos338.erdos_338`.
-/
@[category research open, question value, AMS 11]
theorem erdos_338.variants.eq_order :
    ∀ A : Set ℕ, (∃ h, HasOrder A h) →
      (restrictedOrder A = basisOrder A ↔ erdos_338.variants.eq_order.answer A) := by
  sorry

/--
Is it true that if $A \setminus F$ is a basis for all finite sets $F$ then $A$ must have a
restricted order?
-/
@[category research open, question, AMS 11]
theorem erdos_338.variants.basis_after_finite_removal :
    ∀ A : Set ℕ, (∀ F : Set ℕ, F.Finite → ∃ h, HasOrder (A \ F) h) →
      ∃ t, HasRestrictedOrder A t := by
  sorry

/--
Is it true that if the sets $A \setminus F$, for all finite sets $F$, are bases of the same order,
then $A$ must have a restricted order?

We read "the same order" literally: every $A \setminus F$ has the same exact order $h$. This is
equivalent to asking that the orders of the sets $A \setminus F$ are bounded. Removing elements can
only raise the order, so if the orders are bounded, their maximum is attained at some $F_0$, and
$A \setminus F_0 \subseteq A$ satisfies the literal hypothesis.
-/
@[category research open, question, AMS 11]
theorem erdos_338.variants.same_order_after_finite_removal :
    ∀ A : Set ℕ,
      (∃ h : ℕ, ∀ F : Set ℕ, F.Finite → basisOrder (A \ F) = (h : ℕ∞)) →
      ∃ t, HasRestrictedOrder A t := by
  sorry

/--
Bateman observed that for $h \geq 3$ the set $A = \{1\} \cup \{x > 0 : h \mid x\}$ is a basis of
order $h$ with no restricted order.
-/
@[category research solved, AMS 11]
theorem erdos_338.variants.bateman (h : ℕ) (hh : 3 ≤ h) :
    basisOrder (insert 1 {x : ℕ | 0 < x ∧ h ∣ x}) = h ∧
      ¬ ∃ t, HasRestrictedOrder (insert 1 {x : ℕ | 0 < x ∧ h ∣ x}) t := by
  sorry

section Kelly

/-!
### Kelly's theorem

The proof below is by contradiction. Suppose that infinitely many `n` are not sums of at most four
distinct elements of `A`, and compare a number `c` with `n - c` for such an `n` much larger than
`c`. This shows the following.
* A large odd element of `A` is not also a sum of two distinct elements of `A`
  (`KellySetup.unique`).
* If `o, e ∈ A` are odd and even with `o + e` large, then `o + e / 2 ∈ A` (`KellySetup.half`).
* Large odd elements of `A` are far apart (`KellySetup.lacunary`).

Applying `KellySetup.half` twice shows that large even elements of `A` are `2` modulo `4`
(`KellySetup.mod_four`). Then all odd elements of `A` are congruent modulo `4`, so one class of
odd numbers modulo `4` can only be reached with small even elements, which is impossible
(`KellySetup.end_`).
-/

/-- `m` is a sum of at most `k` distinct elements of `A`. -/
private def IsRSum (A : Set ℕ) (k m : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ k ∧ ∑ x ∈ S, x = m

@[category API, AMS 11]
private lemma IsRSum.le_four {A : Set ℕ} {k m n : ℕ} (h : IsRSum A k m) (hk : k ≤ 4)
    (hmn : m = n) : IsRSum A 4 n := by
  obtain ⟨S, hSA, hS, hSm⟩ := h
  exact ⟨S, hSA, hS.trans hk, hSm.trans hmn⟩

/-- Adding an element larger than `m` to a sum for `m`. -/
@[category API, AMS 11]
private lemma IsRSum.add {A : Set ℕ} {k m x : ℕ} (h : IsRSum A k m) (hx : x ∈ A) (hmx : m < x) :
    IsRSum A (k + 1) (m + x) := by
  obtain ⟨S, hSA, hS, rfl⟩ := h
  have hxS : x ∉ S := fun hxS ↦ by
    have := Finset.single_le_sum (f := fun i ↦ i) (fun i _ ↦ Nat.zero_le i) hxS
    omega
  refine ⟨insert x S, fun y hy ↦ ?_, ?_, ?_⟩
  · rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hx
    · exact hSA y hy
  · rw [Finset.card_insert_of_notMem hxS]
    omega
  · rw [Finset.sum_insert hxS, add_comm]

@[category API, AMS 11]
private lemma isRSum_one {A : Set ℕ} {a : ℕ} (ha : a ∈ A) : IsRSum A 1 a :=
  ⟨{a}, by simpa using ha, by simp, by simp⟩

@[category API, AMS 11]
private lemma isRSum_two {A : Set ℕ} {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    IsRSum A 2 (a + b) := by
  refine ⟨{a, b}, ?_, Finset.card_le_two, Finset.sum_pair hab⟩
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro x (rfl | rfl) <;> assumption

@[category API, AMS 11]
private lemma isRSum_three {A : Set ℕ} {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : IsRSum A 3 (a + b + c) := by
  refine ⟨{a, b, c}, ?_, Finset.card_le_three, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro x (rfl | rfl | rfl) <;> assumption
  · rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc, add_assoc]

@[category API, AMS 11]
private lemma isRSum_four {A : Set ℕ} {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hd : d ∈ A) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) : IsRSum A 4 (a + b + c + d) := by
  refine ⟨{a, b, c, d}, ?_, Finset.card_le_four, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro x (rfl | rfl | rfl | rfl) <;> assumption
  · rw [Finset.sum_insert (by simp [hab, hac, had]), Finset.sum_insert (by simp [hbc, hbd]),
      Finset.sum_pair hcd]
    ring

/-- The setting of Kelly's argument: `0 ∉ A`, every `m ≥ N` is in `A`, a sum of two distinct
elements of `A` or twice an element of `A`, and infinitely many `n` are not sums of at most four
distinct elements of `A`. -/
private structure KellySetup (A : Set ℕ) (N : ℕ) : Prop where
  zero : 0 ∉ A
  cover : ∀ m, N ≤ m → m ∈ A ∨ (∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ x + y = m) ∨ ∃ x ∈ A, x + x = m
  bad : ∀ M, ∃ n, M ≤ n ∧ ¬ IsRSum A 4 n

namespace KellySetup

variable {A : Set ℕ} {N : ℕ}

/-- An odd `m ≥ N` is in `A` or the sum of an odd and an even element of `A`. -/
@[category API, AMS 11]
private lemma cover_odd (H : KellySetup A N) {m : ℕ} (hm : N ≤ m) (hm2 : m % 2 = 1) :
    m ∈ A ∨ ∃ x ∈ A, ∃ y ∈ A, x % 2 = 1 ∧ y % 2 = 0 ∧ x + y = m := by
  rcases H.cover m hm with h | ⟨x, hx, y, hy, -, hxy⟩ | ⟨x, -, hxx⟩
  · exact .inl h
  · rcases Nat.mod_two_eq_zero_or_one x with h | h
    · exact .inr ⟨y, hy, x, hx, by omega, h, by omega⟩
    · exact .inr ⟨x, hx, y, hy, h, by omega, hxy⟩
  · omega

@[category API, AMS 11]
private lemma isRSum_odd (H : KellySetup A N) {m : ℕ} (hm : N ≤ m) (hm2 : m % 2 = 1) :
    IsRSum A 2 m := by
  rcases H.cover_odd hm hm2 with h | ⟨x, hx, y, hy, hx2, hy2, rfl⟩
  · obtain ⟨S, hSA, hS, hSm⟩ := isRSum_one h
    exact ⟨S, hSA, hS.trans (by norm_num), hSm⟩
  · exact isRSum_two hx hy (by omega)

/-- Arbitrarily large `n` that are not sums of at most four distinct elements of `A`. They are
even, since an odd `n ≥ N` is a sum of at most two distinct elements. -/
@[category API, AMS 11]
private lemma bad' (H : KellySetup A N) (M : ℕ) : ∃ n, M ≤ n ∧ n % 2 = 0 ∧ ¬ IsRSum A 4 n := by
  obtain ⟨n, hn, hbad⟩ := H.bad (M + N)
  refine ⟨n, by omega, ?_, hbad⟩
  by_contra h
  exact hbad ((H.isRSum_odd (m := n) (by omega) (by omega)).le_four (by norm_num) rfl)

/-- An odd `c ≥ N` in `A` is not also a sum of two distinct elements of `A`. -/
@[category API, AMS 11]
private lemma unique (H : KellySetup A N) {c x y : ℕ} (hc : c ∈ A) (hcN : N ≤ c)
    (hc2 : c % 2 = 1) (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) (hsum : x + y = c) : False := by
  obtain ⟨n, hn, hn2, hbad⟩ := H.bad' (3 * c + N + 1)
  have hx0 : x ≠ 0 := fun h ↦ H.zero (h ▸ hx)
  have hy0 : y ≠ 0 := fun h ↦ H.zero (h ▸ hy)
  rcases H.cover_odd (m := n - c) (by omega) (by omega) with h | ⟨p, hp, q, hq, hp2, hq2, hpq⟩
  · exact hbad (((isRSum_one hc).add h (by omega)).le_four (by norm_num) (by omega))
  · by_cases hpc : p = c
    -- `n = x + y + c + q` with `x, y < c < q`.
    · exact hbad ((isRSum_four hx hy hc hq hxy (by omega) (by omega) (by omega) (by omega)
        (by omega)).le_four le_rfl (by omega))
    · exact hbad ((isRSum_three hc hp hq (Ne.symm hpc) (by omega) (by omega)).le_four
        (by norm_num) (by omega))

/-- If `o, e ∈ A` are odd and even with `o + e ≥ N`, then `o + e / 2 ∈ A`. -/
@[category API, AMS 11]
private lemma half (H : KellySetup A N) {o e : ℕ} (ho : o ∈ A) (he : e ∈ A) (ho2 : o % 2 = 1)
    (he2 : e % 2 = 0) (hN : N ≤ o + e) : o + e / 2 ∈ A := by
  obtain ⟨n, hn, hn2, hbad⟩ := H.bad' (4 * (o + e) + N + 1)
  rcases H.cover_odd (m := n - (o + e)) (by omega) (by omega) with
    h | ⟨p, hp, q, hq, hp2, hq2, hpq⟩
  · exact (hbad ((isRSum_three ho he h (by omega) (by omega) (by omega)).le_four (by norm_num)
      (by omega))).elim
  · by_cases hpo : p = o
    -- `n = (2 * o + e) + q` with `q > 2 * o + e`, so `2 * o + e` is twice an element.
    · rcases H.cover (2 * o + e) (by omega) with h | ⟨x, hx, y, hy, hxy, hsum⟩ | ⟨x, hx, hxx⟩
      · exact (hbad (((isRSum_one h).add hq (by omega)).le_four (by norm_num)
          (by omega))).elim
      · exact (hbad (((isRSum_two hx hy hxy).add hq (by omega)).le_four (by norm_num)
          (by omega))).elim
      · convert hx using 1
        omega
    · by_cases hqe : q = e
      -- `n = (o + 2 * e) + p` with `p > o + 2 * e`.
      · exact (hbad (((H.isRSum_odd (m := o + 2 * e) (by omega) (by omega)).add hp
          (by omega)).le_four (by norm_num) (by omega))).elim
      · exact (hbad ((isRSum_four ho he hp hq (by omega) (Ne.symm hpo) (by omega) (by omega)
          (Ne.symm hqe) (by omega)).le_four le_rfl (by omega))).elim

/-- There are no odd `z < w` in `A` with `w + N ≤ 2 * z`. -/
@[category API, AMS 11]
private lemma lacunary (H : KellySetup A N) {z w : ℕ} (hz : z ∈ A) (hw : w ∈ A)
    (hz2 : z % 2 = 1) (hw2 : w % 2 = 1) (hzw : z < w) (hwz : w + N ≤ 2 * z) :
    False := by
  obtain ⟨n, hn, hn2, hbad⟩ := H.bad' (4 * z + N + 1)
  rcases H.cover_odd (m := n - z) (by omega) (by omega) with h | ⟨p, hp, q, hq, hp2, hq2, hpq⟩
  · exact hbad (((isRSum_one hz).add h (by omega)).le_four (by norm_num) (by omega))
  · by_cases hpz : p = z
    -- `n = (2 * z - w) + w + q` with `2 * z - w < w < q`.
    · have h := (H.isRSum_odd (m := 2 * z - w) (by omega) (by omega)).add hw (by omega)
      exact hbad ((h.add hq (by omega)).le_four le_rfl (by omega))
    · exact hbad ((isRSum_three hz hp hq (Ne.symm hpz) (by omega) (by omega)).le_four
        (by norm_num) (by omega))

/-- An even `e ∈ A` with `o + e ≥ N` for an odd `o ∈ A` is not divisible by `4`. -/
@[category API, AMS 11]
private lemma mod_four (H : KellySetup A N) {o e : ℕ} (ho : o ∈ A) (he : e ∈ A)
    (ho2 : o % 2 = 1) (he4 : e % 4 = 0) (hN : N ≤ o + e) : False := by
  have hz := H.half ho he ho2 (by omega) hN
  have hz' := H.half hz he (by omega) (by omega) (by omega)
  exact H.unique (c := o + e) (by convert hz' using 1; omega) hN (by omega) ho he (by omega) rfl

/-- The large odd numbers `≡ r (mod 4)` cannot all be sums `o + e` with an even `e < B`. -/
@[category API, AMS 11]
private lemma end_ (H : KellySetup A N) {B r : ℕ} (hr : r % 2 = 1) (hr4 : r < 4)
    (hB : ∀ o ∈ A, ∀ e ∈ A, o % 2 = 1 → e % 2 = 0 → (o + e) % 4 = r → e < B) : False := by
  by_cases hz : ∃ z ∈ A, z % 2 = 1 ∧ N + B + 4 ≤ z
  -- An odd `m ≡ r` just above `z + B` is too close to `z`.
  · obtain ⟨z, hz, hz2, hzN⟩ := hz
    obtain ⟨m, hm4, hm1, hm2⟩ : ∃ m, m % 4 = r ∧ z + B < m ∧ m ≤ z + B + 4 :=
      ⟨z + B + 1 + (r + 4 - (z + B + 1) % 4) % 4, by omega, by omega, by omega⟩
    rcases H.cover_odd (m := m) (by omega) (by omega) with h | ⟨x, hx, y, hy, hx2, hy2, hxy⟩
    · exact H.lacunary hz h hz2 (by omega) (by omega) (by omega)
    · have := hB x hx y hy hx2 hy2 (by omega)
      exact H.lacunary hz hx hz2 hx2 (by omega) (by omega)
  -- All odd elements are small, so a large odd `m ≡ r` is not reached.
  · push Not at hz
    rcases H.cover_odd (m := 4 * (N + B + 4) + r) (by omega) (by omega) with
      h | ⟨x, hx, y, hy, hx2, hy2, hxy⟩
    · have := hz _ h (by omega)
      omega
    · have := hB x hx y hy hx2 hy2 (by omega)
      have := hz x hx hx2
      omega

@[category API, AMS 11]
private lemma false (H : KellySetup A N) : False := by
  obtain ⟨o₀, ho₀, ho₀2⟩ : ∃ o ∈ A, o % 2 = 1 := by
    rcases H.cover_odd (m := 2 * N + 1) (by omega) (by omega) with h | ⟨x, hx, -, -, hx2, -, -⟩
    · exact ⟨_, h, by omega⟩
    · exact ⟨x, hx, hx2⟩
  by_cases hE : ∃ e ∈ A, e % 2 = 0 ∧ 2 * N ≤ e
  · obtain ⟨e, he, he2, heN⟩ := hE
    -- Every odd `o ∈ A` has `o + e / 2 ≡ 2 (mod 4)`, so all odd elements are congruent mod `4`.
    have key : ∀ o ∈ A, o % 2 = 1 → (o + e / 2) % 4 = 2 := by
      intro o ho ho2
      have he4 : e % 4 = 2 := by
        by_contra h
        exact H.mod_four ho he ho2 (by omega) (by omega)
      have hw := H.half ho he ho2 he2 (by omega)
      by_contra h
      exact H.mod_four ho hw ho2 (by omega) (by omega)
    refine H.end_ (B := N) (r := o₀ % 4) (by omega) (by omega) fun o ho f hf ho2 hf2 hr ↦ ?_
    by_contra hfN
    have h1 := key o ho ho2
    have h2 := key o₀ ho₀ ho₀2
    exact H.mod_four ho hf ho2 (by omega) (by omega)
  · push Not at hE
    exact H.end_ (B := 2 * N) (r := 1) (by omega) (by omega) fun _ _ f hf _ hf2 _ ↦ hE f hf hf2

end KellySetup

end Kelly

/--
Kelly [Ke57] showed that any basis of order $2$ has restricted order at most $4$.
-/
@[category research solved, AMS 11]
theorem erdos_338.variants.kelly (A : Set ℕ) (hA : HasOrder A 2) : HasRestrictedOrder A 4 := by
  by_contra hR
  unfold HasRestrictedOrder at hR
  obtain ⟨N, hN⟩ := eventually_atTop.1 hA
  -- Work with the positive elements of `A`; a summand `0` is never needed.
  refine KellySetup.false (A := {x | x ∈ A ∧ x ≠ 0}) (N := N + 1) ⟨fun h ↦ h.2 rfl, ?_, ?_⟩
  · intro m hm
    obtain ⟨S, hSA, hS2, rfl⟩ := hN m (by omega)
    simp only [Set.mem_ofPred_eq]
    obtain h | h | h : Multiset.card S = 0 ∨ Multiset.card S = 1 ∨ Multiset.card S = 2 := by
      omega
    · simp [Multiset.card_eq_zero.1 h] at hm
    · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 h
      simp only [Multiset.sum_singleton] at hm ⊢
      exact .inl ⟨hSA a (by simp), by omega⟩
    · obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 h
      have hx : x ∈ A := hSA x (by simp)
      have hy : y ∈ A := hSA y (by simp)
      simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at hm ⊢
      rcases Nat.eq_zero_or_pos x with rfl | hx0
      · exact .inl ⟨by simpa using hy, by omega⟩
      rcases Nat.eq_zero_or_pos y with rfl | hy0
      · exact .inl ⟨by simpa using hx, by omega⟩
      by_cases hxy : x = y
      · exact .inr (.inr ⟨x, ⟨hx, by omega⟩, by omega⟩)
      · exact .inr (.inl ⟨x, ⟨hx, by omega⟩, y, ⟨hy, by omega⟩, hxy, rfl⟩)
  · intro M
    obtain ⟨n, hn, hbad⟩ := frequently_atTop.1 (not_eventually.1 hR) M
    exact ⟨n, hn, fun ⟨S, hSB, hS⟩ ↦ hbad ⟨S, fun x hx ↦ (hSB x hx : x ∈ A ∧ x ≠ 0).1, hS⟩⟩

/--
Kelly [Ke57] showed that any basis of order $2$ with positive lower density has restricted order
at most $3$.
-/
@[category research solved, AMS 11]
theorem erdos_338.variants.kelly_lowerDensity (A : Set ℕ) (hA : HasOrder A 2)
    (hd : 0 < A.lowerDensity) : HasRestrictedOrder A 3 := by
  sorry

/--
Kelly [Ke57] conjectured that any basis of order $2$ has restricted order at most $3$.

This was disproved by Hennecart [He05], who constructed a basis of order $2$ with restricted
order $4$.
-/
@[category research solved, question, AMS 11]
theorem erdos_338.variants.kelly_conjecture :
    ¬ ∀ A : Set ℕ, HasOrder A 2 → HasRestrictedOrder A 3 := by
  sorry

/--
The set of squares has order $4$ and restricted order $5$ (see [Pa33]).

Here $0$ is a square. The order is $4$ by Lagrange's four-square theorem, and is not $3$ because
no integer $\equiv 7 \pmod 8$ is a sum of three squares.
-/
@[category research solved, AMS 11]
theorem erdos_338.variants.squares :
    basisOrder (Set.range fun k : ℕ ↦ k ^ 2) = 4 ∧
      restrictedOrder (Set.range fun k : ℕ ↦ k ^ 2) = 5 := by
  sorry

/--
The set of triangular numbers has order $3$ and restricted order $3$ (see [Sc54]).

Here $0$ is a triangular number.
-/
@[category research solved, AMS 11]
theorem erdos_338.variants.triangular :
    basisOrder (Set.range fun k : ℕ ↦ k * (k + 1) / 2) = 3 ∧
      restrictedOrder (Set.range fun k : ℕ ↦ k * (k + 1) / 2) = 3 := by
  sorry

/--
Hegyvári, Hennecart and Plagne [HHP07] showed that for all $k \geq 2$ there exists a basis of
order $k$ which has restricted order at least $2^{k-2}+k-1$.

The basis built in the proof of Theorem 4 of [HHP07] (for $k \geq 3$) has order exactly $k$ and a
finite restricted order, equal to $2^{k-2}+k-1$. The finiteness matters: without it, Bateman's
example `Erdos338.erdos_338.variants.bateman` would already give the bound. For $k = 2$ the bound
is $2$, and $A = \{1\} \cup \{x : 2 \mid x\}$ works.
-/
@[category research solved, AMS 11]
theorem erdos_338.variants.hegyvari_hennecart_plagne :
    ∀ k : ℕ, 2 ≤ k → ∃ A : Set ℕ,
      basisOrder A = k ∧ restrictedOrder A = (2 ^ (k - 2) + k - 1 : ℕ) := by
  sorry

end Erdos338
