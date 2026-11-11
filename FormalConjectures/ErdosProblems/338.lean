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
If $A \setminus F$ is a basis for every finite set $F$ and $A$ has positive lower density, then
$A$ has a restricted order. So `Erdos338.erdos_338.variants.basis_after_finite_removal` has a
positive answer for sets of positive lower density.

This was shown by Daniel Veljjanoski on the
[forum](https://www.erdosproblems.com/forum/thread/338#post-9251) (1 October 2026), with the
bound $3\lceil 8/\delta^2\rceil - 2$ on the restricted order, where $\delta$ is the lower density
of $A$. The linked formalisation proves the existence of a restricted order, not this bound.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-03-000016"]
theorem erdos_338.variants.lowerDensity_pos :
    ∀ A : Set ℕ, (∀ F : Set ℕ, F.Finite → ∃ h, HasOrder (A \ F) h) → 0 < A.lowerDensity →
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

/--
Kelly [Ke57] showed that any basis of order $2$ has restricted order at most $4$.
-/
@[category research solved, AMS 11]
theorem erdos_338.variants.kelly (A : Set ℕ) (hA : HasOrder A 2) : HasRestrictedOrder A 4 := by
  sorry

/--
Kelly [Ke57] showed that any basis of order $2$ with positive lower density has restricted order
at most $3$.
-/
@[category research solved, AMS 11]
theorem erdos_338.variants.kelly_lowerDensity (A : Set ℕ) (hA : HasOrder A 2)
    (hd : 0 < A.lowerDensity) : HasRestrictedOrder A 3 := by
  sorry

section KellyConjecture

/-- `Ternary01 a` means that all base-$3$ digits of $a$ are $0$ or $1$. -/
private inductive Ternary01 : ℕ → Prop
  | zero : Ternary01 0
  | three {a : ℕ} : Ternary01 a → Ternary01 (3 * a)
  | three_add_one {a : ℕ} : Ternary01 a → Ternary01 (3 * a + 1)

/-- The last base-$3$ digit of `a` is $0$ or $1$, and removing it gives a `Ternary01` number. -/
@[category API, AMS 11]
private lemma Ternary01.mod_div {a : ℕ} (h : Ternary01 a) : a % 3 ≤ 1 ∧ Ternary01 (a / 3) := by
  cases h with
  | zero => exact ⟨by norm_num, by rw [Nat.zero_div]; exact .zero⟩
  | @three a h => exact ⟨by omega, by rwa [show 3 * a / 3 = a by omega]⟩
  | @three_add_one a h => exact ⟨by omega, by rwa [show (3 * a + 1) / 3 = a by omega]⟩

/-- Every natural number is `a + b` with `a` and `b` in `Ternary01`. -/
@[category API, AMS 11]
private lemma Ternary01.exists_add (k : ℕ) : ∃ a b, Ternary01 a ∧ Ternary01 b ∧ a + b = k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨0, 0, .zero, .zero, rfl⟩
    obtain ⟨a, b, ha, hb, hab⟩ := ih (k / 3) (by omega)
    rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
    · exact ⟨3 * a, 3 * b, ha.three, hb.three, by omega⟩
    · exact ⟨3 * a + 1, 3 * b, ha.three_add_one, hb.three, by omega⟩
    · exact ⟨3 * a + 1, 3 * b + 1, ha.three_add_one, hb.three_add_one, by omega⟩

/-- Every natural number is `a + 2 * c` with `a` and `c` in `Ternary01`. -/
@[category API, AMS 11]
private lemma Ternary01.exists_add_two_mul (k : ℕ) :
    ∃ a c, Ternary01 a ∧ Ternary01 c ∧ a + 2 * c = k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨0, 0, .zero, .zero, rfl⟩
    obtain ⟨a, c, ha, hc, hac⟩ := ih (k / 3) (by omega)
    rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
    · exact ⟨3 * a, 3 * c, ha.three, hc.three, by omega⟩
    · exact ⟨3 * a + 1, 3 * c, ha.three_add_one, hc.three, by omega⟩
    · exact ⟨3 * a, 3 * c + 1, ha.three, hc.three_add_one, by omega⟩

/-- If `a`, `b` and `c` are in `Ternary01` and `a + b + 2 * c = 3 ^ j - 1`, then `a = b`. All
base-$3$ digits of $3^j-1$ are $2$, and comparing last digits shows that `a` and `b` have the
same last digit. -/
@[category API, AMS 11]
private lemma Ternary01.eq_of_add {a b c : ℕ} (ha : Ternary01 a) (hb : Ternary01 b)
    (hc : Ternary01 c) (j : ℕ) (h : a + b + 2 * c + 1 = 3 ^ j) : a = b := by
  induction j generalizing a b c with
  | zero => rw [pow_zero] at h; omega
  | succ j ih =>
    obtain ⟨ha3, ha'⟩ := ha.mod_div
    obtain ⟨hb3, hb'⟩ := hb.mod_div
    obtain ⟨hc3, hc'⟩ := hc.mod_div
    rw [pow_succ] at h
    have := ih ha' hb' hc' (by omega)
    omega

/-- The numbers `2 * a + 1` and `4 * a` with `a` in `Ternary01`. -/
private def ternaryBasis : Set ℕ := {m | ∃ a, Ternary01 a ∧ (m = 2 * a + 1 ∨ m = 4 * a)}

@[category API, AMS 11]
private lemma mem_ternaryBasis {m : ℕ} :
    m ∈ ternaryBasis ↔ ∃ a, Ternary01 a ∧ (m = 2 * a + 1 ∨ m = 4 * a) :=
  Iff.rfl

/-- Every positive integer is a sum of at most two elements of `ternaryBasis`. -/
@[category API, AMS 11]
private lemma hasOrder_ternaryBasis : HasOrder ternaryBasis 2 := by
  unfold HasOrder
  refine eventually_atTop.2 ⟨1, fun m hm ↦ ?_⟩
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · obtain ⟨a, b, ha, hb, hab⟩ := Ternary01.exists_add (k - 1)
    refine ⟨{2 * a + 1, 2 * b + 1}, ?_, by simp, ?_⟩
    · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
      rintro x (rfl | rfl)
      exacts [mem_ternaryBasis.2 ⟨a, ha, .inl rfl⟩, mem_ternaryBasis.2 ⟨b, hb, .inl rfl⟩]
    · simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
      omega
  · obtain ⟨a, c, ha, hc, rfl⟩ := Ternary01.exists_add_two_mul k
    refine ⟨{2 * a + 1, 4 * c}, ?_, by simp, ?_⟩
    · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
      rintro x (rfl | rfl)
      exacts [mem_ternaryBasis.2 ⟨a, ha, .inl rfl⟩, mem_ternaryBasis.2 ⟨c, hc, .inr rfl⟩]
    · simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
      omega

/-- `ternaryBasis` has no restricted order $3$: no number `2 * 3 ^ j` is a sum of at most three
distinct elements of `ternaryBasis`. -/
@[category API, AMS 11]
private lemma not_hasRestrictedOrder_ternaryBasis : ¬ HasRestrictedOrder ternaryBasis 3 := by
  intro hR
  unfold HasRestrictedOrder at hR
  obtain ⟨N, hN⟩ := eventually_atTop.1 hR
  obtain ⟨S, hSA, hS3, hSsum⟩ :=
    hN (2 * 3 ^ N) (by have := Nat.lt_pow_self (n := N) (by norm_num : 1 < 3); omega)
  have hP : 3 ^ N % 2 = 1 := Nat.odd_iff.1 (Odd.pow (by decide))
  interval_cases h : S.card
  · rw [Finset.card_eq_zero.1 h, Finset.sum_empty] at hSsum
    omega
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 h
    rw [Finset.sum_singleton] at hSsum
    obtain ⟨a, ha, rfl | rfl⟩ := mem_ternaryBasis.1 (hSA x (by simp)) <;> omega
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 h
    rw [Finset.sum_pair hxy] at hSsum
    obtain ⟨a, ha, rfl | rfl⟩ := mem_ternaryBasis.1 (hSA x (by simp)) <;>
      obtain ⟨b, hb, rfl | rfl⟩ := mem_ternaryBasis.1 (hSA y (by simp)) <;>
      first
      | omega
      | (have := ha.eq_of_add hb .zero N (by omega); omega)
  · obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 h
    rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_pair hyz] at hSsum
    obtain ⟨a, ha, rfl | rfl⟩ := mem_ternaryBasis.1 (hSA x (by simp)) <;>
      obtain ⟨b, hb, rfl | rfl⟩ := mem_ternaryBasis.1 (hSA y (by simp)) <;>
      obtain ⟨c, hc, rfl | rfl⟩ := mem_ternaryBasis.1 (hSA z (by simp)) <;>
      first
      | omega
      | (have := ha.eq_of_add hb hc N (by omega); omega)
      | (have := ha.eq_of_add hc hb N (by omega); omega)
      | (have := hb.eq_of_add hc ha N (by omega); omega)

end KellyConjecture

/--
Kelly [Ke57] conjectured that any basis of order $2$ has restricted order at most $3$.

This was disproved by Hennecart [He05], who constructed a basis of order $2$ with restricted
order $4$.
-/
@[category research solved, question, AMS 11]
theorem erdos_338.variants.kelly_conjecture :
    ¬ ∀ A : Set ℕ, HasOrder A 2 → HasRestrictedOrder A 3 :=
  fun h ↦ not_hasRestrictedOrder_ternaryBasis (h _ hasOrder_ternaryBasis)

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
