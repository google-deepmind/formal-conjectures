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
# Erdős Problem 539

In this problem, a function $h : \mathbb{N} \to\mathbb{N}$ is defined maximally by a specified
counting property.

The problem asks to estimate $h(n)$. This has been interpreted here as asking for $\Theta(h(n))$.
The principal version includes the unknown function `erdos_539.answer`. On the other hand, the best
known upper bound is $n^{2/3}$ and the best known lower bound is $\sqrt{n}$ so we
also provide these candidates as variants. Moreover, it suffices to show $O(h(n))$ and
$O(\sqrt{n})$ respectively for each, so further variants are provided for those.

In the source paper [Er73], Erdős also remarks that it should not be too difficult
to determine $\lim_{n\to\infty}\log(h(n))/\log(n)$. This does not appear on the website, and
it is not clear whether this remains open, but we include it here either way.

*References:*
- [erdosproblems.com/539](https://www.erdosproblems.com/539)
- [GR99] Granville, A., & Roesler, F. (1999). _The Set of Differences of a Given Set_. The American Mathematical Monthly, 106(4), 338–344.
- [Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971) (1973), 117-138.
- [Sc+26] Schmitt, J., Gehrunger, T., Dekoninck, J., Bérczi, G., Kreitner, U., Price, L., & Holmes, D. (2026). _ProofCouncil: An LLM Agent for Solving Open Mathematical Problems_. [arXiv:2607.09474](https://arxiv.org/abs/2607.09474), Appendix A, Theorem A.1.
-/

@[expose] public section

open Filter

open scoped Asymptotics Finset

namespace Erdos539

/-- We say that $m$ is a cofactor lower bound for a given $n$ if, for every set $A$ of $n$
non-negative integers, there are at least $m$ cofactors $a / (a, b)$, where $a, b\in A$.-/
def IsCofactorLowerBound (n m : ℕ) : Prop := ∀ A : Finset ℕ, #A = n →
  m ≤ #((A ×ˢ A).image fun (a, b) ↦ a / a.gcd b)

/-- The cofactor threshold $h(n)$, for every positive $n$, is the largest cofactor lower bound
for $n$. -/
noncomputable def cofactorThreshold (n : ℕ) : ℕ :=
  sSup {m | IsCofactorLowerBound n m}

def erdos_539.answer : ℕ → ℝ := sorry

/-- Key injectivity argument: fixing a positive $a \in A$, the map $b \mapsto (a/(a,b), b/(a,b))$
is injective, so $|A| \le |D|^2$ where $D$ is the set of cofactors. -/
lemma card_le_sq_card_cofactors (A : Finset ℕ) {a : ℕ} (ha : a ∈ A) (hpos : 0 < a) :
    #A ≤ #((A ×ˢ A).image fun (a, b) ↦ a / a.gcd b) ^ 2 := by
  set D := (A ×ˢ A).image fun (a, b) ↦ a / a.gcd b with hD
  have hmem : ∀ x ∈ A, ∀ y ∈ A, x / x.gcd y ∈ D := fun x hx y hy =>
    Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hx, hy⟩, rfl⟩
  let f : ℕ → ℕ × ℕ := fun b ↦ (a / a.gcd b, b / b.gcd a)
  have hmaps : ∀ b ∈ A, f b ∈ D ×ˢ D := fun b hb =>
    Finset.mem_product.2 ⟨hmem a ha b hb, hmem b hb a ha⟩
  have hinj : Set.InjOn f A := by
    intro b _ c _ hbc
    simp only [f, Prod.mk.injEq] at hbc
    obtain ⟨h1, h2⟩ := hbc
    have hg : a.gcd b = a.gcd c := by
      rw [← Nat.div_div_self (Nat.gcd_dvd_left a b) hpos.ne',
        ← Nat.div_div_self (Nat.gcd_dvd_left a c) hpos.ne', h1]
    rw [Nat.gcd_comm b a, Nat.gcd_comm c a, hg] at h2
    rw [← Nat.div_mul_cancel (Nat.gcd_dvd_right a b), hg, h2,
      Nat.div_mul_cancel (Nat.gcd_dvd_right a c)]
  calc #A ≤ #(D ×ˢ D) := Finset.card_le_card_of_injOn f hmaps hinj
    _ = #D ^ 2 := by rw [Finset.card_product, sq]

/-- Lower bound: $\lfloor\sqrt n\rfloor$ is always a lower bound for the number of cofactors
(the Erdős–Szemerédi lower bound). -/
lemma isCofactorLowerBound_sqrt (n : ℕ) : IsCofactorLowerBound n (Nat.sqrt n) := by
  intro A hA
  set D := (A ×ˢ A).image fun (a, b) ↦ a / a.gcd b with hD
  by_cases h : ∃ a ∈ A, 0 < a
  · obtain ⟨a, ha, hpos⟩ := h
    have h1 := card_le_sq_card_cofactors A ha hpos
    have h2 := Nat.sqrt_le' n
    rw [hA] at h1
    exact (Nat.pow_le_pow_iff_left two_ne_zero).1 (h2.trans h1)
  · simp only [not_exists, not_and, not_lt] at h
    have hsub : A ⊆ {0} := fun x hx => by
      simpa using Nat.le_zero.1 (h x hx)
    have hn : n ≤ 1 := hA ▸ (Finset.card_le_card hsub).trans (by simp)
    refine (Nat.sqrt_le_self n).trans ?_
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with rfl | rfl
    · exact Nat.zero_le _
    · obtain ⟨x, hx⟩ := Finset.card_pos.1 (by omega : 0 < #A)
      exact Finset.card_pos.2 ⟨x / x.gcd x,
        Finset.mem_image.2 ⟨(x, x), Finset.mem_product.2 ⟨hx, hx⟩, rfl⟩⟩

/-- Upper bound: the cofactors of $\{1,2,\dots,2^{n-1}\}$ lie in the set itself, so a lower bound
for the number of cofactors cannot exceed $n$. -/
lemma le_of_isCofactorLowerBound {n m : ℕ} (h : IsCofactorLowerBound n m) : m ≤ n := by
  set A := (Finset.range n).image (2 ^ ·) with hA
  have hcard : #A = n := by
    rw [hA, Finset.card_image_of_injective _ (Nat.pow_right_injective le_rfl),
      Finset.card_range]
  refine (h A hcard).trans (hcard ▸ Finset.card_le_card ?_)
  intro d hd
  obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.1 hd
  obtain ⟨hx, -⟩ := Finset.mem_product.1 hxy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
  have hdvd : 2 ^ i / (2 ^ i).gcd y ∣ 2 ^ i := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  show 2 ^ i / (2 ^ i).gcd y ∈ A
  rw [hk']
  exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 (lt_of_le_of_lt hk (Finset.mem_range.1 hi)),
    rfl⟩

lemma bddAbove_isCofactorLowerBound (n : ℕ) : BddAbove {m | IsCofactorLowerBound n m} :=
  ⟨n, fun _ hm => le_of_isCofactorLowerBound hm⟩

/-- $\lfloor\sqrt n\rfloor \le h(n)$. -/
lemma sqrt_le_cofactorThreshold (n : ℕ) : Nat.sqrt n ≤ cofactorThreshold n :=
  le_csSup (bddAbove_isCofactorLowerBound n) (isCofactorLowerBound_sqrt n)

/-- $h(n) \le n$. -/
lemma cofactorThreshold_le (n : ℕ) : cofactorThreshold n ≤ n :=
  csSup_le ⟨_, isCofactorLowerBound_sqrt n⟩ fun _ hm => le_of_isCofactorLowerBound hm

/-- $h(n)$ itself is a lower bound (the maximum is attained). -/
lemma isCofactorLowerBound_cofactorThreshold (n : ℕ) :
    IsCofactorLowerBound n (cofactorThreshold n) :=
  Nat.sSup_mem ⟨_, isCofactorLowerBound_sqrt n⟩ (bddAbove_isCofactorLowerBound n)

/-- $\sqrt n \ll h(n)$ (formalisation of the Erdős–Szemerédi lower bound). -/
lemma sqrt_isBigO_cofactorThreshold :
    (fun n : ℕ ↦ √n) =O[atTop] fun n ↦ (cofactorThreshold n : ℝ) := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hs : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.2 hn
  have hlt : (n : ℝ) ≤ ((Nat.sqrt n : ℝ) + 1) ^ 2 := by
    exact_mod_cast (Nat.lt_succ_sqrt' n).le
  have h1 : √(n : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (Nat.sqrt n : ℝ) + 1)]
    exact Real.sqrt_le_sqrt hlt
  have h2 : (Nat.sqrt n : ℝ) ≤ cofactorThreshold n := by
    exact_mod_cast sqrt_le_cofactorThreshold n
  have h3 : (1 : ℝ) ≤ Nat.sqrt n := by exact_mod_cast hs
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  linarith

/-- $h(n) \ll n$ (the trivial upper bound). -/
lemma cofactorThreshold_isBigO_id :
    (fun n ↦ (cofactorThreshold n : ℝ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) := by
  refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul]
  exact_mod_cast cofactorThreshold_le n

/-- Let $h(n)$ be maximal such that, for any set $A\subseteq \mathbb{N}$ of size $n$, the
set$$\left\{ \frac{a}{(a,b)}: a,b\in A\right\}$$has size at least $h(n)$. Estimate $h(n)$. -/
@[category research open, question value, AMS 5 11]
theorem erdos_539 :
    (fun n ↦ (cofactorThreshold n : ℝ)) =Θ[atTop] erdos_539.answer := by
  sorry

/-- Let $h(n)$ be maximal such that, for any set $A\subseteq \mathbb{N}$ of size $n$, the
set$$\left\{ \frac{a}{(a,b)}: a,b\in A\right\}$$has size at least $h(n)$.
Is $h(n) = \Theta(\sqrt{n})$? -/
@[category research solved, question, AMS 5 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/erdos-539-sqrt-disproof/blob/f4b14f9ef32c111162d3fd587e1c65b27a1524d5/lean/Erdos539SqrtFC.lean#L41-L44"]
theorem erdos_539.variants.sq :
    ¬ ((fun n ↦ (cofactorThreshold n : ℝ)) =Θ[atTop] fun n ↦ √n) := by
  sorry

/-- Erdős and Szemerédi proved that$$n^{1/2} \ll h(n)$$. -/
@[category research solved, AMS 5 11]
theorem erdos_539.variants.sq_isBigO :
    (fun n : ℕ ↦ √n) =O[atTop] fun n ↦ (cofactorThreshold n : ℝ) := by
  exact sqrt_isBigO_cofactorThreshold

/-- Is $h(n) = O(\sqrt{n})$? -/
@[category research solved, question, AMS 5 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/erdos-539-sqrt-disproof/blob/f4b14f9ef32c111162d3fd587e1c65b27a1524d5/lean/Erdos539SqrtFC.lean#L36-L39"]
theorem erdos_539.variants.isBigO_sq :
    ¬ ((fun n ↦ (cofactorThreshold n : ℝ)) =O[atTop] fun n ↦ √n) := by
  sorry

/-- Let $h(n)$ be maximal such that, for any set $A\subseteq \mathbb{N}$ of size $n$, the
set$$\left\{ \frac{a}{(a,b)}: a,b\in A\right\}$$has size at least $h(n)$.
Is $h(n) = \Theta(n^{2/3})$?
The answer is negative; see [Sc+26, Theorem A.1] and the linked Lean proof. -/
@[category research solved, question, AMS 5 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/erdos-539-formal-conjectures/blob/79897cf9241390eb168572f4a481e29e0e64b5f7/lean/Erdos539/FC.lean#L282-L296"]
theorem erdos_539.variants.sq_cube_root :
    ¬ ((fun n ↦ (cofactorThreshold n : ℝ)) =Θ[atTop]
      fun n ↦ (n : ℝ) ^ ((2 : ℝ) / 3)) := by
  sorry

/-- Granville and Roesler [GR99] showed that $$h(n)\ll n^{2/3}$$.-/
@[category research solved, AMS 5 11]
theorem erdos_539.variants.isBigO_sq_cube_root :
    (fun n ↦ (cofactorThreshold n : ℝ)) =O[atTop] fun n ↦ (n : ℝ) ^ ((2 : ℝ) / 3) := by
  sorry

/-- This lower bound is false; see [Sc+26, Theorem A.1] and the linked Lean proof. -/
@[category research solved, question, AMS 5 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/erdos-539-formal-conjectures/blob/79897cf9241390eb168572f4a481e29e0e64b5f7/lean/Erdos539/FC.lean#L282-L296"]
theorem erdos_539.variants.sq_cube_root_isBigO :
    ¬ ((fun n : ℕ ↦ (n : ℝ) ^ ((2 : ℝ) / 3)) =O[atTop]
      fun n ↦ (cofactorThreshold n : ℝ)) := by
  sorry

noncomputable def erdos_539.variants.limit.answer : Filter ℝ := nhds ((1 : ℝ) / 2)

/-- From [Er73]: The determination of
$$
  \lim_{n\to\infty}\frac{\log(h(n))}{\log(n)}
$$
will perhaps be not too difficult.
The limit is $1/2$; see [Sc+26, Theorem A.1] and the linked Lean proof.
-/
@[category research solved, question value, AMS 5 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/erdos-539-formal-conjectures/blob/79897cf9241390eb168572f4a481e29e0e64b5f7/lean/Erdos539/FC.lean#L282-L296"]
theorem erdos_539.variants.limit :
    atTop.Tendsto
      (fun n ↦ Real.log (cofactorThreshold n) / Real.log n)
      erdos_539.variants.limit.answer := by
  sorry

end Erdos539
