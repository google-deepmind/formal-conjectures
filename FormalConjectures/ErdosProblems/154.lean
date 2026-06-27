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
# Erdős Problem 154

*References:*
- [erdosproblems.com/154](https://www.erdosproblems.com/154)
- [Li98] Lindström, Bernt, *Well distribution of Sidon sets in residue classes*.
  J. Number Theory (1998), 197-200.
- [Ko99] Kolountzakis, Mihail N., *On the uniform distribution in residue classes of dense sets
  of integers with distinct sums*. J. Number Theory (1999), 147-153.
- [ESS94] Erdős, P. and Sárközy, A. and Sós, T., *On Sum Sets of Sidon Sets, I*.
  Journal of Number Theory (1994), 329-347.
-/

open Filter Finset

open scoped Pointwise

namespace Erdos154

/--
Let $A\subset \{1,\ldots,N\}$ be a Sidon set with $\lvert A\rvert\sim N^{1/2}$. Must $A+A$ be
well-distributed over all small moduli? In particular, must about half the elements of $A+A$ be
even and half odd?

The answer is yes. Lindström [Li98] proved the analogous statement for $A$ itself (see
`erdos_154.variants.lindstrom`), later strengthened by Kolountzakis [Ko99]; well-distribution of
$A+A$ then follows using the Sidon property.

We state the question for the sumset: for any sequence of Sidon sets
$A_k\subseteq\{0,\ldots,N_k\}$ with $N_k\to\infty$ and $\lvert A_k\rvert\sim N_k^{1/2}$, and any
modulus $m\geq 2$, the proportion of elements of $A_k+A_k$ congruent to $i\pmod m$ (i.e. the count
divided by $\lvert A_k+A_k\rvert$) tends to $1/m$ for every residue $i<m$.
-/
@[category research solved, AMS 5 11]
theorem erdos_154 : answer(True) ↔
    ∀ (m : ℕ) (hm : 2 ≤ m) (N : ℕ → ℕ) (A : ℕ → Finset ℕ),
      Tendsto (fun k => (N k : ℝ)) atTop atTop →
      (∀ k, ∀ x ∈ A k, x ≤ N k) →
      (∀ k, IsSidon (A k : Set ℕ)) →
      Tendsto (fun k => ((A k).card : ℝ) / Real.sqrt (N k)) atTop (nhds 1) →
      ∀ i < m, Tendsto
        (fun k => (((A k + A k).filter (fun s => s % m = i)).card : ℝ) / ((A k + A k).card : ℝ))
        atTop (nhds (1 / m)) := by
  sorry

/--
Lindström's result for $A$ itself [Li98], later strengthened by Kolountzakis [Ko99]: for any
sequence of Sidon sets $A_k\subseteq\{0,\ldots,N_k\}$ with $N_k\to\infty$ and
$\lvert A_k\rvert\sim N_k^{1/2}$, and any modulus $m\geq 2$, the number of elements of $A_k$
congruent to $i\pmod m$, divided by $N_k^{1/2}$, tends to $1/m$ for every residue $i<m$.

Well-distribution of $A+A$ (the actual question, `erdos_154`) follows from this using the Sidon
property.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/Woett/Lean-files/blob/main/ErdosProblem154.lean"]
theorem erdos_154.variants.lindstrom :
    ∀ (m : ℕ) (hm : 2 ≤ m) (N : ℕ → ℕ) (A : ℕ → Finset ℕ),
      Tendsto (fun k => (N k : ℝ)) atTop atTop →
      (∀ k, ∀ x ∈ A k, x ≤ N k) →
      (∀ k, IsSidon (A k : Set ℕ)) →
      Tendsto (fun k => ((A k).card : ℝ) / Real.sqrt (N k)) atTop (nhds 1) →
      ∀ i < m, Tendsto
        (fun k => (((A k).filter (fun a => a % m = i)).card : ℝ) / Real.sqrt (N k))
        atTop (nhds (1 / m)) := by
  sorry

private def sym2Add : Sym2 ℕ → ℕ :=
  Sym2.lift ⟨fun a b : ℕ => a + b, fun a b => Nat.add_comm a b⟩

@[simp]
private lemma sym2Add_mk (a b : ℕ) : sym2Add s(a, b) = a + b := rfl

private lemma sidon_injOn_sym2Add {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) :
    Set.InjOn sym2Add (A.sym2 : Set (Sym2 ℕ)) := by
  intro x hx y hy hxy
  induction x using Sym2.ind with
  | h a b =>
    induction y using Sym2.ind with
    | h c d =>
      rw [sym2Add_mk, sym2Add_mk] at hxy
      have hab : a ∈ A ∧ b ∈ A :=
        (Finset.mk_mem_sym2_iff (s := A) (a := a) (b := b)).1 hx
      have hcd : c ∈ A ∧ d ∈ A :=
        (Finset.mk_mem_sym2_iff (s := A) (a := c) (b := d)).1 hy
      rcases hA a hab.1 c hcd.1 b hab.2 d hcd.2 hxy with h | h
      · rw [Sym2.eq_iff]
        exact Or.inl ⟨h.1, h.2⟩
      · rw [Sym2.eq_iff]
        exact Or.inr ⟨h.1, h.2⟩

private lemma image_sym2Add_sym2 (A : Finset ℕ) :
    A.sym2.image sym2Add = A + A := by
  rw [Finset.sym2_eq_image]
  rw [Finset.image_image]
  exact Finset.image_add_product

lemma card_sumset_sidon {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) :
    2 * (A + A).card = A.card * A.card + A.card := by
  rw [← image_sym2Add_sym2 A]
  rw [Finset.card_image_of_injOn (sidon_injOn_sym2Add (A := A) hA)]
  rw [Finset.card_sym2]
  have h : (A.card + 1) * A.card = Nat.choose (A.card + 1) 2 * 2 := by
    simpa using Nat.add_one_mul_choose_eq A.card 1
  rw [Nat.mul_comm 2]
  rw [← h]
  ring

lemma card_sumset_filter_sidon {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) (m i : ℕ) :
    ((A + A).filter (fun s => s % m = i)).card =
      (A.sym2.filter (fun z => sym2Add z % m = i)).card := by
  rw [← image_sym2Add_sym2 A]
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injOn]
  intro x hx y hy hxy
  exact sidon_injOn_sym2Add (A := A) hA (by exact (Finset.mem_filter.1 hx).1)
    (by exact (Finset.mem_filter.1 hy).1) hxy

private lemma two_mul_card_image_mk_offDiag_filter (A : Finset ℕ) (m i : ℕ) :
    2 * (((A.offDiag.filter (fun p : ℕ × ℕ => (p.1 + p.2) % m = i)).image
      Sym2.mk).card) =
      (A.offDiag.filter (fun p : ℕ × ℕ => (p.1 + p.2) % m = i)).card := by
  let T : Finset (ℕ × ℕ) := A.offDiag.filter (fun p : ℕ × ℕ => (p.1 + p.2) % m = i)
  have hsum := Finset.card_eq_sum_card_image (Sym2.mk) T
  have hfiber : ∀ z ∈ T.image Sym2.mk, (T.filter fun p => Sym2.mk p = z).card = 2 := by
    intro z hz
    rcases Finset.mem_image.1 hz with ⟨p, hpT, rfl⟩
    rcases p with ⟨a, b⟩
    have hp := Finset.mem_filter.1 hpT
    have hpOff := Finset.mem_offDiag.1 hp.1
    have hQ : (a + b) % m = i := hp.2
    have hswapT : (b, a) ∈ T := by
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_offDiag]
        exact ⟨hpOff.2.1, hpOff.1, hpOff.2.2.symm⟩
      · simpa [Nat.add_comm] using hQ
    have hfiber_eq : (T.filter fun p : ℕ × ℕ => Sym2.mk p = s(a, b)) =
        {(a, b), (b, a)} := by
      ext q
      rcases q with ⟨c, d⟩
      constructor
      · intro hq
        rw [Finset.mem_filter] at hq
        rw [Sym2.eq_iff] at hq
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        exact hq.2
      · intro hq
        rw [Finset.mem_filter]
        constructor
        · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hq
          rcases hq with hq | hq
          · rcases hq with ⟨rfl, rfl⟩
            exact hpT
          · rcases hq with ⟨rfl, rfl⟩
            exact hswapT
        · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hq
          rcases hq with hq | hq
          · rcases hq with ⟨rfl, rfl⟩
            rw [Sym2.eq_iff]
            exact Or.inl ⟨rfl, rfl⟩
          · rcases hq with ⟨rfl, rfl⟩
            rw [Sym2.eq_iff]
            exact Or.inr ⟨rfl, rfl⟩
    rw [hfiber_eq]
    rw [Finset.card_insert_of_notMem]
    · simp
    · simp [hpOff.2.2]
  have hsum_const : ∑ z ∈ T.image Sym2.mk, (T.filter fun p => Sym2.mk p = z).card =
      (T.image Sym2.mk).card * 2 := by
    exact Finset.sum_const_nat hfiber
  rw [hsum_const] at hsum
  rw [hsum, Nat.mul_comm]

private lemma card_diag_filter (A : Finset ℕ) (m i : ℕ) :
    (A.diag.filter (fun p : ℕ × ℕ => (p.1 + p.2) % m = i)).card =
      (A.filter (fun a => (2 * a) % m = i)).card := by
  rw [← Finset.card_image_of_injOn
    (s := A.diag.filter (fun p : ℕ × ℕ => (p.1 + p.2) % m = i))
    (f := fun p : ℕ × ℕ => p.1)]
  · congr 1
    ext a
    simp [two_mul]
  · intro p hp q hq hpq
    change p ∈ A.diag.filter (fun p : ℕ × ℕ => (p.1 + p.2) % m = i) at hp
    change q ∈ A.diag.filter (fun p : ℕ × ℕ => (p.1 + p.2) % m = i) at hq
    rw [Finset.mem_filter] at hp hq
    have hpdiag := Finset.mem_diag.1 hp.1
    have hqdiag := Finset.mem_diag.1 hq.1
    ext
    · exact hpq
    · simpa [hpdiag.2, hqdiag.2] using hpq

lemma two_mul_card_sym2_filter_eq_ordered_pair_count_add_diag
    (A : Finset ℕ) (m i : ℕ) :
    2 * (A.sym2.filter (fun z => sym2Add z % m = i)).card =
      ((A.product A).filter (fun p : ℕ × ℕ => (p.1 + p.2) % m = i)).card
        + (A.filter (fun a => (2 * a) % m = i)).card := by
  let Q : ℕ × ℕ → Prop := fun p => (p.1 + p.2) % m = i
  have hsym : A.sym2.filter (fun z => sym2Add z % m = i) =
      ((A.product A).filter Q).image Sym2.mk := by
    rw [Finset.sym2_eq_image]
    rw [Finset.filter_image]
    rfl
  rw [hsym]
  have hprod : A.product A = A.diag ∪ A.offDiag := by
    rw [Finset.product_eq_sprod]
    exact (Finset.diag_union_offDiag A).symm
  rw [hprod]
  rw [Finset.filter_union]
  have hdisj : Disjoint (A.diag.filter Q) (A.offDiag.filter Q) := by
    exact Disjoint.mono (by intro x hx; exact (Finset.mem_filter.1 hx).1)
      (by intro x hx; exact (Finset.mem_filter.1 hx).1) (Finset.disjoint_diag_offDiag (s := A))
  rw [Finset.card_union_of_disjoint hdisj]
  have himage_union : ((A.diag.filter Q ∪ A.offDiag.filter Q).image Sym2.mk).card =
      ((A.diag.filter Q).image Sym2.mk).card +
        ((A.offDiag.filter Q).image Sym2.mk).card := by
    rw [Finset.image_union]
    rw [Finset.card_union_of_disjoint]
    rw [Finset.disjoint_iff_ne]
    intro z hz1 w hz2 hzw
    rw [Finset.mem_image] at hz1 hz2
    rcases hz1 with ⟨p, hp, hpz⟩
    rcases hz2 with ⟨q, hq, hqw⟩
    have hmk : Sym2.mk p = Sym2.mk q := by rw [hpz, hzw, hqw]
    have hpdiag := Finset.mem_diag.1 (Finset.mem_filter.1 hp).1
    have hqoff := Finset.mem_offDiag.1 (Finset.mem_filter.1 hq).1
    rcases p with ⟨a, b⟩
    rcases q with ⟨c, d⟩
    simp only at hpdiag hqoff
    rw [Sym2.eq_iff] at hmk
    rcases hmk with hmk | hmk <;> simp_all
  rw [himage_union]
  have hdiag_card : ((A.diag.filter Q).image Sym2.mk).card =
      (A.filter (fun a => (2 * a) % m = i)).card := by
    rw [Finset.card_image_of_injOn]
    · exact card_diag_filter A m i
    · intro p hp q hq hpq
      change p ∈ A.diag.filter Q at hp
      change q ∈ A.diag.filter Q at hq
      rw [Sym2.mk_eq_mk_iff] at hpq
      have hpdiag := Finset.mem_diag.1 (Finset.mem_filter.1 hp).1
      have hqdiag := Finset.mem_diag.1 (Finset.mem_filter.1 hq).1
      rcases hpq with hpq | hpq
      · rcases p with ⟨a, b⟩
        rcases q with ⟨c, d⟩
        simp_all
      · rcases p with ⟨a, b⟩
        rcases q with ⟨c, d⟩
        simp_all
  have hoff_card : 2 * ((A.offDiag.filter Q).image Sym2.mk).card =
      (A.offDiag.filter Q).card := by
    simpa [Q] using two_mul_card_image_mk_offDiag_filter A m i
  have hdiag_filter : (A.diag.filter Q).card =
      (A.filter (fun a => (2 * a) % m = i)).card := by
    simpa [Q] using card_diag_filter A m i
  rw [hdiag_card]
  rw [Nat.mul_add]
  rw [hoff_card, hdiag_filter]
  omega

end Erdos154
