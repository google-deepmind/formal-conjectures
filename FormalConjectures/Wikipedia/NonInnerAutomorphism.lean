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
# Finite $p$-Group Non-Inner Automorphisms

Wolfgang Gaschütz (1966) proved that every non-abelian finite $p$-group $G$ admits a
$p$-power-order non-inner automorphism; in that 1966 paper Gaschütz deduced that every finite
$p$-group of cardinality exceeding $p$ possesses an outer automorphism.

Whether every non-abelian finite $p$-group $G$ admits a non-inner automorphism of exact order $p$
(posed by Yakov Berkovich in 1973 as Problem 4.13 of the Kourovka Notebook) remains an open
question. Among known special cases, Alireza Abdollahi (2007) proved an affirmative answer whenever
$G$ has nilpotency class $2$.

*References:*
- [Wikipedia: Inner automorphism](https://en.wikipedia.org/wiki/Inner_automorphism)
- W. Gaschütz, *Nichtabelsche $p$-Gruppen besitzen äussere $p$-Automorphismen*, J. Algebra **4**
  (1966), 1–2.
- A. Abdollahi, *Finite $p$-groups of class $2$ have noninner automorphisms of order $p$*,
  J. Algebra **312** (2007), 876–879.
- V. D. Mazurov and E. I. Khukhro (eds.), *The Kourovka Notebook: Unsolved Problems in Group
  Theory*, Problem 4.13 (Ya. G. Berkovich, 1973).
-/

@[expose] public section

namespace NonInnerAutomorphism

/-- Predicate that a group $G$ admits an automorphism outside $\operatorname{Inn}(G)$. -/
def HasNonInnerAut (G : Type*) [Group G] : Prop :=
  ∃ φ : MulAut G, φ ∉ (MulAut.conj (G := G)).range

/-- For a commutative group $G$, inner automorphisms are trivial, so `HasNonInnerAut G` holds
precisely when $G$ admits a non-identity automorphism. -/
@[category API, AMS 20]
theorem hasNonInnerAut_commGroup_iff (G : Type*) [CommGroup G] :
    HasNonInnerAut G ↔ ∃ φ : MulAut G, φ ≠ 1 := by
  unfold HasNonInnerAut
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, fun h1 => hφ ⟨1, ?_⟩⟩
    rw [h1, map_one]
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, ?_⟩
    rintro ⟨g, rfl⟩
    apply hφ
    ext x
    simp [MulAut.conj_apply]

/-- For a prime $p$ and any non-inner automorphism $\varphi \in \operatorname{Aut}(G)$, having
order $p$ is equivalent to satisfying $\varphi^p = 1$. -/
@[category API, AMS 20]
theorem nonInner_orderOf_eq_prime_iff {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {φ : MulAut G} (hφ : φ ∉ (MulAut.conj (G := G)).range) :
    orderOf φ = p ↔ φ ^ p = 1 := by
  refine ⟨fun h => h ▸ pow_orderOf_eq_one φ, fun hpow => ?_⟩
  rcases hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hpow) with h1 | hp'
  · exact False.elim (hφ ⟨1, by rw [orderOf_eq_one_iff.mp h1, map_one]⟩)
  · exact hp'

/-- The Klein four-group $(\mathbb{Z}/2\mathbb{Z}) \times (\mathbb{Z}/2\mathbb{Z})$ admits a
non-inner automorphism obtained by swapping its two factors. -/
@[category test, AMS 20]
theorem hasNonInnerAut_klein_four :
    HasNonInnerAut (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  rw [hasNonInnerAut_commGroup_iff]
  refine ⟨MulEquiv.prodComm, ?_⟩
  intro h
  have h1 := MulEquiv.ext_iff.mp h (Multiplicative.ofAdd 1, 1)
  revert h1
  decide

/-- **Gaschütz's Theorem** (1966): Every non-abelian finite $p$-group $G$ admits a non-inner
automorphism whose order in $\operatorname{Aut}(G)$ is a power of $p$. -/
@[category research solved, AMS 20]
theorem gaschutz_non_inner_p_power_automorphism
    (p : ℕ) (hp : p.Prime) (G : Type*) [Group G] [Finite G]
    (hG : IsPGroup p G) (hnonab : ¬ ∀ a b : G, a * b = b * a) :
    ∃ φ : MulAut G, φ ∉ (MulAut.conj (G := G)).range ∧ ∃ k : ℕ, orderOf φ = p ^ k := by
  sorry

/-- **Gaschütz's Outer Automorphism Corollary** (1966): Every finite $p$-group $G$ of cardinality
$|G| > p$ admits a non-inner automorphism. Stated from Gaschütz (1966), combining the non-abelian
theorem above with elementary automorphisms on abelian $p$-groups of order exceeding $p$. -/
@[category research solved, AMS 20]
theorem gaschutz_hasNonInnerAut_of_card_gt_prime
    (p : ℕ) (hp : p.Prime) (G : Type*) [Group G] [Finite G]
    (hG : IsPGroup p G) (hcard : p < Nat.card G) :
    HasNonInnerAut G := by
  sorry

/-- **Abdollahi's Class-$2$ Theorem** (2007): Every non-abelian finite $p$-group $G$ of nilpotency
class $2$ ($[G, G] \le Z(G)$) admits a non-inner automorphism of exact order $p$. -/
@[category research solved, AMS 20]
theorem abdollahi_class_two_non_inner_order_p
    (p : ℕ) (hp : p.Prime) (G : Type*) [Group G] [Finite G]
    (hG : IsPGroup p G) (hnonab : ¬ ∀ a b : G, a * b = b * a)
    (hclass2 : commutator G ≤ Subgroup.center G) :
    ∃ φ : MulAut G, φ ∉ (MulAut.conj (G := G)).range ∧ orderOf φ = p := by
  sorry

/-- **Non-Inner Automorphism of Order $p$ Question** (Berkovich 1973, Kourovka Problem 4.13): Does
every non-abelian finite $p$-group $G$ admit a non-inner automorphism of exact order $p$? Note that
Wikipedia's second sentence omits both "finite" and "non-inner" as shorthand inherited from the
subsection heading and preceding sentence (inner automorphisms of order $p$ always exist by Cauchy's
theorem on $G / Z(G)$). -/
@[category research open, question, AMS 20]
theorem berkovich_non_inner_automorphism_order_p
    (p : ℕ) (hp : p.Prime) (G : Type*) [Group G] [Finite G]
    (hG : IsPGroup p G) (hnonab : ¬ ∀ a b : G, a * b = b * a) :
    ∃ φ : MulAut G, φ ∉ (MulAut.conj (G := G)).range ∧ orderOf φ = p := by
  sorry

end NonInnerAutomorphism
