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
# Rota's basis conjecture

Let $M$ be a matroid of rank $n$ with $n$ disjoint bases $B_1, \dots, B_n$. Rota conjectured that
there are $n$ disjoint bases $C_1, \dots, C_n$ such that each $C_i$ contains exactly one element of
each $B_j$. Equivalently, the elements of the $B_j$ can be arranged in an $n \times n$ matrix whose
rows are the $B_j$ and whose columns are also bases.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Rota%27s_basis_conjecture)
- [Open Problem Garden](http://www.openproblemgarden.org/op/rotas_basis_conjecture)
- [HR94] Huang, R. and Rota, G.-C., *On the relations of various conjectures on Latin squares and
  straightening coefficients*. Discrete Math. 128 (1994), 225-236, Conjecture 4.
- [Cha95] Chan, W., *An exchange property of matroid*. Discrete Math. 146 (1995), 299-302.
- [GeHu06] Geelen, J. and Humphries, P. J., *Rota's basis conjecture for paving matroids*.
  SIAM J. Discrete Math. 20 (2006), 1042-1045.
- [Gly10] Glynn, D. G., *The conjectures of Alon-Tarsi and Rota in dimension prime minus one*.
  SIAM J. Discrete Math. 24 (2010), 394-399.
- [BKPS20] Bucić, M., Kwan, M., Pokrovskiy, A. and Sudakov, B., *Halfway to Rota's basis
  conjecture*. Int. Math. Res. Not. IMRN (2020).
  [arXiv:1810.07462](https://arxiv.org/abs/1810.07462)
- [McG24] McGuinness, S., *Rota's basis conjecture for matroids with density close to one*.
  Adv. in Appl. Math. 152 (2024), 102593.
-/

@[expose] public section

namespace RotaBasisConjecture

open Function

/-- In a matroid of rank $1$ the given basis is itself the required family. -/
@[category test, AMS 5]
theorem rota_basis_conjecture_rank_one {α : Type*} (M : Matroid α) (hr : M.eRank = 1)
    (B : Fin 1 → Set α) (hB : ∀ i, M.IsBase (B i)) :
    ∃ C : Fin 1 → Set α, (∀ i, M.IsBase (C i)) ∧ Pairwise (Disjoint on C) ∧
      ∀ i j, (C i ∩ B j).ncard = 1 := by
  refine ⟨B, hB, fun i j h ↦ (h (Subsingleton.elim i j)).elim, fun i j ↦ ?_⟩
  obtain ⟨x, hx⟩ := Set.encard_eq_one.mp ((hB j).encard_eq_eRank.trans hr)
  rw [Subsingleton.elim i j, Set.inter_self, hx, Set.ncard_singleton]

/--
**Rota's basis conjecture.** Let $M$ be a matroid of rank $n$ and let $B_1, \dots, B_n$ be
pairwise disjoint bases of $M$. Then there are pairwise disjoint bases $C_1, \dots, C_n$ of $M$
such that $|C_i \cap B_j| = 1$ for all $i$ and $j$.

Rota stated it in 1989; it was first published in [HR94]. It is known for $n \le 3$ [Cha95] and
for paving matroids [GeHu06].
-/
@[category research open, AMS 5]
theorem rota_basis_conjecture {α : Type*} (M : Matroid α) (n : ℕ) (hr : M.eRank = n)
    (B : Fin n → Set α) (hB : ∀ i, M.IsBase (B i)) (hdisj : Pairwise (Disjoint on B)) :
    ∃ C : Fin n → Set α, (∀ i, M.IsBase (C i)) ∧ Pairwise (Disjoint on C) ∧
      ∀ i j, (C i ∩ B j).ncard = 1 := by
  sorry

/--
The vector space version [HR94, Conjecture 4]: if $B_1, \dots, B_n$ are bases of an
$n$-dimensional vector space $V$, written as rows of an $n \times n$ array, then the entries of
each row can be permuted so that every column is also a basis of $V$. Vectors may repeat across
the $B_i$.

[HR94] states this over an infinite field. The statement here allows any field, which is the
case of `rota_basis_conjecture` for matroids representable over that field.
-/
@[category research open, AMS 5 15]
theorem rota_basis_conjecture.variants.vector_space {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (n : ℕ) (hV : Module.finrank K V = n) (B : Fin n → Fin n → V)
    (hB : ∀ i, LinearIndependent K (B i)) :
    ∃ σ : Fin n → Equiv.Perm (Fin n), ∀ j, LinearIndependent K fun i ↦ B i (σ i j) := by
  sorry

/-- Rota's basis conjecture holds for matroids of rank at most $3$ [Cha95]. -/
@[category research solved, AMS 5]
theorem rota_basis_conjecture.variants.rank_le_three {α : Type*} (M : Matroid α) (n : ℕ)
    (hn : n ≤ 3) (hr : M.eRank = n) (B : Fin n → Set α) (hB : ∀ i, M.IsBase (B i))
    (hdisj : Pairwise (Disjoint on B)) :
    ∃ C : Fin n → Set α, (∀ i, M.IsBase (C i)) ∧ Pairwise (Disjoint on C) ∧
      ∀ i j, (C i ∩ B j).ncard = 1 := by
  sorry

/--
The vector space version holds in dimension $p - 1$ for every prime $p$, over every field of
characteristic zero [Gly10]. Glynn proves that the numbers of even and odd Latin squares of order
$p - 1$ differ, which implies the conjecture in that dimension by [HR94].
-/
@[category research solved, AMS 5 15]
theorem rota_basis_conjecture.variants.prime_sub_one {K V : Type*} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] {p : ℕ} (hp : p.Prime) (hV : Module.finrank K V = p - 1)
    (B : Fin (p - 1) → Fin (p - 1) → V) (hB : ∀ i, LinearIndependent K (B i)) :
    ∃ σ : Fin (p - 1) → Equiv.Perm (Fin (p - 1)),
      ∀ j, LinearIndependent K fun i ↦ B i (σ i j) := by
  sorry

/--
For every $\varepsilon > 0$ and every large enough $n$, a matroid of rank $n$ with $n$ disjoint
bases $B_1, \dots, B_n$ has at least $(1/2 - \varepsilon) n$ pairwise disjoint bases that each
meet every $B_j$ in exactly one element [BKPS20]. See also [McG24, Section 1].
-/
@[category research solved, AMS 5]
theorem rota_basis_conjecture.variants.halfway (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ {α : Type} (M : Matroid α), M.eRank = n →
      ∀ B : Fin n → Set α, (∀ i, M.IsBase (B i)) → Pairwise (Disjoint on B) →
        ∃ k : ℕ, (1 / 2 - ε) * n ≤ k ∧ ∃ C : Fin k → Set α, (∀ i, M.IsBase (C i)) ∧
          Pairwise (Disjoint on C) ∧ ∀ i j, (C i ∩ B j).ncard = 1 := by
  sorry

end RotaBasisConjecture
