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
# Vanishing of the Whitehead group for torsion-free groups

For a group $G$, Whitehead [Wh50] defined the *Whitehead group*
$\operatorname{Wh}(G) = K_1(\mathbb{Z}[G]) / \{\pm g : g \in G\}$ by dividing the stabilized
general linear group $\operatorname{GL}(\mathbb{Z}[G])$ by elementary transvection matrices and
trivial units $\pm g$ ($g \in G$); see also Milnor's survey [Mi66].

Bass, Heller, and Swan [BHS64] proved $\operatorname{Wh}(\mathbb{Z}^d) = 0$ for finitely generated
free abelian groups, while for a finite cyclic group $C_n$ ($n \ge 1$) combining Higman's unit
theorem [Hi40] with $SK_1(\mathbb{Z}[C_n]) = 0$ [BMS67] gives $\operatorname{Wh}(C_n) = 0$
precisely when $n \in \{1, 2, 3, 4, 6\}$ (see [Co73, §11]). It is conjectured that
$\operatorname{Wh}(G) = 0$ for every torsion-free group $G$.

*References:*
- [Wikipedia: Whitehead torsion](https://en.wikipedia.org/wiki/Whitehead_torsion)
- [Hi40] G. Higman, *The units of group-rings*, Proc. London Math. Soc. (2) **46** (1940),
  231–248, https://doi.org/10.1112/plms/s2-46.1.231.
- [Wh50] J. H. C. Whitehead, *Simple homotopy types*, Amer. J. Math. **72** (1950), no. 1, 1–57,
  https://doi.org/10.2307/2372133.
- [BHS64] H. Bass, A. Heller, R. G. Swan, *The Whitehead group of a polynomial extension*, Publ.
  Math. Inst. Hautes Études Sci. **22** (1964), 61–79, https://doi.org/10.1007/BF02684690.
- [Mi66] J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. **72** (1966), no. 3, 358–426,
  https://doi.org/10.1090/S0002-9904-1966-11484-2.
- [BMS67] H. Bass, J. Milnor, J.-P. Serre, *Solution of the congruence subgroup problem for
  $\operatorname{SL}_n$ ($n \ge 3$) and $\operatorname{Sp}_{2n}$ ($n \ge 2$)*, Publ. Math. Inst.
  Hautes Études Sci. **33** (1967), 59–137, https://doi.org/10.1007/BF02684586.
- [Co73] M. M. Cohen, *A Course in Simple-Homotopy Theory*, Graduate Texts in Mathematics **10**,
  Springer, 1973.
-/

@[expose] public section

namespace WhiteheadGroup

/-- Block-pads an $n \times n$ matrix into an $(n + k) \times (n + k)$ matrix by placing `A` in the
top-left block and `1` along the remaining `k` diagonal entries. -/
def stabilizeMatrix {R : Type*} [Semiring R] {n : ℕ} (k : ℕ)
    (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + k)) (Fin (n + k)) R :=
  Matrix.of fun i j =>
    Fin.addCases
      (fun i₁ => Fin.addCases (fun j₁ => A i₁ j₁) (fun _ => 0) j)
      (fun i₂ => Fin.addCases (fun _ => 0) (fun j₂ => if i₂ = j₂ then 1 else 0) j)
      i

/-- Stabilization preserves the identity matrix. -/
@[category API, AMS 19 20]
theorem stabilizeMatrix_one {R : Type*} [Semiring R] (n k : ℕ) :
    stabilizeMatrix k (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
  · refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
    · simp [stabilizeMatrix, Matrix.one_apply]
    · simp [stabilizeMatrix, Matrix.one_apply, Fin.addCases]
      intro h
      exact absurd (congrArg Fin.val h) (by simp; omega)
  · refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
    · simp [stabilizeMatrix, Matrix.one_apply, Fin.addCases]
      intro h
      exact absurd (congrArg Fin.val h) (by simp; omega)
    · simp [stabilizeMatrix, Matrix.one_apply]

/-- Stabilization commutes with matrix multiplication. -/
@[category API, AMS 19 20]
theorem stabilizeMatrix_mul {R : Type*} [Semiring R] {n : ℕ} (k : ℕ)
    (A B : Matrix (Fin n) (Fin n) R) :
    stabilizeMatrix k A * stabilizeMatrix k B = stabilizeMatrix k (A * B) := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_add]
  refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i <;>
    refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j <;>
    simp [stabilizeMatrix, Matrix.mul_apply]

/-- Stabilization homomorphism $\operatorname{GL}_n(R) \to \operatorname{GL}_{n + k}(R)$. -/
def stabilizeGL {R : Type*} [Semiring R] {n : ℕ} (k : ℕ) :
    Matrix.GeneralLinearGroup (Fin n) R →* Matrix.GeneralLinearGroup (Fin (n + k)) R where
  toFun u :=
    { val := stabilizeMatrix k u.val
      inv := stabilizeMatrix k u.inv
      val_inv := by rw [stabilizeMatrix_mul, u.val_inv, stabilizeMatrix_one]
      inv_val := by rw [stabilizeMatrix_mul, u.inv_val, stabilizeMatrix_one] }
  map_one' := Units.ext (stabilizeMatrix_one n k)
  map_mul' u v := Units.ext (stabilizeMatrix_mul k u.val v.val).symm

/-- Generating set of trivial Whitehead elements in $\operatorname{GL}_N(\mathbb{Z}[G])$:
off-diagonal elementary transvections $I_N + r E_{i,j}$ ($i \ne j$) together with the stabilized
trivial units $\operatorname{diag}(\pm g, 1, \dots, 1)$ ($g \in G$). -/
def whiteheadTrivialGenerators (G : Type*) [Group G] (N : ℕ) :
    Set (Matrix.GeneralLinearGroup (Fin N) (MonoidAlgebra ℤ G)) :=
  {u | ∃ (i j : Fin N) (r : MonoidAlgebra ℤ G),
      i ≠ j ∧ u.val = 1 + Matrix.single i j r} ∪
  {u | ∃ (hN : 0 < N) (g : G) (ε : ℤ),
      (ε = 1 ∨ ε = -1) ∧
      u.val = Matrix.diagonal (fun i : Fin N =>
        if i = ⟨0, hN⟩ then MonoidAlgebra.single g ε else 1)}

/-- The Whitehead group $\operatorname{Wh}(G)$ vanishes if every
$u \in \operatorname{GL}_n(\mathbb{Z}[G])$ stabilizes for some $k \ge 0$ into the subgroup
generated by `whiteheadTrivialGenerators G (n + k)`. -/
def HasTrivialWhiteheadGroup (G : Type*) [Group G] : Prop :=
  ∀ (n : ℕ) (u : Matrix.GeneralLinearGroup (Fin n) (MonoidAlgebra ℤ G)),
    ∃ k : ℕ, stabilizeGL k u ∈ Subgroup.closure (whiteheadTrivialGenerators G (n + k))

/-- The $1 \times 1$ identity matrix belongs to `whiteheadTrivialGenerators G 1`. -/
@[category test, AMS 19 20]
theorem one_mem_whiteheadTrivialGenerators (G : Type*) [Group G] :
    (1 : Matrix.GeneralLinearGroup (Fin 1) (MonoidAlgebra ℤ G)) ∈
      whiteheadTrivialGenerators G 1 := by
  refine Or.inr ⟨Nat.zero_lt_one, 1, 1, Or.inl rfl, ?_⟩
  ext i j
  fin_cases i
  fin_cases j
  simp [MonoidAlgebra.one_def]

/-- Every off-diagonal $2 \times 2$ transvection `1 + Matrix.single 0 1 r` belongs to
`whiteheadTrivialGenerators G 2`. -/
@[category test, AMS 19 20]
theorem transvection_mem_whiteheadTrivialGenerators (G : Type*) [Group G]
    (r : MonoidAlgebra ℤ G)
    (u : Matrix.GeneralLinearGroup (Fin 2) (MonoidAlgebra ℤ G))
    (hu : u.val = 1 + Matrix.single (0 : Fin 2) 1 r) :
    u ∈ whiteheadTrivialGenerators G 2 :=
  Or.inl ⟨0, 1, r, by decide, hu⟩

/--
**Trivial group case**: $\operatorname{Wh}(G) = 0$ when $G$ is trivial, via Euclidean row and
column reduction over $\mathbb{Z}$.
-/
@[category textbook, AMS 19 20]
theorem hasTrivialWhiteheadGroup_of_subsingleton (G : Type*) [Group G] [Subsingleton G] :
    HasTrivialWhiteheadGroup G := by
  sorry

/--
**Bass–Heller–Swan theorem** [BHS64]: the Whitehead group of every finitely generated free abelian
group $\mathbb{Z}^d$ vanishes.
-/
@[category research solved, AMS 19 20]
theorem bass_heller_swan_free_abelian (d : ℕ) :
    HasTrivialWhiteheadGroup (Multiplicative (Fin d → ℤ)) := by
  sorry

/--
**Finite cyclic groups** [Hi40, BMS67, Co73]: for $n \ge 1$, the cyclic group $C_n$ of order $n$
satisfies $\operatorname{Wh}(C_n) = 0$ precisely for $n \in \{1, 2, 3, 4, 6\}$, combining Higman's
characterization of trivial units in $\mathbb{Z}[C_n]$ [Hi40] with $SK_1(\mathbb{Z}[C_n]) = 0$
[BMS67] (see [Co73, §11]). The guard $1 \le n$ excludes `ZMod 0`, which is isomorphic to
$\mathbb{Z}$ rather than a finite cyclic group.
-/
@[category research solved, AMS 19 20]
theorem hasTrivialWhiteheadGroup_cyclic_iff {n : ℕ} (hn : 1 ≤ n) :
    HasTrivialWhiteheadGroup (Multiplicative (ZMod n)) ↔ n ∈ ({1, 2, 3, 4, 6} : Set ℕ) := by
  sorry

/--
**Whitehead group vanishing conjecture** [Mi66]: for every torsion-free group $G$, the Whitehead
group $\operatorname{Wh}(G)$ vanishes.
-/
@[category research open, AMS 19 20]
theorem whitehead_group_vanishing_conjecture (G : Type*) [Group G]
    (hG : Monoid.IsTorsionFree G) :
    HasTrivialWhiteheadGroup G := by
  sorry

end WhiteheadGroup
