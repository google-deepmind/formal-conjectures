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
# Torsion-Freeness of Artin–Tits Groups

From a symmetric Coxeter matrix $M = (m_{ij})_{i, j \in B}$ (`CoxeterMatrix B`, where $m_{ii} = 1$
and $m_{ij} = 0$ encodes $m_{ij} = \infty$), one constructs the *Artin–Tits group* $A(M)$ generated
by $\{s_i : i \in B\}$ subject to the homogeneous alternating braid relations
$$\underbrace{s_i s_j s_i \cdots}_{m_{ij}\text{ factors}}
  = \underbrace{s_j s_i s_j \cdots}_{m_{ij}\text{ factors}}$$
for every pair $(i, j)$ with $m_{ij} \ge 2$, omitting the reflection relations $s_i^2 = 1$ of the
associated Coxeter group $W(M)$ (`M.Group`).

A central open conjecture in combinatorial and geometric group theory states that every Artin–Tits
group $A(M)$ has trivial torsion (`Monoid.IsTorsionFree`). Deligne (1972) and Brieskorn and Saito
(1972) established torsion-freeness whenever $M$ has spherical type ($W(M)$ finite), and the same
conclusion holds in the right-angled case ($m_{ij} \in \{2, \infty\}$ for $i \ne j$; see Charney
2007).

*References:*
- [Wikipedia: Artin–Tits group](https://en.wikipedia.org/wiki/Artin%E2%80%93Tits_group)
- E. Brieskorn and K. Saito, *Artin-Gruppen und Coxeter-Gruppen*, Invent. Math. **17** (1972),
  245–271.
- P. Deligne, *Les immeubles des groupes de tresses généralisés*, Invent. Math. **17** (1972),
  273–302.
- R. Charney, *An introduction to right-angled Artin groups*, Geom. Dedicata **125** (2007),
  141–158.
-/

@[expose] public section

namespace ArtinTitsGroup

/-- Alternating word $a b a b \cdots$ of length $m$ on generators $a, b \in B$ inside
`FreeGroup B`. -/
def alternatingBraidWord {B : Type*} (a b : B) : ℕ → FreeGroup B
  | 0 => 1
  | m + 1 => FreeGroup.of a * alternatingBraidWord b a m

/-- Defining relators of the Artin–Tits group attached to `M : CoxeterMatrix B`, where `M i j = 0`
represents $m_{ij} = \infty$ and imposes no braid relation. -/
def relators {B : Type*} (M : CoxeterMatrix B) : Set (FreeGroup B) :=
  {r | ∃ i j : B, 2 ≤ M i j ∧
    r = alternatingBraidWord i j (M i j) * (alternatingBraidWord j i (M i j))⁻¹}

/-- The Artin–Tits group $A(M)$ presented by the braid relations of `M : CoxeterMatrix B`. -/
abbrev ofMatrix {B : Type*} (M : CoxeterMatrix B) : Type _ :=
  PresentedGroup (relators M)

/-- The alternating braid word of length $2$ equals $a b$. -/
@[category API, AMS 20]
theorem alternatingBraidWord_two {B : Type*} (a b : B) :
    alternatingBraidWord a b 2 = FreeGroup.of a * FreeGroup.of b := by
  simp [alternatingBraidWord]

/-- The alternating braid word of length $3$ equals $a b a$. -/
@[category test, AMS 20]
theorem alternatingBraidWord_three {B : Type*} (a b : B) :
    alternatingBraidWord a b 3 = FreeGroup.of a * FreeGroup.of b * FreeGroup.of a := by
  simp [alternatingBraidWord, mul_assoc]

/-- On `Fin 0`, the set of Artin–Tits defining relators is empty. -/
@[category API, AMS 20]
theorem relators_fin_zero (M : CoxeterMatrix (Fin 0)) :
    relators M = ∅ := by
  ext r
  simp [relators]

/-- The rank-$0$ Artin–Tits group is trivial and therefore torsion-free. -/
@[category test, AMS 20]
theorem ofMatrix_rank_zero_torsion_free (M : CoxeterMatrix (Fin 0)) :
    Monoid.IsTorsionFree (ofMatrix M) := by
  have h1 : ∀ x : FreeGroup (Fin 0), x = 1 := fun x =>
    FreeGroup.induction_on x rfl (fun i => Fin.elim0 i) (fun i _ => Fin.elim0 i)
      fun _ _ hx hy => by rw [hx, hy, one_mul]
  have : Subsingleton (FreeGroup (Fin 0)) := ⟨fun x y => (h1 x).trans (h1 y).symm⟩
  have : Subsingleton (ofMatrix M) := by
    unfold ofMatrix PresentedGroup
    infer_instance
  intro g hg
  exact False.elim (hg (Subsingleton.elim g 1))

/-- **Artin–Tits Torsion-Freeness Conjecture**: For every finite index set $B$ and Coxeter matrix
$M$ on $B$, the Artin–Tits group $A(M)$ has trivial torsion (`Monoid.IsTorsionFree`). Note that
uniqueness of roots (`IsMulTorsionFree`) already fails in the $3$-strand braid group, where
$(s_1 s_2)^3 = (s_2 s_1)^3$ with $s_1 s_2 \ne s_2 s_1$. -/
@[category research open, AMS 20]
theorem artin_tits_group_torsion_free {B : Type} [Finite B] (M : CoxeterMatrix B) :
    Monoid.IsTorsionFree (ofMatrix M) := by
  sorry

/-- **Deligne–Brieskorn–Saito Theorem** (1972): Every spherical-type Artin–Tits group—one whose
associated Coxeter group `M.Group` is finite—is torsion-free. -/
@[category research solved, AMS 20]
theorem spherical_torsion_free {B : Type} [Finite B] (M : CoxeterMatrix B)
    (hfin : Finite M.Group) :
    Monoid.IsTorsionFree (ofMatrix M) := by
  sorry

/-- **Right-Angled Torsion-Freeness**: When $B$ is finite and off-diagonal Coxeter entries satisfy
$m_{ij} \in \{2, \infty\}$ (`M i j = 2 ∨ M i j = 0`), the Artin–Tits group $A(M)$ is torsion-free
(see Charney 2007). -/
@[category research solved, AMS 20]
theorem right_angled_torsion_free {B : Type} [Finite B] (M : CoxeterMatrix B)
    (hra : ∀ i j : B, i ≠ j → M i j = 2 ∨ M i j = 0) :
    Monoid.IsTorsionFree (ofMatrix M) := by
  sorry

end ArtinTitsGroup
