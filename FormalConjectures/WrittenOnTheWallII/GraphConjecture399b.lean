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
# Written on the Wall II - Conjecture 399b

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

The conjecture is false: there is a counterexample on 12 vertices
([wowii-399b-counterexample](https://github.com/jirichmel/wowii-399b-counterexample)).
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture399b

open SimpleGraph

-- `IsTwoDominating` and `twoDominationNumber` are copied verbatim from the open
-- Formal Conjectures pull request #7320 (WOWII Conjecture 396), at its head commit
-- adb67e65958b.

/-- Every vertex outside the set has at least two neighbors in the set. -/
def IsTwoDominating {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) : Prop :=
  ∀ v ∉ D, 2 ≤ (D.filter fun w => G.Adj v w).card

/-- The minimum order of a 2-dominating set. -/
noncomputable def twoDominationNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n | ∃ D : Finset V, IsTwoDominating G D ∧ D.card = n}

/-- The degrees of `G` in nondecreasing order, $d_1 \le d_2 \le \dots \le d_n$,
as a list indexed from `0`, so that $d_k$ is the entry at index `k - 1`. -/
def sortedDegrees {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map fun v => G.degree v).sort (· ≤ ·)

/-- Welsh-Powell of the complement of `G`, written $\mathrm{WP}(\overline{G})$.
Definition 113 of Written on the Wall II reads: "is the largest k such that the
k + d_k is less than or equal to n, where the degree sequence is order in
nondecreasing order, that is d_1 <= d_2 <= ... d_n." (The catalogue writes the
subscripts in HTML; they are written here with `_`.)

The definition does not say whose degree sequence is meant. Here
$d_1 \le \dots \le d_n$ are read as the degrees of `G`; with this reading the value
is the Welsh-Powell bound for the chromatic number of the complement of `G`.
The index $k$ ranges over $1, \dots, n$. For $n \ge 1$ the value $k = 1$ always
qualifies; the value is `0` only when $n = 0$. -/
def welshPowellComplement {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((Finset.Icc 1 (Fintype.card V)).filter fun k =>
    k + (sortedDegrees G).getD (k - 1) 0 ≤ Fintype.card V).sup id

/-- $A_3$: the set of vertices of degree at least three. -/
def degreeAtLeastThree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => 3 ≤ G.degree v

/--
WOWII Conjecture 399b states: "If $G$ is a connected graph on $n > 2$ vertices,
then $\gamma_2 \le \mathrm{WP}(\overline{G}) + \lfloor 3/\alpha(G[A_3]) \rfloor$,
where $A_3$ is the set vertices of degree at least three."

Definition 90 of Written on the Wall II reads: "A subset of the vertices, D_2, of
the graph is called a 2-dominating set of the graph if for every vertex v of the
graph, either in v is D_2 or v is adjacent to 2 vertices of D_2. The 2-domination
number of a graph is the size of a smallest 2-dominating set of the graph." (The
catalogue writes the subscripts and italics in HTML; subscripts are written here
with `_`.) "Adjacent to 2 vertices" is read as "adjacent to at least two
vertices", the standard meaning; this is `IsTwoDominating`.

Here $\gamma_2$ is `twoDominationNumber G`, $\mathrm{WP}(\overline{G})$ is
`welshPowellComplement G`, $A_3$ is `degreeAtLeastThree G`, and
$\alpha(G[A_3])$ is the independence number of the induced subgraph; `/` on `ℕ`
is floor division. When $A_3$ is empty, $\alpha(G[A_3]) = 0$ and the source's
right side $3/0$ is undefined, so the statement assumes that $A_3$ is nonempty.
This hypothesis only weakens the conjecture, so its negation, stated here, is
the stronger claim.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-23-000032"]
theorem conjecture399b : ¬ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → 2 < Fintype.card V → (degreeAtLeastThree G).Nonempty →
        twoDominationNumber G ≤
          welshPowellComplement G +
            3 / (G.induce (degreeAtLeastThree G : Set V)).indepNum := by
  sorry

-- Sanity checks

/-- The path on three vertices, `0 - 1 - 2`. -/
abbrev path3 : SimpleGraph (Fin 3) := SimpleGraph.fromRel fun i j => j.val = i.val + 1

/-- The star $K_{1,3}$ with centre `0`. -/
abbrev star3 : SimpleGraph (Fin 4) := SimpleGraph.fromRel fun i _ => i = 0

/-- The path on three vertices has degrees `1, 1, 2`, so $\mathrm{WP}(\overline{P_3}) = 2$
($2 + d_2 = 3 \le 3 < 3 + d_3$), and $A_3$ is empty. -/
@[category test, AMS 5]
example : welshPowellComplement path3 = 2 ∧ degreeAtLeastThree path3 = ∅ := by
  have h : sortedDegrees path3 = [1, 1, 2] :=
    List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _) (by decide)
      (Multiset.coe_eq_coe.mp (by rw [sortedDegrees, Multiset.sort_eq]; decide))
  simp only [welshPowellComplement, h]
  decide

/-- The star $K_{1,3}$ has degrees `1, 1, 1, 3`, so $\mathrm{WP}(\overline{K_{1,3}}) = 3$,
and $A_3$ is its centre. -/
@[category test, AMS 5]
example : welshPowellComplement star3 = 3 ∧ degreeAtLeastThree star3 = {0} := by
  have h : sortedDegrees star3 = [1, 1, 1, 3] :=
    List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _) (by decide)
      (Multiset.coe_eq_coe.mp (by rw [sortedDegrees, Multiset.sort_eq]; decide))
  simp only [welshPowellComplement, h]
  decide

/-- The three leaves of $K_{1,3}$ form a 2-dominating set, and two leaves do not. -/
@[category test, AMS 5]
example : IsTwoDominating star3 {1, 2, 3} ∧ ¬ IsTwoDominating star3 {1, 2} := by
  unfold IsTwoDominating
  decide

/-- The triangle has degrees `2, 2, 2`, so $\mathrm{WP}(\overline{K_3}) = 1$. -/
@[category test, AMS 5]
example : welshPowellComplement (⊤ : SimpleGraph (Fin 3)) = 1 := by
  have h : sortedDegrees (⊤ : SimpleGraph (Fin 3)) = [2, 2, 2] :=
    List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _) (by decide)
      (Multiset.coe_eq_coe.mp (by rw [sortedDegrees, Multiset.sort_eq]; decide))
  simp only [welshPowellComplement, h]
  decide

end WrittenOnTheWallII.GraphConjecture399b
