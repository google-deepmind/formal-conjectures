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
# Written on the Wall II - Conjecture 213

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

The conjecture is proved in
[wowii-213-proof](https://github.com/jirichmel/wowii-213-proof).
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture213

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

/-- The term $d_k$ of the degree sequence of `G` in nondecreasing order, for
$1 \le k \le n$ (indexed from `1`). -/
def sortedDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  (sortedDegrees G).getD (k - 1) 0

/-- The lower median of the degree sequence of `G`, the middle term $d_{\lceil n/2 \rceil}$.
Definition 68 of Written on the Wall II reads: "Let d_1 ≤ d_2 ≤ ... ≤ d_{n-1} ≤ d_n
be the degree sequence in nondecreasing order. If the graph has an odd number of
vertices, then median of the ordered degree sequence is the d_{(n+1)/2+1} degree;
otherwise it is the average of the degrees d_{n/2} and d_{n/2+1}. If the graph has
an odd number of vertices then the lower and upper median are precisely the median
degree of the graph; if the number of vertices is even, then the lower median is
the d_{n/2} degree and the upper median is the d_{(n+2)/2} degree." (The catalogue
writes the subscripts, bold face and italics in HTML; a subscript is written here
after `_`, in braces when it is longer than one character.)

For odd $n$ the text names $d_{(n+1)/2+1}$, which is not the middle of the sequence.
The middle term $d_{(n+1)/2}$, the median in the usual statistical sense, is used here,
as in E. DeLaViña, C. E. Larson, R. Pepper and B. Waller, Graffiti.pc on the
2-domination number of a graph, Congr. Numer. 203 (2010) 15–32, which defines the upper
median for an odd number of vertices as the (statistical) median, the middle term (p. 14
of the version at https://www.uhd.edu/documents/academics/sciences/gpcon2-dominmay17.pdf);
by definition 68 the lower and upper medians coincide when $n$ is odd.
For even $n$ the two readings agree: this is $d_{n/2}$. In general it is
$d_{\lceil n/2 \rceil}$, the term with index `(n + 1) / 2` counted from `1`. The literal
reading is `lowerMedianDegreeLiteral`. -/
def lowerMedianDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sortedDegree G ((Fintype.card V + 1) / 2)

/-- The lower median of the degree sequence of `G`, read literally from definition 68.
Definition 68 of Written on the Wall II reads: "Let d_1 ≤ d_2 ≤ ... ≤ d_{n-1} ≤ d_n
be the degree sequence in nondecreasing order. If the graph has an odd number of
vertices, then median of the ordered degree sequence is the d_{(n+1)/2+1} degree;
otherwise it is the average of the degrees d_{n/2} and d_{n/2+1}. If the graph has
an odd number of vertices then the lower and upper median are precisely the median
degree of the graph; if the number of vertices is even, then the lower median is
the d_{n/2} degree and the upper median is the d_{(n+2)/2} degree." (The catalogue
writes the subscripts, bold face and italics in HTML; a subscript is written here
after `_`, in braces when it is longer than one character.)

This definition follows that text literally: it is $d_{n/2}$ for even $n$ and
$d_{(n+1)/2+1}$ for odd $n$. For odd $n$ that is not the middle term $d_{(n+1)/2}$,
which `lowerMedianDegree` uses. The literal term is never smaller than the middle
term, so with it the hypothesis of Conjecture 213 is stronger and the statement weaker;
the two readings differ on some connected graphs with $n = 7$. It is used only in
`conjecture213.variants.literal`. -/
def lowerMedianDegreeLiteral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  if Fintype.card V % 2 = 1 then
    sortedDegree G ((Fintype.card V + 1) / 2 + 1)
  else
    sortedDegree G (Fintype.card V / 2)

/--
WOWII Conjecture 213 states: "If G is a simple connected graph with n > 1 such
that 2 + the lower median of degree sequence of $\overline{G}$ ≤
$\gamma_2(\overline{G})$, then G has a Hamiltonian path." The catalogue draws an
overline (HTML `text-decoration: overline`) on the $G$ after "degree sequence of"
and on the $G$ inside $\gamma_2(\cdot)$, and on no other $G$.

Definition 31 of Written on the Wall II reads: "Let G be a graph. The complement
graph of G, denoted $\overline{G}$, is the graph on the same vertex set such that
u and v are adjacent in $\overline{G}$ if and only if they are not adjacent in G."
This is `Gᶜ`.

Definition 85 of Written on the Wall II reads: "A graph is said to have a
Hamiltonian path if there exist two vertices with a path between them which
visits each vertex of the graph exactly once." This is a walk `p` with
`p.IsHamiltonian`. For $n > 1$ the two ends of such a walk are distinct, as
definition 85 requires.

Definition 90 of Written on the Wall II reads: "A subset of the vertices, D_2, of
the graph is called a 2-dominating set of the graph if for every vertex v of the
graph, either in v is D_2 or v is adjacent to 2 vertices of D_2. The 2-domination
number of a graph is the size of a smallest 2-dominating set of the graph." (The
catalogue writes the subscripts and italics in HTML; subscripts are written here
with `_`.) "Adjacent to 2 vertices" is read as "adjacent to at least two
vertices", the standard meaning; this is `IsTwoDominating`.

Here $n$ is `Fintype.card V`, $\gamma_2(\overline{G})$ is
`twoDominationNumber Gᶜ`, and the lower median of the degree sequence of
$\overline{G}$ is `lowerMedianDegree Gᶜ` (definition 68). For odd $n$ that is the
middle term $d_{(n+1)/2}$, not the term $d_{(n+1)/2+1}$ that the text of definition 68
names; see `lowerMedianDegree`. The literal reading is `conjecture213.variants.literal`.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-23-000036"]
theorem conjecture213 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hn : 1 < Fintype.card V)
    (h : 2 + lowerMedianDegree Gᶜ ≤ twoDominationNumber Gᶜ) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  sorry

/--
WOWII Conjecture 213 with the literal reading of definition 68: the lower median of
the degree sequence of $\overline{G}$ is `lowerMedianDegreeLiteral Gᶜ`, which for odd
$n$ is the term $d_{(n+1)/2+1}$ that the text of definition 68 names. Everything else
is as in `conjecture213`. This follows from `conjecture213`, because the literal term
is never smaller than the middle term, so the hypothesis here is the stronger one.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-23-000036"]
theorem conjecture213.variants.literal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hn : 1 < Fintype.card V)
    (h : 2 + lowerMedianDegreeLiteral Gᶜ ≤ twoDominationNumber Gᶜ) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  sorry

-- Sanity checks

/-- The path on three vertices, `0 - 1 - 2`. -/
abbrev path3 : SimpleGraph (Fin 3) := SimpleGraph.fromRel fun i j => j.val = i.val + 1

/-- The star $K_{1,3}$ with centre `0`. -/
abbrev star3 : SimpleGraph (Fin 4) := SimpleGraph.fromRel fun i _ => i = 0

/-- The star $K_{1,3}$ has degrees `1, 1, 1, 3`; $n = 4$ is even, so both readings give
$d_2 = 1$. -/
@[category test, AMS 5]
example : lowerMedianDegree star3 = 1 ∧ lowerMedianDegreeLiteral star3 = 1 := by
  have h : sortedDegrees star3 = [1, 1, 1, 3] :=
    List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _) (by decide)
      (Multiset.coe_eq_coe.mp (by rw [sortedDegrees, Multiset.sort_eq]; decide))
  simp only [lowerMedianDegree, lowerMedianDegreeLiteral, sortedDegree, h]
  decide

/-- The path on three vertices has degrees `1, 1, 2`; $n = 3$ is odd, so the middle term
is $d_2 = 1$, while the literal reading takes $d_{(3+1)/2+1} = d_3 = 2$. -/
@[category test, AMS 5]
example : lowerMedianDegree path3 = 1 ∧ lowerMedianDegreeLiteral path3 = 2 := by
  have h : sortedDegrees path3 = [1, 1, 2] :=
    List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _) (by decide)
      (Multiset.coe_eq_coe.mp (by rw [sortedDegrees, Multiset.sort_eq]; decide))
  simp only [lowerMedianDegree, lowerMedianDegreeLiteral, sortedDegree, h]
  decide

/-- $K_2$ satisfies the hypothesis: its complement has degrees `0, 0`, so the lower
median is $d_1 = 0$, and a 2-dominating set of the complement must contain both
vertices, so $\gamma_2 = 2$. -/
@[category test, AMS 5]
example : 2 + lowerMedianDegree (⊤ : SimpleGraph (Fin 2))ᶜ ≤
    twoDominationNumber (⊤ : SimpleGraph (Fin 2))ᶜ := by
  have h : sortedDegrees (⊤ : SimpleGraph (Fin 2))ᶜ = [0, 0] :=
    List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _) (by decide)
      (Multiset.coe_eq_coe.mp (by rw [sortedDegrees, Multiset.sort_eq]; decide))
  have hm : lowerMedianDegree (⊤ : SimpleGraph (Fin 2))ᶜ = 0 := by
    simp only [lowerMedianDegree, sortedDegree, h]
    decide
  have key : ∀ D : Finset (Fin 2),
      IsTwoDominating (⊤ : SimpleGraph (Fin 2))ᶜ D → 2 ≤ D.card := by
    unfold IsTwoDominating
    decide
  rw [hm]
  exact le_csInf ⟨2, Finset.univ, by unfold IsTwoDominating; decide, by simp⟩
    (by rintro n ⟨D, hD, rfl⟩; exact key D hD)

/-- The path on three vertices has a Hamiltonian path, `0 - 1 - 2`. -/
@[category test, AMS 5]
example : ∃ a b : Fin 3, ∃ p : path3.Walk a b, p.IsHamiltonian :=
  ⟨0, 2, .cons (v := 1) (by decide) (.cons (v := 2) (by decide) .nil), by
    unfold Walk.IsHamiltonian
    decide⟩

end WrittenOnTheWallII.GraphConjecture213
