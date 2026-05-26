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
# Enumeration of Self-Avoiding Walks on Lattices

A *self-avoiding walk* (SAW) of length $n$ on a graph $G$ is a sequence of vertices
$v_0, v_1, \ldots, v_n$ where consecutive vertices are adjacent and all vertices are distinct
(the walk does not visit any vertex twice).  Let $c_n(G)$ denote the number of self-avoiding
walks of length $n$ on $G$ starting at a fixed origin.

**Open Problem.**  Does there exist a closed-form formula or a general computable algorithm
that yields $c_n(L)$ for arbitrary lattices $L$ and arbitrary path lengths $n$?  No such
formula is currently known.  Computational enumeration has extended explicit values to large
$n$ on specific lattices (e.g. length 79 on the square lattice $\mathbb{Z}^2$, due to
Iwan Jensen).

The *connective constant* $\mu(L) = \lim_{n \to \infty} c_n(L)^{1/n}$ controls the exponential
growth rate of $c_n(L)$.  It is explicitly known only for the hexagonal lattice, where
Duminil-Copin and Smirnov (2012) proved $\mu = \sqrt{2 + \sqrt{2}}$.

*References:*

- [Self-avoiding walk (Wikipedia)](https://en.wikipedia.org/wiki/Self-avoiding_walk)
- [Self-Avoiding Walk (MathWorld)](https://mathworld.wolfram.com/Self-AvoidingWalk.html)
- [Lectures on Self-Avoiding Walks, Bauerschmidt-Duminil-Copin-Goodman-Slade](https://www.ihes.fr/~duminil/publi/saw_lecture_notes.pdf)
- [The Self-Avoiding Walk, Madras and Slade (1993)](https://doi.org/10.1007/978-1-4614-6025-1)
- [Exact critical point and critical exponents of O(n) models in two dimensions, Nienhuis (1982)](https://doi.org/10.1103/PhysRevLett.49.1062)
- [The connective constant of the honeycomb lattice equals √(2 + √2), Duminil-Copin and Smirnov (2012)](https://arxiv.org/abs/1007.0575)
- [OEIS A001411](https://oeis.org/A001411) — SAWs on the square lattice $\mathbb{Z}^2$
- [OEIS A001412](https://oeis.org/A001412) — SAWs on the simple cubic lattice $\mathbb{Z}^3$
- [OEIS A001413](https://oeis.org/A001413) — SAWs on the four-dimensional hypercubic lattice $\mathbb{Z}^4$
-/

open Filter

open scoped Topology

namespace SelfAvoidingWalk

/--
The integer lattice graph $\mathbb{Z}^d$, whose vertices are points of $\mathbb{Z}^d$ and
whose edges connect points that differ by $\pm 1$ in exactly one coordinate.
-/
def integerLattice (d : ℕ) : SimpleGraph (Fin d → ℤ) where
  Adj a b := ∃ i : Fin d, (∀ j, j ≠ i → a j = b j) ∧ |a i - b i| = 1
  symm := by
    rintro a b ⟨i, hj, hi⟩
    refine ⟨i, fun j hji => (hj j hji).symm, ?_⟩
    rw [abs_sub_comm]; exact hi
  loopless := by
    rintro a ⟨i, _, hi⟩
    simp at hi

/--
The hexagonal (honeycomb) lattice, in its *brick-wall* presentation on $\mathbb{Z}^2$.  The
vertices are the points of $\mathbb{Z}^2$; every point is joined to its two horizontal neighbours
$(x \pm 1, y)$, and a vertical edge joins $(x, y)$ to $(x, y + 1)$ exactly when $x + y$ is even.
The resulting graph is $3$-regular and isomorphic to the honeycomb lattice: its bounded faces are
hexagons, for instance $(0,0), (1,0), (2,0), (2,1), (1,1), (0,1)$.
-/
def hexagonalLattice : SimpleGraph (ℤ × ℤ) where
  Adj a b :=
    (|a.1 - b.1| = 1 ∧ a.2 = b.2) ∨
      (a.1 = b.1 ∧ |a.2 - b.2| = 1 ∧ Even (a.1 + min a.2 b.2))
  symm := by
    rintro a b (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨by rw [abs_sub_comm]; exact h1, h2.symm⟩
    · refine Or.inr ⟨h1.symm, by rw [abs_sub_comm]; exact h2, ?_⟩
      rw [← h1, min_comm]
      exact h3
  loopless := by
    rintro a (⟨h, -⟩ | ⟨-, h, -⟩) <;> simp at h

-- TODO: a uniform treatment of arbitrary crystallographic lattices, e.g. Bravais lattices via
-- `IsZLattice` together with an extra basis for non-Bravais lattices such as the honeycomb, would
-- let the connective constant range over all lattices at once, generalising both `integerLattice`
-- and `hexagonalLattice`.

/--
The number of self-avoiding walks of length $n$ on a simple graph $G$, starting at vertex
$v$.  A self-avoiding walk is a walk whose vertex sequence has no repetition, modelled as a
`SimpleGraph.Walk` whose support list is `Nodup` (i.e. `IsPath`).  The count is taken over
all possible endpoint vertices.
-/
noncomputable def numSAWFrom {V : Type*} (G : SimpleGraph V) (v : V) (n : ℕ) : ℕ :=
  Set.ncard {p : Σ u, G.Walk v u | p.2.IsPath ∧ p.2.length = n}

/--
The number of self-avoiding walks of length $n$ on the integer lattice $\mathbb{Z}^d$,
starting at the origin.
-/
noncomputable def cN (d n : ℕ) : ℕ :=
  numSAWFrom (integerLattice d) (0 : Fin d → ℤ) n

/--
The number of self-avoiding walks of length $n$ on the hexagonal (honeycomb) lattice, starting
at the origin.
-/
noncomputable def cHex (n : ℕ) : ℕ :=
  numSAWFrom hexagonalLattice (0, 0) n

/--
`IsConnectiveConstant G v μ` states that the real number `μ` is the *connective constant* of the
graph `G` based at the vertex `v`: writing $c_n$ for the number of self-avoiding walks of length
$n$ from `v`, the normalised counts $c_n^{1/n}$ converge to `μ`, i.e. $\mu = \lim_{n \to \infty}
c_n^{1/n}$.  This limit exists for every vertex-transitive graph by the submultiplicativity
$c_{m+n} \le c_m c_n$ (Hammersley and Morton), and is independent of the base vertex.
-/
def IsConnectiveConstant {V : Type*} (G : SimpleGraph V) (v : V) (μ : ℝ) : Prop :=
  Tendsto (fun n => (numSAWFrom G v n : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 μ)

/--
**Enumeration of self-avoiding walks (open).**  No closed-form formula is currently known
that yields $c_n(\mathbb{Z}^d)$ for arbitrary $d$ and $n$.  We formalise the question as
asking for the value of the function $c_n$ itself.
-/
@[category research open, AMS 5 68]
theorem self_avoiding_walk_closed_form : cN = answer(sorry) := by
  sorry

/--
The connective constant of the integer lattice $\mathbb{Z}^d$ exists: there is a real number to
which the normalised self-avoiding-walk counts $c_n(\mathbb{Z}^d)^{1/n}$ converge.  This is the
classical consequence of the submultiplicativity $c_{m+n} \le c_m c_n$ via Fekete's subadditive
lemma (Hammersley and Morton, 1954).
-/
@[category research solved, AMS 5 82]
theorem exists_isConnectiveConstant_integerLattice (d : ℕ) :
    ∃ μ : ℝ, IsConnectiveConstant (integerLattice d) (0 : Fin d → ℤ) μ := by
  sorry

/--
**Connective constant of the hexagonal lattice (Duminil-Copin and Smirnov, 2012).**  The
connective constant of the hexagonal (honeycomb) lattice equals $\sqrt{2 + \sqrt 2}$, confirming a
prediction of Nienhuis (1982).  This is the only lattice whose connective constant is known in
closed form.
-/
@[category research solved, AMS 5 82]
theorem isConnectiveConstant_hexagonalLattice :
    IsConnectiveConstant hexagonalLattice (0, 0) (Real.sqrt (2 + Real.sqrt 2)) := by
  sorry

/--
**Universality of the self-avoiding-walk critical exponent (open).**  The number of self-avoiding
walks of length $n$ is expected to grow as $c_n \sim A \mu^n n^{\gamma - 1}$, where the *critical
exponent* $\gamma$ is conjectured to be *universal*: it depends only on the dimension of the
lattice and not on its local structure.  In particular the square lattice $\mathbb{Z}^2$ and the
hexagonal lattice, both two-dimensional, should share a single exponent $\gamma$, predicted by
Nienhuis (1982) to equal $43/32$.
-/
@[category research open, AMS 5 82]
theorem saw_universality :
    answer(sorry) ↔ ∃ γ : ℝ,
      (∃ A μ : ℝ, 0 < A ∧ 0 < μ ∧
        Tendsto (fun n => (cN 2 n : ℝ) / (A * μ ^ n * (n : ℝ) ^ (γ - 1))) atTop (𝓝 1)) ∧
      (∃ A μ : ℝ, 0 < A ∧ 0 < μ ∧
        Tendsto (fun n => (cHex n : ℝ) / (A * μ ^ n * (n : ℝ) ^ (γ - 1))) atTop (𝓝 1)) := by
  sorry

/-- In $\mathbb{Z}^d$ (with $d \ge 1$), there are exactly $2d$ SAWs of length $1$ from the
origin: each of the $d$ coordinates contributes a $\pm 1$ step. -/
@[category test, AMS 5]
theorem cN_one (d : ℕ) (hd : 0 < d) : cN d 1 = 2 * d := by
  sorry

/-- $c_2(\mathbb{Z}^2) = 12$: on the square lattice there are exactly twelve SAWs of length
two (four first steps, each followed by three second steps that avoid the backtrack).
See [OEIS A001411](https://oeis.org/A001411). -/
@[category test, AMS 5]
theorem cN_two_dim_two : cN 2 2 = 12 := by
  sorry

/--
On the hexagonal lattice every vertex has degree $3$, so there are exactly $3$ self-avoiding walks
of length $1$ from the origin.
-/
@[category test, AMS 5]
theorem cHex_one : cHex 1 = 3 := by
  sorry

/--
**Smallest unknown value on the square lattice (open).**  The number of self-avoiding
walks of length $80$ on $\mathbb{Z}^2$ is the smallest value of $c_n(\mathbb{Z}^2)$ that is
not yet known: as of the most recent enumerations of Iwan Jensen, the sequence
[OEIS A001411](https://oeis.org/A001411) is known up to $n = 79$.
-/
@[category research open, AMS 5 68]
theorem cN_two_eighty : cN 2 80 = answer(sorry) := by
  sorry

end SelfAvoidingWalk
