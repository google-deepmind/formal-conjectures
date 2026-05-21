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
- [OEIS A001411](https://oeis.org/A001411) — SAWs on the square lattice $\mathbb{Z}^2$
- [OEIS A001412](https://oeis.org/A001412) — SAWs on the simple cubic lattice $\mathbb{Z}^3$
- [OEIS A001413](https://oeis.org/A001413) — SAWs on the four-dimensional hypercubic lattice $\mathbb{Z}^4$
-/

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
**Enumeration of self-avoiding walks (open).**  No closed-form formula is currently known
that yields $c_n(\mathbb{Z}^d)$ for arbitrary $d$ and $n$.  We formalise the question as
asking for the value of the function $c_n$ itself.
-/
@[category research open, AMS 5 68]
theorem self_avoiding_walk_closed_form : cN = answer(sorry) := by
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
**Smallest unknown value on the square lattice (open).**  The number of self-avoiding
walks of length $80$ on $\mathbb{Z}^2$ is the smallest value of $c_n(\mathbb{Z}^2)$ that is
not yet known: as of the most recent enumerations of Iwan Jensen, the sequence
[OEIS A001411](https://oeis.org/A001411) is known up to $n = 79$.
-/
@[category research open, AMS 5 68]
theorem cN_two_eighty : cN 2 80 = answer(sorry) := by
  sorry

end SelfAvoidingWalk
