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
# Erdős Problem 733

*References:*
- [erdosproblems.com/733](https://www.erdosproblems.com/733)
- [Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*.
  Combinatorica (1981), 25-42. [PDF](https://www.renyi.hu/~p_erdos/1981-16.pdf)
- [SzTr83] Szemerédi, E. and Trotter, Jr., W. T., *Extremal problems in discrete geometry*.
  Combinatorica (1983), 381-392.
-/

@[expose] public section

open EuclideanGeometry Filter Topology

namespace Erdos733

/-- A line in the plane: a nonempty affine subspace of $\mathbb{R}^2$ of dimension one.
(The nonemptiness is implied by `IsLine`, see `nonempty_of_isLine`.) -/
abbrev Line : Type :=
  {ℓ : AffineSubspace ℝ ℝ² // (ℓ : Set ℝ²).Nonempty ∧ IsLine ℓ}

/-- If `ℓ` satisfies `IsLine`, then `ℓ` is nonempty: the direction of the empty subspace `⊥` is
trivial, so it has dimension $0$ and not $1$. -/
@[category API, AMS 5 52]
theorem nonempty_of_isLine {ℓ : AffineSubspace ℝ ℝ²} (h : IsLine ℓ) :
    (ℓ : Set ℝ²).Nonempty := by
  rw [AffineSubspace.nonempty_iff_ne_bot]
  rintro rfl
  rw [IsLine, AffineSubspace.direction_bot, finrank_bot] at h
  exact zero_ne_one h

open scoped Classical in
/-- The number of points of the finite set `P` that lie on the line `ℓ`. -/
noncomputable def lineCount (P : Finset ℝ²) (ℓ : Line) : ℕ :=
  (P.filter fun p ↦ p ∈ (ℓ.1 : AffineSubspace ℝ ℝ²)).card

/-- The multiset of the numbers of points of `P` on the (distinct) lines in `L`. Lines with the
same number of points are kept with multiplicity. -/
noncomputable def lineSizeMultiset (P : Finset ℝ²) (L : Finset Line) : Multiset ℕ :=
  L.val.map (lineCount P)

/-- The nondecreasing list $X_1\leq\cdots\leq X_m$ of the numbers of points of `P` on the lines
in `L`, i.e. the sorted version of `lineSizeMultiset P L`. -/
noncomputable def lineSizeSequence (P : Finset ℝ²) (L : Finset Line) : List ℕ :=
  (lineSizeMultiset P L).sort (· ≤ ·)

/-- A sequence `X` is line-compatible for $n$ if there is a set `P` of $n$ points of
$\mathbb{R}^2$ and a finite set `L` of distinct lines, each containing at least two points of
`P`, such that `X` lists the numbers of points of `P` on the lines of `L` in nondecreasing
order. -/
def LineCompatible (n : ℕ) (X : List ℕ) : Prop :=
  ∃ P : Finset ℝ², P.card = n ∧
    ∃ L : Finset Line, (∀ ℓ ∈ L, 2 ≤ lineCount P ℓ) ∧ X = lineSizeSequence P L

/-- The set of line-compatible sequences for $n$ points. -/
def compatibleSequences (n : ℕ) : Set (List ℕ) :=
  {X | LineCompatible n X}

/-- Erdős's original count [Er81]: the sequences obtained from *all* the lines determined by a
set `P` of $n$ points, i.e. `L` is exactly the set of lines containing at least two points of
`P`. These form a subset of `compatibleSequences n`. -/
def allLinesSequences (n : ℕ) : Set (List ℕ) :=
  {X | ∃ P : Finset ℝ², P.card = n ∧
    ∃ L : Finset Line, (∀ ℓ : Line, ℓ ∈ L ↔ 2 ≤ lineCount P ℓ) ∧ X = lineSizeSequence P L}

set_option linter.style.formal_proof_palomar false in
/--
Call a sequence $1<X_1\leq\cdots\leq X_m\leq n$ line-compatible if there is a set of $n$ points in
$\mathbb{R}^2$ such that there are $m$ lines $\ell_1,\ldots,\ell_m$ containing at least two
points, and the number of points on $\ell_i$ is exactly $X_i$.

Prove that there are at most
$$\exp(O(n^{1/2}))$$
many line-compatible sequences.

Asked by Erdős [Er81] and proved by Szemerédi and Trotter [SzTr83]. We take the lines $\ell_i$ to
be distinct but not necessarily all the lines determined by the points, as on erdosproblems.com;
[Er81] uses all the determined lines (`allLinesSequences`), so this bound implies his. Finiteness
of the set is part of the statement, since `Set.ncard` of an infinite set is $0$.
-/
@[category research solved, AMS 5 52, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos733.lean#L41"]
theorem erdos_733 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (compatibleSequences n).Finite ∧
        ((compatibleSequences n).ncard : ℝ) ≤ Real.exp (C * Real.sqrt n) := by
  sorry

/--
Erdős [Er81] writes that it is 'easy' to prove there are at least
$$\exp(cn^{1/2})$$
many such sequences for some constant $c>0$, but expected proving the upper bound to be
difficult. Once it is done, he asked for the existence and value of
$$\lim_{n\to \infty}\frac{\log f(n)}{n^{1/2}},$$
where $f(n)$ counts the number of line-compatible sequences. Does this limit exist?

In [Er81], $f(n)$ counts the sequences of the numbers of points on all the lines determined by
$n$ points, i.e. `(allLinesSequences n).ncard`; this set is finite, as a subset of
`compatibleSequences n`.
-/
@[category research open, question, AMS 5 52]
theorem erdos_733.variants.limit_exists :
    ∃ c : ℝ, Tendsto
      (fun n : ℕ ↦ Real.log ((allLinesSequences n).ncard : ℝ) / Real.sqrt n)
      atTop (𝓝 c) := by
  sorry

end Erdos733
