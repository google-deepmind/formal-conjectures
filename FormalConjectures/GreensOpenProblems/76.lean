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
# Ben Green's Open Problem 76

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.76)
- [AES10] Aronov, Boris, Esther Ezra, and Micha Sharir. "Small-size $\varepsilon$-nets for
  axis-parallel rectangles and boxes." SIAM Journal on Computing 39.7 (2010): 3248-3282.
  [doi:10.1137/090762968](https://doi.org/10.1137/090762968)
- [PT11] Pach, János. "Boxes and the art of $\varepsilon$-net maintenance." Invited problems,
  2nd Emléktábla Workshop (2011), Problem 5 (Pach and Tardos).
  [PDF](https://www.renyi.hu/~emlektab/emlektabla2withresults.pdf)
- [PT13] Pach, János, and Gábor Tardos. "Tight lower bounds for the size of epsilon-nets."
  Journal of the American Mathematical Society 26.3 (2013): 645-658.
  [doi:10.1090/S0894-0347-2012-00759-0](https://doi.org/10.1090/S0894-0347-2012-00759-0),
  [arXiv:1012.1240](https://arxiv.org/abs/1012.1240)
-/

@[expose] public section

open scoped Finset

namespace Green76

/--
`HitsRichRectangles k A A'` says that every closed axis-parallel rectangle that contains at least
$k$ points of $A$ also contains a point of $A'$.

For $a = (a_1, a_2)$ and $b = (b_1, b_2)$, `Set.Icc a b` is the rectangle
$[a_1, b_1] \times [a_2, b_2]$. It is empty if $a_1 > b_1$ or $a_2 > b_2$, and it can be a segment
or a point.
-/
def HitsRichRectangles (k : ℕ) (A A' : Finset (ℝ × ℝ)) : Prop :=
  ∀ a b : ℝ × ℝ, k ≤ #{p ∈ A | p ∈ Set.Icc a b} → ∃ p ∈ A', p ∈ Set.Icc a b

/--
Let $A$ be a set of $n$ points in the plane. Can one select a set $A'$ of $n/2$ points, with the
property that any axis-parallel rectangle containing $1000$ points of $A$ contains at least one
point of $A'$?

We read "a set of $n/2$ points" as at most $\lfloor n/2 \rfloor$ points, and "containing $1000$
points" as containing at least $1000$ points. The points of $A'$ need not lie in $A$. If
$A' \subseteq A$ is required, then the answer is no; see `green_76.variants.subset`.
-/
@[category research open, question, AMS 5 52]
theorem green_76 :
    ∀ A : Finset (ℝ × ℝ), ∃ A', #A' ≤ #A / 2 ∧ HitsRichRectangles 1000 A A' := by
  sorry

/--
Is there a constant $k$ such that the answer to `green_76` is yes with $1000$ replaced by $k$?
[PT11, Problem 5] asks this in an equivalent form, with $k = C + 1$: is there a constant $C$ such
that every set of $n$ points in the plane has a set $Y$ of $n/2$ points such that every
axis-parallel rectangle disjoint from $Y$ contains at most $C$ of the $n$ points?

Each of `green_76` and `green_76.variants.weak_net` implies this.
-/
@[category research open, question, AMS 5 52]
theorem green_76.variants.exists_constant :
    ∃ k : ℕ, ∀ A : Finset (ℝ × ℝ), ∃ A', #A' ≤ #A / 2 ∧ HitsRichRectangles k A A' := by
  sorry

/--
Do weak $\varepsilon$-nets of size $O(1/\varepsilon)$ exist for axis-parallel rectangles in the
plane? [Gr24] believes that `green_76` is an instance of this question, which he states for
axis-parallel boxes. With $k = \varepsilon n$: is there a constant $C$ such that, for every
$k \ge 1$, every set $A$ of $n$ points in the plane has a set $A'$ of at most $Cn/k$ points that
meets every axis-parallel rectangle containing at least $k$ points of $A$?

A positive answer implies `green_76.variants.exists_constant`, and it implies `green_76` if the
constant $C$ is at most $500$. [AES10, Theorem 2.2] gives such sets of size
$O(\varepsilon^{-1} \log \log \varepsilon^{-1})$, even with $A' \subseteq A$. When
$A' \subseteq A$ is required, this size is optimal [PT13, Theorem 4].
-/
@[category research open, question, AMS 5 52]
theorem green_76.variants.weak_net :
    ∃ C : ℝ, ∀ k : ℕ, 0 < k → ∀ A : Finset (ℝ × ℝ),
      ∃ A', #A' ≤ C * #A / k ∧ HitsRichRectangles k A A' := by
  sorry

/--
If $A'$ is required to be a subset of $A$, then the answer to `green_76` is no, even with $1000$
replaced by any constant. [Gr24] attributes this remark to Alon. It follows from
[PT13, Lemma 4.1], which [Gr24] cites as Lemma 3.1, its number in the arXiv version.
-/
@[category research solved, AMS 5 52]
theorem green_76.variants.subset :
    ¬ ∃ k : ℕ, ∀ A : Finset (ℝ × ℝ), ∃ A' ⊆ A, #A' ≤ #A / 2 ∧ HitsRichRectangles k A A' := by
  sorry

/--
The answer to `green_76` is yes if $1000$ is replaced by $C \log \log n$ [Gr24]. This follows
from [AES10, Theorem 2.2], which gives $\varepsilon$-nets of size
$O(\varepsilon^{-1} \log \log \varepsilon^{-1})$ for axis-parallel rectangles. These nets are
subsets of $A$. The hypothesis $n \ge 3$ ensures that $\log \log n > 0$.
-/
@[category research solved, AMS 5 52]
theorem green_76.variants.subset_log_log :
    ∃ C : ℝ, ∀ A : Finset (ℝ × ℝ), 3 ≤ #A → ∃ A' ⊆ A,
      #A' ≤ #A / 2 ∧ HitsRichRectangles ⌈C * Real.log (Real.log #A)⌉₊ A A' := by
  sorry

/-- `HitsRichRectangles` is preserved by raising the threshold $k$ and by enlarging $A'$. -/
@[category API, AMS 5 52]
theorem HitsRichRectangles.mono {k l : ℕ} {A A' B : Finset (ℝ × ℝ)}
    (h : HitsRichRectangles k A A') (hkl : k ≤ l) (hB : A' ⊆ B) :
    HitsRichRectangles l A B := by
  intro a b hab
  obtain ⟨p, hp, hpR⟩ := h a b (hkl.trans hab)
  exact ⟨p, hB hp, hpR⟩

/-- For $k \ge 1$, the set $A$ itself satisfies `HitsRichRectangles k A A`. -/
@[category API, AMS 5 52]
theorem hitsRichRectangles_self {k : ℕ} (hk : 0 < k) (A : Finset (ℝ × ℝ)) :
    HitsRichRectangles k A A := by
  intro a b hab
  obtain ⟨p, hp⟩ := Finset.card_pos.1 (hk.trans_le hab)
  exact ⟨p, Finset.mem_filter.1 hp⟩

/--
If $|A| < k$, then every $A'$ satisfies `HitsRichRectangles k A A'`. So `green_76` only has
content for $n \ge 1000$.
-/
@[category API, AMS 5 52]
theorem hitsRichRectangles_of_card_lt {k : ℕ} {A : Finset (ℝ × ℝ)} (A' : Finset (ℝ × ℝ))
    (h : #A < k) : HitsRichRectangles k A A' := by
  intro a b hab
  have := hab.trans (Finset.card_filter_le A _)
  omega

/--
`HitsRichRectangles 0 A A'` never holds. So $k = 0$ is not a trivial witness for
`green_76.variants.exists_constant`.
-/
@[category test, AMS 5 52]
theorem not_hitsRichRectangles_zero (A A' : Finset (ℝ × ℝ)) :
    ¬ HitsRichRectangles 0 A A' := by
  intro h
  obtain ⟨p, -, hp⟩ := h (1, 1) (0, 0) (Nat.zero_le _)
  have := hp.1.trans hp.2
  norm_num [Prod.le_def] at this

end Green76
