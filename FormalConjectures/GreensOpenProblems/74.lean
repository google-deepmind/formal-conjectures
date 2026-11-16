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
# Ben Green's Open Problem 74

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.74)
-/

@[expose] public section

open Filter Asymptotics
open scoped Finset

namespace Green74

/-- `embed x` is the point $x \in \mathbb{N}^d$ viewed as a point of $\mathbb{R}^d$. -/
def embed {d : ℕ} (x : Fin d → ℕ) : Fin d → ℝ :=
  fun i ↦ (x i : ℝ)

/--
`NoFiveCoplanar A` says that no $5$ points of `A` lie on a $2$-plane of $\mathbb{R}^d$: no
$5$-element subset of `A` is coplanar, that is, contained in an affine subspace of dimension at
most $2$.
-/
def NoFiveCoplanar {d : ℕ} (A : Finset (Fin d → ℕ)) : Prop :=
  ∀ S ⊆ A, #S = 5 → ¬ Coplanar ℝ (embed '' (S : Set (Fin d → ℕ)))

/--
`maxNoFiveCoplanar d N` is $f(d, N)$, the size of the largest subset of $[N]^d$ with no $5$
points on a $2$-plane, where $[N] = \{1, \dots, N\}$. The set of possible sizes contains $0$ and is
bounded by $N^d$ (`maxNoFiveCoplanar_le`), so the supremum is a maximum.
-/
noncomputable def maxNoFiveCoplanar (d N : ℕ) : ℕ :=
  sSup {m | ∃ A ⊆ Fintype.piFinset (fun _ : Fin d ↦ Finset.Icc 1 N), #A = m ∧ NoFiveCoplanar A}

/-- $f(d, N) \le N^d$, the size of the grid $[N]^d$. -/
@[category API, AMS 5 52]
theorem maxNoFiveCoplanar_le (d N : ℕ) : maxNoFiveCoplanar d N ≤ N ^ d := by
  refine csSup_le' ?_
  rintro m ⟨A, hA, rfl, -⟩
  calc #A ≤ #(Fintype.piFinset fun _ : Fin d ↦ Finset.Icc 1 N) := Finset.card_le_card hA
    _ = N ^ d := by simp

def green_74.answer : ℕ → ℕ → ℕ := sorry

/--
What is the largest subset of $[N]^d$ with no $5$ points on a $2$-plane?

Here $[N] = \{1, \dots, N\}$ as in [Gr24], and a $2$-plane is a $2$-dimensional affine subspace of
$\mathbb{R}^d$. We ask for the size $f(d, N)$ of a largest such subset (`maxNoFiveCoplanar`) as a
function of $d$ and $N$; for its order of growth in $N$ see `green_74.variants.order`. For
$d \le 2$ any $5$ points are coplanar, so then $f(d, N) \le 4$.
-/
@[category research open, question value, AMS 5 52]
theorem green_74 : ∀ d N : ℕ, maxNoFiveCoplanar d N = green_74.answer d N := by
  sorry

def green_74.variants.order.answer : ℕ → ℕ → ℝ := sorry

/--
For fixed $d$, what is the order of magnitude of $f(d, N)$, the size of the largest subset of
$[N]^d$ with no $5$ points on a $2$-plane, as $N \to \infty$?

This asks for `green_74` up to constant factors that may depend on $d$.
-/
@[category research open, question value, AMS 5 52]
theorem green_74.variants.order :
    ∀ d : ℕ, (fun N ↦ (maxNoFiveCoplanar d N : ℝ)) =Θ[atTop] green_74.variants.order.answer d := by
  sorry

/--
[Gr24] writes: "I do not know if there can be such a set of size $N^{d-100}$." We read this as
the question whether, for every $d$, $f(d, N) \ge N^{d - 100}$ for all sufficiently large $N$.

The exponent uses truncated subtraction, so the case $d \le 100$ is trivial. For $d \ge 2$,
$[N]^d$ is covered by $N^{d-2}$ parallel coordinate $2$-planes, so $f(d, N) \le 4N^{d-2}$; the
question is whether the loss in the exponent can be kept at $100$ for every $d$ (Green's $100$
presumably stands for an absolute constant).
-/
@[category research open, question, AMS 5 52]
theorem green_74.variants.large :
    ∀ d : ℕ, ∀ᶠ N in atTop, N ^ (d - 100) ≤ maxNoFiveCoplanar d N := by
  sorry

end Green74
