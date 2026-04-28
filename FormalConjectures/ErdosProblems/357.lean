/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 357

*Reference:* [erdosproblems.com/357](https://www.erdosproblems.com/357)
-/

namespace Erdos357

open Filter Asymptotics

def HasDistinctSums {ι α : Type*} [Preorder ι] [AddCommMonoid α] (a : ι → α) : Prop :=
  {J : Finset ι | (J : Set ι).OrdConnected}.InjOn (fun J ↦ ∑ x ∈ J, a x)

/-- Let $f(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 < \dotsc < a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℤ, Set.range a ⊆ Set.Icc 1 n ∧ StrictMono a ∧ HasDistinctSums a}

/-- Let $f(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 < \dotsc < a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. Is $f(n)=o(n)$? -/
@[category research open, AMS 11]
theorem erdos_357.parts.i : (fun n ↦ (f n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ)) := by
  sorry

/-
Formalisation note: the next 5 formalisations are an attempt at capturing the question "how does
$f(n)$ grow?". In addition to trivial solutions (e.g. setting `answer(sorry) = 0` in some of these),
it is possible that some of these admit easy solutions that shouldn't count as genuine solutions.
As usual in this repo, solving this problem is not simply providing a term to replace `answer(sorry)`
together with a proof of the theorem, but providing a *mathematically interesting* answer.
Note also that there might be other reasonable (and non equivalent) formal statements that capture this
question.
Similar remarks hold for the `variants.monotone` formalisations later in this file.
-/

/-- Let $f(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 < \dotsc < a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct.
How does $f(n)$ grow? Can we find a (good) explicit function $g$ such that $g = O(f)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.parts.ii.bigO_version :
    (answer(sorry) : ℕ → ℝ) =O[atTop] (fun n ↦ (f n : ℝ)) := by
  sorry

/-- Let $f(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 < \dotsc < a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct.
How does $f(n)$ grow? Can we find a (good) explicit function $g$ such that $f = O(g)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.parts.ii.bigO_version_symm :
    (fun n ↦ (f n : ℝ)) =O[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/-- Let $f(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 < \dotsc < a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct.
How does $f(n)$ grow? Can we find a (good) explicit function $g$ such that $f = \Theta(g)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.parts.ii.bigTheta_version :
    (fun n ↦ (f n : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/-- Let $f(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 < \dotsc < a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct.
How does $f(n)$ grow? Can we find a (good) explicit function $g$ such that $g = o(f)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.parts.ii.littleO_version :
    (answer(sorry) : ℕ → ℝ) =o[atTop] (fun n ↦ (f n : ℝ)) := by
  sorry

/-- Let $f(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 < \dotsc < a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct.
How does $f(n)$ grow? Can we find a (good) explicit function $g$ such that $f = o(g)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.parts.ii.littleO_version_symm :
    (fun n ↦ (f n : ℝ)) =o[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/-- Let $f(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 < \dotsc < a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct.
It is known that $f(n) \geq (2+o(1))\sqrt{n}$.
Source: See comment by Desmond Weisenberg here: https://www.erdosproblems.com/forum/thread/357.
-/
@[category research solved, AMS 11]
theorem erdos_357.variants.weisenberg : ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ n in atTop, (2 + o n) * √n ≤ f n := by
  sorry

/-- Suppose $A$ is an infinite set such that all finite sums of consecutive terms of $A$ are distinct.
Then $A$ has lower density 0. -/
@[category research solved, AMS 11]
theorem erdos_357.variants.infinite_set_lower_density (A : ℕ → ℕ) (hA : StrictMono A)
    (hA : HasDistinctSums A) : (Set.range A).lowerDensity = 0 := by
  sorry

/--  Suppose $A$ is an infinite set such that all finite sums of consecutive terms of $A$ are distinct.
Then it is conjectured that $A$ has density 0. -/
@[category research open, AMS 11]
theorem erdos_357.variants.infinite_set_density (A : ℕ → ℕ) (hA : StrictMono A)
    (hA : HasDistinctSums A) :
    (Set.range A).HasDensity 0 := by
  sorry


/-- Suppose $A$ is an infinite set such that all finite sums of consecutive terms of $A$ are distinct.
Then it is conjectured that the sum $\sum_k \frac{1}{a_k}$ converges. -/
@[category research open, AMS 11]
theorem erdos_357.variants.infinite_set_sum (A : ℕ → ℕ) (hA : StrictMono A)
    (hA : HasDistinctSums A) :
    Summable (fun i ↦ (1 : ℝ) / A i) := by
  sorry

/-- Let $g(n)$ be the maximal $k$ such that there exist integers $1 \le a_1, \dotsc, a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℕ, (Set.range a ⊆ Set.Icc 1 n) ∧ HasDistinctSums a}

/-- Let $g(n)$ be the maximal $k$ such that there exist integers $1 \le a_1, \dotsc, a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. It is known that
$$\left(\frac 1 3 + o(1) \right)n \leq g(n) \leq \left(\frac 2 3 + o(1) \right)n.$$ -/
@[category research open, AMS 11]
theorem erdos_357.variants.hegyvari : ∃ (o o' : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    o' =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ n in atTop, (g n : ℝ) ∈ Set.Icc ((1 / 3 + o n) * n) ((2 / 3 + o' n)*n) := by
  sorry

/-- Let $h(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 \leq \dotsc \leq a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. -/
noncomputable def h (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℤ, Set.range a ⊆ Set.Icc 1 n ∧ Monotone a ∧ HasDistinctSums a}

-- The analogous question assuming only monotonicity of the $a_i$. The wording of the website
-- suggests that this is open, though it's not clear whether the difficulty is the same as for the
-- strictly monotone case.

/-- Let $h(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 \leq \dotsc \leq a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. Is $h(n)=o(n)$? -/
@[category research open, AMS 11]
theorem erdos_357.variants.monotone.parts.i : (fun n ↦ (h n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ)) := by
  sorry

/-- Let $h(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 \leq \dotsc \leq a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. How does $h(n)$ grow?
Can we find a (good) explicit function $g$ such that $g = O(h)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.variants.monotone.parts.ii.bigO_version :
    (answer(sorry) : ℕ → ℝ) =O[atTop] (fun n ↦ (h n : ℝ)) := by
  sorry

/-- Let $h(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 \leq \dotsc \leq a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. How does $h(n)$ grow?
Can we find a (good) explicit function $g$ such that $h = O(g)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.variants.monotone.parts.ii.bigO_version_symm :
    (fun n ↦ (h n : ℝ)) =O[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/-- Let $h(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 \leq \dotsc \leq a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. How does $h(n)$ grow?
Can we find a (good) explicit function $g$ such that $h = \Theta(g)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.variants.monotone.parts.ii.bigTheta_version :
    (fun n ↦ (h n : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/-- Let $h(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 \leq \dotsc \leq a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. How does $h(n)$ grow?
Can we find a (good) explicit function $g$ such that $g = o(h)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.variants.monotone.parts.ii.littleO_version :
    (answer(sorry) : ℕ → ℝ) =o[atTop] (fun n ↦ (h n : ℝ)) := by
  sorry

/-- Let $h(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 \leq \dotsc \leq a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. How does $h(n)$ grow?
Can we find a (good) explicit function $g$ such that $h = o(g)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.variants.monotone.parts.ii.littleO_version_symm :
    (fun n ↦ (h n : ℝ)) =o[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

-- TODO(Paul-Lez): add results from last paragraph of the page.

end Erdos357
