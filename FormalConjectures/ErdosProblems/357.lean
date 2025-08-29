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
# Erdős Problem 358

*Reference:* [erdosproblems.com/358](https://www.erdosproblems.com/358)
-/

namespace Erdos357

open Filter Asymptotics

def IsInterval {α : Type*} [LE α] (A : Set α) (B : Set α := Set.univ) : Prop :=
    ∀ᵉ (a ∈ B) (b ∈ B) (c ∈ A),  a ≤ c → c ≤ b → c ∈ B

noncomputable def f (n : ℕ) : ℕ := sSup {k : ℕ | ∀ I ⊆ Finset.Icc 1 n, I.card = k → ∀ J ⊆ I,
    ∀ J' ⊆ I, IsInterval (α := ℕ) J I → IsInterval (α := ℕ) J' I → ∑ x ∈ J, x = ∑ x ∈ J', x → J = J'}

/-- Let $1 \le a_1 < \dotsc < a_k \le n$ be integers such that all sums of the shape
$\sum_{u \le i \le v} a_i$ are distinct. Let $f(n)$ be the maximal such $k$. Is $f(n)=o(n)$? -/
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
-/

/-- Let $1 \le a_1 < \dotsc < a_k \le n$ be integers such that all sums of the shape
$\sum_{u \le i \le v} a_i$ are distinct. How does $f(n)$ grow? Can we find a (good) explicit function
$g$ such that $g = O(f)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.parts.ii.bigO_version :
    (answer(sorry) : ℕ → ℝ) =O[atTop] (fun n ↦ (f n : ℝ)) := by
  sorry

/-- Let $1 \le a_1 < \dotsc < a_k \le n$ be integers such that all sums of the shape
$\sum_{u \le i \le v} a_i$ are distinct. How does $f(n)$ grow? Can we find a (good) explicit function
$g$ such that $g = O(f)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.parts.ii.bigO_version_symm :
    (fun n ↦ (f n : ℝ)) =O[atTop] (answer(sorry) : ℕ → ℝ)  := by
  sorry

/-- Let $1 \le a_1 < \dotsc < a_k \le n$ be integers such that all sums of the shape
$\sum_{u \le i \le v} a_i$ are distinct. How does $f(n)$ grow? Can we find a (good) explicit function
$g$ such that $f = θ(g)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.parts.ii.bigTheta_version :
    (fun n ↦ (f n : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/-- Let $1 \le a_1 < \dotsc < a_k \le n$ be integers such that all sums of the shape
$\sum_{u \le i \le v} a_i$ are distinct. How does $f(n)$ grow? Can we find a (good) explicit function
$g$ such that $g = o(f)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.parts.ii.littleO_version :
    (answer(sorry) : ℕ → ℝ) =o[atTop] (fun n ↦ (f n : ℝ)) := by
  sorry

/-- Let $1 \le a_1 < \dotsc < a_k \le n$ be integers such that all sums of the shape
$\sum_{u \le i \le v} a_i$ are distinct. How does $f(n)$ grow? Can we find a (good) explicit function
$g$ such that $f = o(g)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.parts.ii.littleO_version_symm :
    (fun n ↦ (f n : ℝ)) =o[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/-- Suppose $A$ is an infinite set such that all finite sums of consecutive terms of $A$ are distinct.
Then $A$ has lower density 0. -/
@[category research solved, AMS 11]
theorem erdos_357.variants.infinite_set_lower_density (A : ℕ → ℕ) (hA : StrictMono A)
    (hA : ∀ I J : Finset ℕ, ∑ i ∈ I, A i = ∑ j ∈ J, A j → I = J) :
    (Set.range A).lowerDensity = 0 := by
  sorry

/--  Suppose $A$ is an infinite set such that all finite sums of consecutive terms of $A$ are distinct.
Then it is conjectured that $A$ has density 0. -/
@[category research open, AMS 11]
theorem erdos_357.variants.infinite_set_density (A : ℕ → ℕ) (hA : StrictMono A)
    (hA : ∀ I J : Finset ℕ, ∑ i ∈ I, A i = ∑ j ∈ J, A j → I = J) :
    (Set.range A).HasDensity 0 := by
  sorry

/-- Suppose $A$ is an infinite set such that all finite sums of consecutive terms of $A$ are distinct.
Then it is conjectured that the sum $\sum_k \frac{1}{a_k}$ converges. -/
@[category research open, AMS 11]
theorem erdos_357.variants.infinite_set_sum (A : ℕ → ℕ) (hA : StrictMono A)
    (hA : ∀ I J : Finset ℕ, ∑ i ∈ I, A i = ∑ j ∈ J, A j → I = J) : Summable (1 / A) := by
  sorry

noncomputable def g (n : ℕ) : ℕ := sSup {k : ℕ | ∃ a : Fin k → ℕ, (∀ i, a i ∈ Set.Icc 1 n) ∧
    (∀ I J : Finset (Fin k), IsInterval (α := Fin k) I → IsInterval (α := Fin k) J →
      ∑ i ∈ I, a i = ∑ j ∈ J, a j → I = J)}

@[category research open, AMS 11]
theorem erdos_357.variants.hegyvari : ∃ (o o' : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    o' =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ n in atTop, (g n : ℝ) ∈ Set.Icc (1 / 3 + o n) (2 / 3 + o' n) := by
  sorry

--TODO(Paul-Lez): add non-strict monotone version of problem

end Erdos357
