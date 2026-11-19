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
# Erdős Problem 671
*Reference:* [erdosproblems.com/671](https://www.erdosproblems.com/671)
-/

@[expose] public section

namespace Erdos671

/-- The Lagrange Basis polynomials $p_k$ of the nodes `x 0, …, x (n - 1)`, evaluated at `t`:
$$p_k(t)=\frac{\prod_{i\neq k}(t-x_i)}{\prod_{i\neq k}(x_k-x_i)},$$
where $i$ and $k$ range over `Finset.range n`. If two nodes coincide, a denominator vanishes and
the value is the junk value `0`, so the statements below assume that the nodes are distinct. -/
noncomputable def lagrangeBasis (n : ℕ) (x : ℕ → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  (∏ i ∈ (Finset.range n).erase k, (t - x i)) / ∏ i ∈ (Finset.range n).erase k, (x k - x i)

/-- The Lebesgue function $L_n(t)=\sum_{k<n}\lvert p_k(t)\rvert$ of the first `n` nodes
`x 0, …, x (n - 1)`. -/
noncomputable def lebesgueFunction (n : ℕ) (x : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, |lagrangeBasis n x k t|

/-- The Lagrange Interpolation of a function $\mathcal{L}^nf(t) = \sum_{1\leq k\leq n}f(x_k)p_k(t)$
of the nodes `x 0, …, x (n - 1)`, evaluated at `t`. -/
noncomputable def lagrangeInterpolation (n : ℕ) (x : ℕ → ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (f (x k)) * (lagrangeBasis n x k t)


/-- Given $a_{i}^n\in [-1,1]$ for all $1\leq i\leq n<\infty$ such that for fixed $n$ the $a_{i}^n$
are pairwise disjoint, we define $p_{i}^n$ as the unique polynomial of degree at most $n-1$ such
that $p_{i}^n(a_{i}^n)=1$ and $p_{i}^n(a_{i'}^n)=0$ if $1\leq i'\leq n$ with $i\neq i'$. We similarly
define \[\mathcal{L}^nf(x) = \sum_{1\leq i\leq n}f(a_i^n)p_i^n(x),\] the unique polynomial of degree
at most $n-1$ which agrees with $f$ on $a_i^n$ for $1\leq i\leq n$ (that is, the sequence of
Lagrange interpolation polynomials).

Is there such a sequence of $a_i^n$ such that for every continuous $f:[-1,1]\to \mathbb{R}$ there
exists some $x\in [-1,1]$ where\[\limsup_{n\to \infty} \sum_{1\leq i\leq n}|p_{i}^n(x)|=\infty\]and
yet\[\mathcal{L}^nf(x) \to f(x)?\]
-/

@[category research open, question, AMS 41]
theorem erdos_671.parts.i :
    ∃ a : ℕ → ℕ → ℝ, (∀ k,∀ i : Fin k, a k i ∈ Set.Icc (-1 : ℝ) 1 ∧ Set.InjOn (a k) (Finset.range k)) ∧
    (∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc (-1 : ℝ) 1) → ∃ x ∈ Set.Icc (-1 : ℝ) 1,
    (∀ M : ℕ, ∃ᶠ n : ℕ in Filter.atTop, lebesgueFunction n (a n) x ≥ M) ∧
    (∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n : ℕ, (n ≥ N → |lagrangeInterpolation n (a n) f x - f x| < ε))) := by
  sorry

/-- Is there such a sequence such that\[\limsup_{n\to \infty} \sum_{1\leq i\leq n}|p_{i}^n(x)|=\infty\]
for every $x\in [-1,1]$ and yet for every continuous $f:[-1,1]\to \mathbb{R}$ there exists $x\in [-1,1]$
with\[\mathcal{L}^nf(x) \to f(x)?\] -/

@[category research open, question, AMS 41]
theorem erdos_671.parts.ii :
    ∃ a : ℕ → ℕ → ℝ, (∀ k,∀ i : Fin k, a k i ∈ Set.Icc (-1 : ℝ) 1 ∧ Set.InjOn (a k) (Finset.range k)) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, (∀ M : ℕ, ∃ᶠ n : ℕ in Filter.atTop, lebesgueFunction n (a n) x ≥ M)) ∧
    (∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc (-1 : ℝ) 1) → ∃ x₀ ∈ Set.Icc (-1 : ℝ) 1, (∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n : ℕ,
    (n ≥ N → |lagrangeInterpolation n (a n) f x₀ - f x₀| < ε))) := by
  sorry

end Erdos671
