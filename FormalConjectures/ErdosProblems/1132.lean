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

import FormalConjecturesUtil

/-!
# Erdős Problem 1132

*References:*
- [erdosproblems.com/1132](https://www.erdosproblems.com/1132)
- [Er67] Erdős, P., Problems and results on the convergence and divergence properties of the
  Lagrange interpolation polynomials and some extremal problems. Mathematica (Cluj) (1967), 65-73.
- [Er61c] Erdős, P., Problems and results on the theory of interpolation. II.
  Acta Math. Acad. Sci. Hungar. (1961), 235-244.
- [Be31] S. Bernstein, Sur la limitation des valeurs d'un polynome $P_n(x)$ de degré $n$
  sur tout un segment par ses valeurs en $(n+1)$ points du segment.
  Izv. Akad. Nauk. SSSR (1931), 1025-1050.
- [Ta26b] T. Tao, Local Bernstein theory, and lower bounds for Lebesgue constants.
  [arXiv:2603.21453](https://arxiv.org/abs/2603.21453) (2026).
-/

open Filter Set MeasureTheory

namespace Erdos1132

/--
The $k$-th Lagrange basis polynomial for the nodes $x_0,\ldots,x_{n-1}$:
$$l_k(x)=\frac{\prod_{i\neq k}(x-x_i)}{\prod_{i\neq k}(x_k-x_i)}.$$
This is Mathlib's `Lagrange.basis` on `Finset.univ`. When the nodes are pairwise distinct one has
$l_k(x_k)=1$ and $l_k(x_i)=0$ for $i\neq k$.
-/
noncomputable def lagrangeBasis {n : ℕ} (xs : Fin n → ℝ) (k : Fin n) : Polynomial ℝ :=
  Lagrange.basis Finset.univ xs k

/--
The Lebesgue function of Lagrange interpolation at the nodes $x_0,\ldots,x_{n-1}$:
$$L_n(x)=\sum_{k}\lvert l_k(x)\rvert.$$
-/
noncomputable def lebesgueFunction {n : ℕ} (xs : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ k : Fin n, |(lagrangeBasis xs k).eval x|

/-- The Lebesgue function $L_n$ formed from the first $n$ terms of a sequence of nodes. -/
noncomputable def lebesgueFunctionSeq (xs : ℕ → Icc (-1 : ℝ) 1) (n : ℕ) (x : ℝ) : ℝ :=
  lebesgueFunction (fun k : Fin n ↦ (xs k : ℝ)) x

/--
For $x_1,\ldots,x_n\in [-1,1]$ let
$$l_k(x)=\frac{\prod_{i\neq k}(x-x_i)}{\prod_{i\neq k}(x_k-x_i)},$$
which are such that $l_k(x_k)=1$ and $l_k(x_i)=0$ for $i\neq k$.

Let $x_1,x_2,\ldots\in [-1,1]$ be an infinite sequence, and let
$$L_n(x) = \sum_{1\leq k\leq n}\lvert l_k(x)\rvert,$$
where each $l_k(x)$ is defined above with respect to $x_1,\ldots,x_n$.

Must there exist $x\in (-1,1)$ such that
$$L_n(x) >\frac{2}{\pi}\log n-O(1)$$
for infinitely many $n$?

The Lagrange basis is formed from distinct nodes, so the sequence is taken injective.
Tao [Ta26b] notes that it is unclear whether the $O(1)$ constant may depend on $x$; the
formalisation allows a constant depending on the sequence and on $x$.
-/
@[category research open, AMS 26 41]
theorem erdos_1132.parts.i :
    answer(sorry) ↔
    ∀ (xs : ℕ → Icc (-1 : ℝ) 1), Function.Injective xs →
      ∃ x ∈ Ioo (-1 : ℝ) 1, ∃ C : ℝ, ∃ᶠ n : ℕ in atTop,
        (2 / Real.pi) * Real.log n - C < lebesgueFunctionSeq xs n x := by
  sorry

/--
Is it true that
$$\limsup_{n\to \infty}\frac{L_n(x)}{\log n}\geq \frac{2}{\pi}$$
for almost all $x\in (-1,1)$?
-/
@[category research open, AMS 26 41]
theorem erdos_1132.parts.ii :
    answer(sorry) ↔
    ∀ (xs : ℕ → Icc (-1 : ℝ) 1), Function.Injective xs →
      ∀ᵐ x ∂volume.restrict (Ioo (-1 : ℝ) 1),
        (2 / Real.pi : EReal) ≤ atTop.limsup fun n : ℕ ↦
          (lebesgueFunctionSeq xs n x / Real.log n : EReal) := by
  sorry

/--
Erdős [Er61c] proved that, for any fixed $x_1,\ldots,x_n\in [-1,1]$,
$$\max_{x\in [-1,1]}\sum_{1\leq k\leq n}\lvert l_k(x)\rvert>\frac{2}{\pi}\log n-O(1).$$
The nodes are taken pairwise distinct so that the Lagrange basis is defined.
-/
@[category research solved, AMS 26 41]
theorem erdos_1132.variants.max_bound :
    ∃ C : ℝ, ∀ (n : ℕ) (xs : Fin n → Icc (-1 : ℝ) 1), Function.Injective xs →
      ∃ x ∈ Icc (-1 : ℝ) 1,
        (2 / Real.pi) * Real.log n - C < lebesgueFunction (fun k ↦ (xs k : ℝ)) x := by
  sorry

/--
A result of Bernstein [Be31] implies that the set of $x\in(-1,1)$ for which
$$\limsup_{n\to \infty}\frac{L_n(x)}{\log n}\geq \frac{2}{\pi}$$
is everywhere dense.
-/
@[category research solved, AMS 26 41]
theorem erdos_1132.variants.bernstein (xs : ℕ → Icc (-1 : ℝ) 1) (hxs : Function.Injective xs) :
    Dense { x : Ioo (-1 : ℝ) 1 |
      (2 / Real.pi : EReal) ≤ atTop.limsup fun n : ℕ ↦
        (lebesgueFunctionSeq xs n x / Real.log n : EReal) } := by
  sorry

/--
Tao [Ta26b] proved that for any function $\omega(n)$ which tends to infinity with $n$ there
exists a dense set of $x\in (-1,1)$ such that
$$L_n(x)\geq \frac{2}{\pi}\log n-\omega(n)$$
for infinitely many $n$.
-/
@[category research solved, AMS 26 41]
theorem erdos_1132.variants.tao (xs : ℕ → Icc (-1 : ℝ) 1) (hxs : Function.Injective xs)
    (ω : ℕ → ℝ) (hω : Tendsto ω atTop atTop) :
    Dense { x : Ioo (-1 : ℝ) 1 | ∃ᶠ n : ℕ in atTop,
      (2 / Real.pi) * Real.log n - ω n ≤ lebesgueFunctionSeq xs n x } := by
  sorry

end Erdos1132
