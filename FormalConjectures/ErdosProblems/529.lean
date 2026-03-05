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
# Erdős Problem 529

Let $d_k(n)$ denote the expected Euclidean distance from the origin of the endpoint of a
uniformly random $n$-step self-avoiding walk on $\mathbb{Z}^k$. The problem asks whether
$d_2(n)/\sqrt{n} \to \infty$ (Part 1) and whether $d_k(n) \ll \sqrt{n}$ for $k \geq 3$ (Part 2).

*Reference:* [erdosproblems.com/529](https://www.erdosproblems.com/529)

[DuHa13] Duminil-Copin, H. and Hammond, A., *Self-avoiding walk is sub-ballistic*,
J. Eur. Math. Soc. (2013).
-/

open BigOperators Filter Classical

namespace Erdos529

/-- Two points in $\mathbb{Z}^k$ are adjacent in the integer lattice if their $\ell^1$ distance
is $1$ (i.e., they differ by $\pm 1$ in exactly one coordinate). -/
def LatticeAdj {k : ℕ} (x y : Fin k → ℤ) : Prop :=
  (∑ i : Fin k, |x i - y i|) = 1

/-- The set of self-avoiding walks of $n$ steps in $\mathbb{Z}^k$ starting at the origin. -/
def selfAvoidingWalks (n k : ℕ) : Set (Fin (n + 1) → (Fin k → ℤ)) :=
  {w | w 0 = 0 ∧
    (∀ i : Fin n, LatticeAdj (w ⟨i.val, by omega⟩) (w ⟨i.val + 1, by omega⟩)) ∧
    Function.Injective w}

/-- The Euclidean distance of a point in $\mathbb{Z}^k$ from the origin. -/
noncomputable def euclidDistFromOrigin {k : ℕ} (x : Fin k → ℤ) : ℝ :=
  Real.sqrt (∑ i : Fin k, ((x i : ℝ)) ^ 2)

/-- The expected Euclidean distance from the origin of the endpoint of a uniformly
random self-avoiding walk of $n$ steps in $\mathbb{Z}^k$.
$$d_k(n) = \frac{1}{|\mathrm{SAW}(n,k)|} \cdot \sum_{w \in \mathrm{SAW}(n,k)} \|w(n)\|_2$$ -/
noncomputable def expectedSAWDist (n k : ℕ) : ℝ :=
  if h : (selfAvoidingWalks n k).Finite then
    (h.toFinset.sum (fun w => euclidDistFromOrigin (w ⟨n, by omega⟩))) /
    (h.toFinset.card : ℝ)
  else 0

/--
Erdős Problem 529, Part 1:

Let $d_k(n)$ be the expected distance from the origin after taking $n$ steps of a
uniformly random self-avoiding walk in $\mathbb{Z}^k$. Is it true that
$$\lim_{n \to \infty} \frac{d_2(n)}{n^{1/2}} = \infty?$$

That is, in two dimensions, does the expected endpoint distance grow strictly
faster than $\sqrt{n}$?

Duminil-Copin and Hammond [DuHa13] proved $d_2(n) = o(n)$. It is conjectured
that $d_2(n) \sim D \cdot n^{3/4}$.
-/
@[category research open, AMS 5 60]
theorem erdos_529 : answer(sorry) ↔
    Tendsto (fun n : ℕ => expectedSAWDist n 2 / (n : ℝ) ^ ((1 : ℝ) / 2))
      atTop atTop := by
  sorry

/--
Erdős Problem 529, Part 2:

Is it true that $d_k(n) \ll n^{1/2}$ for $k \geq 3$?

Hara and Slade proved $d_k(n) \sim D \cdot n^{1/2}$ for all $k \geq 5$. It is now believed
that this is false for $k = 3$ and $k = 4$: the conjectured behavior is
$d_3(n) \sim n^{\nu}$ where $\nu \approx 0.59$ and
$d_4(n) \sim D \cdot (\log n)^{1/8} \cdot n^{1/2}$.
-/
@[category research open, AMS 5 60]
theorem erdos_529.variants.part2 : answer(sorry) ↔
    ∀ k : ℕ, k ≥ 3 →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      expectedSAWDist n k ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  sorry

end Erdos529
