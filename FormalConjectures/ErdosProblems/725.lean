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
# Erdős Problem 725

*Reference:* [erdosproblems.com/725](https://www.erdosproblems.com/725)

Erdős and Kaplansky [ErKa46] proved the count $L(k,n)$ of $k \times n$ Latin rectangles satisfies
$$
L(k,n) \sim e^{-\binom{k}{2}} \cdot (n!)^k
$$
when $k = o((\log n)^{3/2-\varepsilon})$. Yamamoto [Ya51] extended this to
$k \leq n^{1/3-o(1)}$.

[ErKa46] Erdős, P. and Kaplansky, I., _The asymptotic number of Latin rectangles_ (1946).

[Ya51] Yamamoto, K., _On the asymptotic number of Latin rectangles_ (1951).

[Er81] Erdős, P. (1981).
-/

open Filter

namespace Erdos725

/-- A $k \times n$ Latin rectangle: a function $f : \text{Fin}\, k \to \text{Fin}\, n \to \text{Fin}\, n$
where each row is a bijection (permutation of $\text{Fin}\, n$) and each column has distinct
entries. -/
def IsLatinRectangle {k n : ℕ} (f : Fin k → Fin n → Fin n) : Prop :=
  (∀ i : Fin k, Function.Bijective (f i)) ∧
  (∀ j : Fin n, Function.Injective (fun i : Fin k => f i j))

/-- The number of $k \times n$ Latin rectangles. -/
noncomputable def latinRectangleCount (k n : ℕ) : ℕ :=
  Set.ncard {f : Fin k → Fin n → Fin n | IsLatinRectangle f}

/--
Erdős Problem 725 [Er81]:

For any sequence $k(n)$ with $k(n) = o(\sqrt{n})$ and $k(n) \geq 2$ eventually,
the number $L(k(n), n)$ of $k(n) \times n$ Latin rectangles satisfies
$$
\frac{L(k(n), n)}{e^{-\binom{k(n)}{2}} \cdot (n!)^{k(n)}} \to 1 \quad \text{as } n \to \infty.
$$
-/
@[category research open, AMS 5]
theorem erdos_725 :
    ∀ (k : ℕ → ℕ),
    (∀ᶠ n in atTop, 2 ≤ k n) →
    (∀ n, k n ≤ n) →
    Tendsto (fun n => (k n : ℝ) / Real.sqrt ↑n) atTop (nhds 0) →
    Tendsto
      (fun n => (latinRectangleCount (k n) n : ℝ) /
        (Real.exp (-(↑(Nat.choose (k n) 2) : ℝ)) * ((Nat.factorial n : ℝ) ^ (k n))))
      atTop (nhds 1) := by
  sorry

end Erdos725
