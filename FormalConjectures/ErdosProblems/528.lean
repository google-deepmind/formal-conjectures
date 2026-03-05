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
# Erdős Problem 528

*Reference:* [erdosproblems.com/528](https://www.erdosproblems.com/528)

Let $f(n,k)$ count the number of self-avoiding walks of $n$ steps beginning at the origin
in the integer lattice $\mathbb{Z}^k$. The connective constant $C_k$ is defined as
$C_k = \lim_{n \to \infty} f(n,k)^{1/n}$. The problem asks to determine $C_k$ exactly.

[HM54] Hammersley, J. M. and Morton, K. W., *Poor man's Monte Carlo*. J. Roy. Statist.
Soc. Ser. B (1954), 23–38.

[Ke63] Kesten, H., *On the number of self-avoiding walks*. J. Math. Phys. (1963), 960–969.
-/

open Classical Finset BigOperators Filter

namespace Erdos528

/-- Two points in $\mathbb{Z}^k$ are adjacent in the integer lattice if their $\ell^1$ distance
is $1$ (i.e., they differ by $\pm 1$ in exactly one coordinate). -/
def LatticeAdj {k : ℕ} (x y : Fin k → ℤ) : Prop :=
  (∑ i : Fin k, |x i - y i|) = 1

/-- The number of self-avoiding walks of $n$ steps in $\mathbb{Z}^k$ starting at the origin.
A self-avoiding walk is a path in the integer lattice $\mathbb{Z}^k$ that starts at the
origin, takes $n$ steps along lattice edges, and never revisits a vertex. -/
noncomputable def selfAvoidingWalkCount (n k : ℕ) : ℕ :=
  Set.ncard {w : Fin (n + 1) → (Fin k → ℤ) |
    w 0 = 0 ∧
    (∀ i : Fin n, LatticeAdj (w ⟨i.val, by omega⟩) (w ⟨i.val + 1, by omega⟩)) ∧
    Function.Injective w}

/-- The connective constant $C_k$ for self-avoiding walks on $\mathbb{Z}^k$, defined as
$C_k = \lim_{n \to \infty} f(n,k)^{1/n}$ where $f(n,k)$ is the number of self-avoiding
walks of $n$ steps. Returns the limit value if it exists, or $0$ otherwise. -/
noncomputable def connectiveConstant (k : ℕ) : ℝ :=
  if h : ∃ C : ℝ, Filter.Tendsto
    (fun n : ℕ => ((selfAvoidingWalkCount n k : ℝ)) ^ ((1 : ℝ) / (n : ℝ)))
    atTop (nhds C)
  then h.choose
  else 0

/--
Erdős Problem 528 asks to determine the connective constant $C_k$ exactly, where $C_k$ is
the limit of $f(n,k)^{1/n}$ as $n \to \infty$ and $f(n,k)$ counts the number of
self-avoiding walks of $n$ steps in $\mathbb{Z}^k$.

Hammersley and Morton [HM54] showed this limit exists. Kesten [Ke63] proved
$C_k = 2k - 1 - 1/(2k) + O(1/k^2)$.
-/
@[category research open, AMS 5 82]
theorem erdos_528 :
    ∀ k : ℕ, 0 < k →
    connectiveConstant k = answer(sorry) := by
  sorry

/-- Variant: The connective constant $C_k$ exists and satisfies the known bounds
$k \le C_k \le 2k - 1$ [HM54] [Ke63]. -/
@[category research solved, AMS 5 82]
theorem erdos_528.variants.existence_with_bounds :
    ∀ k : ℕ, 0 < k →
    ∃ C : ℝ,
      (k : ℝ) ≤ C ∧ C ≤ 2 * (k : ℝ) - 1 ∧
      Filter.Tendsto
        (fun n : ℕ => ((selfAvoidingWalkCount n k : ℝ)) ^ ((1 : ℝ) / (n : ℝ)))
        atTop (nhds C) := by
  sorry

end Erdos528
