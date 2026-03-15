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

*Related problems:* [Problem 529](https://www.erdosproblems.com/529)

Let $f(n,k)$ count the number of self-avoiding walks of $n$ steps beginning at the origin
in the integer lattice $\mathbb{Z}^k$. The connective constant $C_k$ is defined as
$C_k = \lim_{n \to \infty} f(n,k)^{1/n}$. The problem asks to determine $C_k$ exactly.

OEIS: [A387897](https://oeis.org/A387897), [A156816](https://oeis.org/A156816)

[Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. 6 (1961),
221–254.

[HM54] Hammersley, J. M. and Morton, K. W., _Poor man's Monte Carlo_. J. Roy. Statist.
Soc. Ser. B (1954), 23–38; discussion 61–75.

[Ke63] Kesten, H., _On the number of self-avoiding walks_. J. Math. Phys. (1963), 960–969.

[CG93] Conway, A. R. and Guttmann, A. J., _Lower bound on the connective constant for
square lattice self-avoiding walks_. J. Phys. A (1993), 3719–3724.

[Al93] Alm, S. E., _Upper bounds for the connective constant of self-avoiding walks_.
Combin. Probab. Comput. (1993), 115–136.

[CLS07] Clisby, N., Liang, R., and Slade, G., _Self-avoiding walk enumeration via the lace
expansion_. J. Phys. A (2007), 10973–11017.

[JSG16] Jacobsen, J. L., Scullard, C. R., and Guttmann, A. J., _On the growth constant for
square-lattice self-avoiding walks_. J. Phys. A (2016), 494004, 18.
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
  -- The limit, if it exists, is unique (ℝ is Hausdorff), so `h.choose` is well-defined.
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
$k \le C_k \le 2k - 1$. The upper bound $C_k \le 2k - 1$ is due to [HM54] (at each step
there are at most $2k - 1$ non-backtracking choices); the lower bound $C_k \ge k$ follows
from [Ke63]. -/
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
