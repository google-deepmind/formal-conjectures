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
# Erdős Problem 154

*References:*
- [erdosproblems.com/154](https://www.erdosproblems.com/154)
- [Li98] Lindström, Bernt, *Well distribution of Sidon sets in residue classes*.
  J. Number Theory (1998), 197-200.
- [Ko99] Kolountzakis, Mihail N., *On the uniform distribution in residue classes of dense sets
  of integers with distinct sums*. J. Number Theory (1999), 147-153.
- [ESS94] Erdős, P. and Sárközy, A. and Sós, T., *On Sum Sets of Sidon Sets, I*.
  Journal of Number Theory (1994), 329-347.
-/

open Filter Finset

namespace Erdos154

/--
Let $A\subset \{1,\ldots,N\}$ be a Sidon set with $\lvert A\rvert\sim N^{1/2}$. Must $A+A$ be
well-distributed over all small moduli? In particular, must about half the elements of $A+A$ be
even and half odd?

Lindström [Li98] has shown this is true for $A$ itself, subsequently strengthened by
Kolountzakis [Ko99]. It follows immediately using the Sidon property that $A+A$ is similarly
well-distributed.

We formalise Lindström's result for $A$ itself: for any sequence of Sidon sets
$A_k\subseteq\{0,\ldots,N_k\}$ with $N_k\to\infty$ and $\lvert A_k\rvert\sim N_k^{1/2}$, and any
modulus $m\geq 2$, the number of elements of $A_k$ congruent to $i\pmod m$, divided by
$N_k^{1/2}$, tends to $1/m$ for every residue $i<m$.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/Woett/Lean-files/blob/main/ErdosProblem154.lean"]
theorem erdos_154 : answer(True) ↔
    ∀ (m : ℕ) (hm : 2 ≤ m) (N : ℕ → ℕ) (A : ℕ → Finset ℕ),
      Tendsto (fun k => (N k : ℝ)) atTop atTop →
      (∀ k, ∀ x ∈ A k, x ≤ N k) →
      (∀ k, IsSidon (A k : Set ℕ)) →
      Tendsto (fun k => ((A k).card : ℝ) / Real.sqrt (N k)) atTop (nhds 1) →
      ∀ i < m, Tendsto (fun k => (((A k).filter (fun a => a % m = i)).card : ℝ) / Real.sqrt (N k))
        atTop (nhds (1 / m)) := by
  sorry

end Erdos154
