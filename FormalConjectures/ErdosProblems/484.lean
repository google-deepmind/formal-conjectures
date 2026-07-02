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
# Erdős Problem 484

*References:*
- [erdosproblems.com/484](https://www.erdosproblems.com/484)
- [ESS89] Erdős, P., Sárközy, A., and Sós, V. T., *On a conjecture of Roth and some related
  problems. I*. (1989), 47-59.
-/

namespace Erdos484

open scoped Classical in
/--
Prove that there exists an absolute constant $c>0$ such that, whenever $\{1,\ldots,N\}$ is
$k$-coloured (and $N$ is large enough depending on $k$) then there are at least $cN$ many
integers in $\{1,\ldots,N\}$ which are representable as a monochromatic sum (that is, $a+b$
where $a,b\in \{1,\ldots,N\}$ are in the same colour class and $a\neq b$).

A conjecture of Roth. Solved by Erdős, Sárközy, and Sós [ESS89], who in fact prove that
there are at least $\frac{N}{2}-O(N^{1-1/2^{k+1}})$ many even numbers which are of this form.

The $k$-colouring of $\{1,\ldots,N\}$ is formalised as a function `f : ℕ → Fin k`; only its
values on `Finset.Icc 1 N` are inspected, and the monochromatic sums counted are those landing
back in `Finset.Icc 1 N`.
-/
-- Divergences from the hosted theorems (plby and jayyhk state the identical
-- `monochromatic_sums_linear` / `erdos_484` over an auxiliary `monochromaticSumSet`):
-- * hosted bound is `(monochromaticSumSet N k f).card ≥ ⌊c * (N : ℝ)⌋₊`; here the bound is
--   stated directly over ℝ as `c * N ≤ card`, matching the problem's "at least $cN$".
--   The two forms are equivalent up to rescaling the existentially quantified `c`.
-- * hosted proofs define `monochromaticSumSet` as a classical `Finset.filter`; here the same
--   filter predicate is inlined verbatim (same `Finset.Icc 1 N` window, same
--   `a ≠ b ∧ f a = f b ∧ a + b = n` condition), so no auxiliary definition is needed.
-- * `0 < k` here vs `k ≥ 1` hosted (definitionally equal on ℕ).
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos484.lean"]
theorem erdos_484 :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 0 < k → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ f : ℕ → Fin k,
      c * N ≤ (((Finset.Icc 1 N).filter fun n =>
        ∃ a ∈ Finset.Icc 1 N, ∃ b ∈ Finset.Icc 1 N,
          a ≠ b ∧ f a = f b ∧ a + b = n).card : ℝ) := by
  sorry

end Erdos484
