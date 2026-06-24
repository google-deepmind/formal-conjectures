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
import FormalConjecturesForMathlib.Combinatorics.Additive.Coset


/-!
# Green's Open Problem 51

*References:*
- [Gr24] [Green's Open Problems](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.51)
- [Gr13] B. J. Green, Restriction and Kakeya phenomena, notes from a 2003 course.
  Available at http://people.maths.ox.ac.uk/greenbj/papers/rkp.pdf
- [Sa11] Sanders, Tom. "Green's sumset problem at density one half."
  Acta Arithmetica 146.1 (2011): 91-101.
- [Gr02] Green, Ben. "Arithmetic progressions in sumsets."
  Geometric & Functional Analysis GAFA 12.3 (2002): 584-597.
- [Ruz91] Ruzsa, Imre Z. "Arithmetic progressions in sumsets."
  Acta Arithmetica 60.2 (1991): 191-202.
-/

open Filter Real
open scoped Pointwise

namespace Green51

/-- The largest dimension of a coset guaranteed to be contained in $2A$ for $A \subseteq \mathbb{F}_2^n$ with density $\alpha$. -/
noncomputable def guaranteedMaxCosetDim (n : ℕ) (α : ℝ) : ℕ :=
  sInf { maxCosetDim (ZMod 2) (𝔽₂ n) ↑(A + A) | (A : Finset (𝔽₂ n)) (_h : A.dens ≥ α) }

/--
Suppose that $A \subset \mathbb{F}_2^n$ is a set of density $\alpha$. What is the largest size of coset
guaranteed to be contained in $2A$?

We phrase this by asking for the exact function $F(\alpha, n)$ giving the maximum dimension
of a guaranteed coset.
-/
@[category research open, AMS 5 11]
theorem green_51 : answer(sorry) = guaranteedMaxCosetDim := by
  sorry

/-- It is known that $A + A$ must contain a coset of dimension $\gg_\alpha n$ [Gr13]. -/
@[category research solved, AMS 5 11]
theorem green_51.lower :
    ∀ (α : ℝ), 0 < α → α ≤ 1 →
    ∃ c > 0, ∀ᶠ (n : ℕ) in atTop, c * (n : ℝ) ≤ guaranteedMaxCosetDim n α := by
  sorry

/-- It is known that $A + A$ need not contain a coset of dimension $n - \sqrt{n}$ [Gr13]. -/
@[category research solved, AMS 5 11]
theorem green_51.upper :
    ∃ α > 0, α ≤ 1 ∧ ∀ᶠ (n : ℕ) in atTop, (guaranteedMaxCosetDim n α : ℝ) < (n : ℝ) - sqrt n := by
  sorry

/--
Suppose that $A \subset \mathbb{F}_2^n$ has density $\alpha > 1/2 - C/\sqrt{n}$.
Does $A + A$ contain a subspace of co-dimension $O_C(1)$? [Sa11, Question 5.1]
-/
@[category research open, AMS 5 11]
theorem green_51.one_half :
    answer(sorry) ↔ ∀ (k : ℝ), 0 < k →
      ∃ (c : ℕ), ∀ᶠ (n : ℕ) in atTop,
        ∀ (α : ℝ), α > (1/2 : ℝ) - k / sqrt (n : ℝ) → α ≤ 1 →
          n ≤ guaranteedMaxCosetDim n α + c := by
  sorry

/--
The largest length of an arithmetic progression guaranteed to be contained in $A+A$
for $A \subseteq \{1, \dots, N\}$ with density $\alpha$.
-/
noncomputable def guaranteedMaxAPLength (N : ℕ) (α : ℝ) : ℕ :=
  sInf { sSup {l : ℕ | ∃ s ⊆ (A + A : Set ℕ), s.IsAPOfLength (l : ℕ∞)}
       | (A : Finset ℕ) (_hA : A ⊆ Finset.Icc 1 N) (_h : α * (N : ℝ) ≤ A.card) }

/-- It is known that $A + A$ must contain an arithmetic progression of length $\sim \exp(c (\log N)^{1/2})$ [Gr02]. -/
@[category research solved, AMS 5 11]
theorem green_51.lower_ap :
    ∀ (α : ℝ), 0 < α → α ≤ 1 →
      ∃ c > 0, ∀ᶠ (N : ℕ) in atTop,
        exp (c * log (N : ℝ) ^ (1/2 : ℝ)) ≤ guaranteedMaxAPLength N α := by
  sorry

/-- It is known that $A + A$ need not contain an arithmetic progression of length $\sim \exp(c (\log N)^{2/3})$ [Ruz91]. -/
@[category research solved, AMS 5 11]
theorem green_51.upper_ap :
    ∀ (α : ℝ), 0 < α → α < 1/2 →
      ∃ c > 0, ∀ᶠ (N : ℕ) in atTop,
        guaranteedMaxAPLength N α ≤ exp (c * log (N : ℝ) ^ (2/3 : ℝ)) := by
  sorry

end Green51
