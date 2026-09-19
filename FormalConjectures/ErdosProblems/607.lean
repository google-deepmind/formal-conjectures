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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 607

*References:*
- [erdosproblems.com/607](https://www.erdosproblems.com/607)
- [Er85] Erdős, P., _Problems and results in combinatorial geometry_. Discrete geometry and
  convexity (New York, 1982) (1985), 1-11.
- [SzTr83] Szemerédi, Endre and Trotter, Jr., William T., _Extremal problems in discrete
  geometry_. Combinatorica (1983), 381-392.
-/

@[expose] public section

open Filter Real EuclideanGeometry

namespace Erdos607

/-- The lines determined by a finite set of points `P` in the plane. -/
def determinedLines (P : Finset ℝ²) : Set (AffineSubspace ℝ ℝ²) :=
  {affineSpan ℝ {p, q} | (p ∈ P) (q ∈ P) (_ : p ≠ q)}

open scoped Classical in
/-- $A(P)=\{\lvert \ell_1\cap P\rvert,\ldots,\lvert \ell_m\cap P\rvert\}$, where
$\ell_1,\ldots,\ell_m$ are the lines determined by `P`. -/
noncomputable def spectrum (P : Finset ℝ²) : Set ℕ :=
  (fun ℓ ↦ (P.filter (· ∈ ℓ)).card) '' determinedLines P

/-- `F n` counts the number of possible sets $A(P)$ over all sets `P` of `n` points. -/
noncomputable def F (n : ℕ) : ℕ :=
  {A | ∃ P : Finset ℝ², P.card = n ∧ spectrum P = A}.ncard

/--
For a set of $n$ points $P\subset \mathbb{R}^2$ let $\ell_1,\ldots,\ell_m$ be the lines
determined by $P$, and let $A=\{\lvert \ell_1\cap P\rvert,\ldots,\lvert \ell_m\cap P\rvert\}$.

Let $F(n)$ count the number of possible sets $A$ that can be constructed this way. Is it true
that
$$F(n) \leq \exp(O(\sqrt{n}))?$$

The answer is yes, proved by Szemerédi and Trotter [SzTr83]. Erdős writes it is 'easy to see'
that this bound would be best possible.
-/
@[category research solved, AMS 5 52, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos607.lean#L826"]
theorem erdos_607 : answer(True) ↔
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, (F n : ℝ) ≤ exp (C * √n) := by
  sorry

/-- Erdős writes it is 'easy to see' that the bound $F(n) \leq \exp(O(\sqrt{n}))$ would be best
possible: $F(n)\geq \exp(c\sqrt{n})$ for some $c>0$. -/
@[category research solved, AMS 5 52]
theorem erdos_607.variants.lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, exp (c * √n) ≤ F n := by
  sorry

end Erdos607
