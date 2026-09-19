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
# Erdős Problem 190

*References:*
- [erdosproblems.com/190](https://www.erdosproblems.com/190)
- [ErGr79] P. Erdős and R. L. Graham, *Old and new problems and results in combinatorial
  number theory: van der Waerden's theorem and related topics*, Enseign. Math. (2) 25 (1979),
  325–344 (p. 333).
- [ErGr80] P. Erdős and R. L. Graham, *Old and New Problems and Results in Combinatorial
  Number Theory*, Monogr. Enseign. Math. 28 (1980), p. 17.
- [Ba26] J. H. Bae, *A resolution of Erdős Problem #190: the canonical van der Waerden number
  satisfies $H(k)^{1/k}/k\to\infty$*, arXiv:2604.20588 (2026).
- [FoHu26] J. Fox and Z. Hunter, *Three-color van der Waerden numbers grow
  super-exponentially*, arXiv:2606.02541 (2026).
-/

open Filter

namespace Erdos190

/-- A `k`-term arithmetic progression in `[N] = Fin N`: start `a`, common difference `d ≥ 1`,
last term `a + (k-1) d < N`. -/
structure AP (N k : ℕ) where
  a : ℕ
  d : ℕ
  d_pos : 0 < d
  last_lt : a + (k - 1) * d < N

/-- The `i`-th term `a + i d` of the progression, as an element of `Fin N`. -/
def AP.term {N k : ℕ} (P : AP N k) (i : Fin k) : Fin N :=
  ⟨P.a + i.1 * P.d, by
    have hi : i.1 ≤ k - 1 := Nat.le_sub_one_of_lt i.2
    have := P.last_lt
    nlinarith [Nat.mul_le_mul_right P.d hi]⟩

/-- The colouring `c` has a monochromatic `k`-term arithmetic progression. -/
def HasMonoAP {N k : ℕ} {κ : Type*} (c : Fin N → κ) : Prop :=
  ∃ P : AP N k, ∀ i j : Fin k, c (P.term i) = c (P.term j)

/-- The colouring `c` has a rainbow `k`-term arithmetic progression (all terms of distinct
colours). -/
def HasRainbowAP {N k : ℕ} {κ : Type*} (c : Fin N → κ) : Prop :=
  ∃ P : AP N k, ∀ i j : Fin k, c (P.term i) = c (P.term j) → i = j

/-- `[N]` is *canonical* for `k`: every finite colouring of `[N]` (colours in `ℕ`, so any
number of colours) contains a monochromatic or a rainbow `k`-term arithmetic progression.
The canonical van der Waerden number `H(k)` is the least such `N`. -/
def Canonical (N k : ℕ) : Prop :=
  ∀ c : Fin N → ℕ, HasMonoAP (k := k) c ∨ HasRainbowAP (k := k) c

/-- The canonical van der Waerden number `H(k)`, the least canonical `N` (`0` if none exists;
existence follows from Szemerédi's theorem [ErGr79]). -/
noncomputable def H (k : ℕ) : ℕ := sInf {N | Canonical N k}

/--
Let $H(k)$ be the smallest $N$ such that in any finite colouring of $\{1,\ldots,N\}$ (into
any number of colours) there is always either a monochromatic $k$-term arithmetic progression
or a rainbow arithmetic progression (i.e. all elements are different colours). Estimate
$H(k)$. Is it true that $H(k)^{1/k}/k\to\infty$ as $k\to\infty$?

The question was answered affirmatively in [Ba26] (22 April 2026), which gave the first
publicly available proof, with $H(k)\geq k^{(2-o(1))k}$.  The subsequent work [FoHu26]
(1 June 2026) describes [Ba26] as independent work that also resolves the problem, and
obtains $H(k)\geq k^{(1-o(1))k\log k}$.

The statement is formalised without assuming the existence of $H(k)$: for every $C$, every
canonical $N$ exceeds $(Ck)^k$ for all large $k$.  Given the existence of $H(k)$ this is
equivalent to $H(k)^{1/k}/k\to\infty$ (see `erdos_190.variants.H`).

The formal proof (Lean 4 / Mathlib v4.33.0, following Section 4.3 of [Ba26]) is registered in
the Palomar registry as PALOMAR-2026-09-15-000003.
-/
@[category research solved, AMS 5 11,
formal_proof using lean4 at "https://github.com/jbaelaw/erdos190-lean/blob/be43a3ead08a9d9af352cf296d284dd3468ca805/Erdos190/Eventually.lean"]
theorem erdos_190 :
    answer(True) ↔ ∀ C : ℕ, ∀ᶠ k in atTop, ∀ N, Canonical N k → (C * k) ^ k < N := by
  sorry

/-- The same statement in terms of `H(k)`, assuming that a canonical `N` exists for every `k`
(the Erdős–Graham theorem, via Szemerédi's theorem). -/
@[category research solved, AMS 5 11,
formal_proof using lean4 at "https://github.com/jbaelaw/erdos190-lean/blob/be43a3ead08a9d9af352cf296d284dd3468ca805/Erdos190/Eventually.lean"]
theorem erdos_190.variants.H :
    answer(True) ↔ (∀ k, {N | Canonical N k}.Nonempty) →
      ∀ C : ℕ, ∀ᶠ k in atTop, (C * k) ^ k < H k := by
  sorry

end Erdos190
