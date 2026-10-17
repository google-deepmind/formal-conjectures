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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 190

*References:*
- [erdosproblems.com/190](https://www.erdosproblems.com/190)
- [ErGr79] P. Erdős and R. L. Graham, *Old and new problems and results in combinatorial
  number theory: van der Waerden's theorem and related topics*, Enseign. Math. (2) 25 (1979),
  325–344 (p. 333).
- [ErGr80] P. Erdős and R. L. Graham, *Old and New Problems and Results in Combinatorial
  Number Theory*, Monogr. Enseign. Math. 28 (1980), p. 17.
- [Ba26] J. H. Bae, *A resolution of Erdős Problem #190 via Erdős–Lovász, BCT, and
  Baker–Harman–Pintz*, arXiv:2604.20588 (22 April 2026).
- [FoHu26] J. Fox and Z. Hunter, *Three-color van der Waerden numbers grow
  super-exponentially*, arXiv:2606.02541 (1 June 2026).
-/

@[expose] public section

open Filter

namespace Erdos190

/-- `N` is *canonical* for `k` if every colouring of $\{1, \ldots, N\}$ contains a `k`-term
arithmetic progression which is either monochromatic or rainbow (its terms receive pairwise
distinct colours). Colours are taken in `ℕ`; since only the finitely many values on
$\{1, \ldots, N\}$ matter, this covers colourings into any number of colours. -/
def IsCanonical (N k : ℕ) : Prop :=
  ∀ c : ℕ → ℕ, ∃ S ⊆ Set.Icc 1 N, S.IsAPOfLength k ∧ ((∃ γ, ∀ n ∈ S, c n = γ) ∨ S.InjOn c)

/-- The canonical van der Waerden number $H(k)$: the least `N` which is canonical for `k`
(`0` if there is none). -/
noncomputable def H (k : ℕ) : ℕ := sInf {N | IsCanonical N k}

/-- Any two distinct points form a $2$-term progression which is monochromatic or rainbow, so
$\{1, 2\}$ is canonical for $k = 2$. -/
@[category test, AMS 5 11]
theorem isCanonical_two_two : IsCanonical 2 2 := by
  intro c
  refine ⟨{1, 2}, ?_, by exact_mod_cast Nat.isAPOfLength_pair (by norm_num : 1 < 2), ?_⟩
  · rintro x (rfl | rfl) <;> simp
  · by_cases h : c 1 = c 2
    · exact Or.inl ⟨c 1, by rintro n (rfl | rfl) <;> simp [h]⟩
    · refine Or.inr ?_
      rintro x (rfl | rfl) y (rfl | rfl) hxy <;> simp_all

/-- $\{1\}$ contains no $2$-term arithmetic progression, so it is not canonical for $k = 2$. -/
@[category test, AMS 5 11]
theorem not_isCanonical_one_two : ¬ IsCanonical 1 2 := by
  intro h
  obtain ⟨S, hS, ⟨a, d, hcard, -⟩, -⟩ := h id
  have h1 : S.encard ≤ 1 := by
    calc S.encard ≤ (Set.Icc 1 1 : Set ℕ).encard := Set.encard_le_encard hS
      _ = 1 := by simp
  have h2 : S.encard = 2 := by exact_mod_cast hcard
  rw [h2] at h1
  exact absurd h1 (by decide)

/-- $H(2) = 2$. -/
@[category test, AMS 5 11]
theorem H_two : H 2 = 2 := by
  apply le_antisymm (Nat.sInf_le isCanonical_two_two)
  refine le_csInf ⟨2, isCanonical_two_two⟩ fun N hN => ?_
  by_contra hlt
  interval_cases N
  · obtain ⟨S, hS, ⟨a, d, hcard, -⟩, -⟩ := hN id
    have : S = ∅ := by
      ext x; simp only [Set.mem_empty_iff_false, iff_false]; intro hx; simpa using hS hx
    subst this
    simp at hcard
  · exact not_isCanonical_one_two hN

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
canonical $N$ exceeds $(Ck)^k$ for all large $k$. Given the existence of $H(k)$ this is
equivalent to $H(k)^{1/k}/k\to\infty$ (see `erdos_190.variants.H`).

The formal proof (Lean 4 / Mathlib v4.33.0, following Section 4.3 of [Ba26]) is registered in
the Palomar registry as PALOMAR-2026-09-15-000003.  A bridge deriving this exact statement
(with the definitions above) from the registered proof is available at
[jbaelaw/erdos190-fc-bridge](https://github.com/jbaelaw/erdos190-fc-bridge).
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/jbaelaw/erdos190-lean/blob/be43a3ead08a9d9af352cf296d284dd3468ca805/Erdos190/Eventually.lean"]
theorem erdos_190 :
    answer(True) ↔ ∀ C : ℕ, ∀ᶠ k in atTop, ∀ N, IsCanonical N k → (C * k) ^ k < N := by
  sorry

/-- The same statement in terms of $H(k)$, assuming that a canonical `N` exists for every `k`
(the Erdős–Graham theorem, via Szemerédi's theorem). -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/jbaelaw/erdos190-lean/blob/be43a3ead08a9d9af352cf296d284dd3468ca805/Erdos190/Eventually.lean"]
theorem erdos_190.variants.H :
    answer(True) ↔ (∀ k, {N | IsCanonical N k}.Nonempty) →
      ∀ C : ℕ, ∀ᶠ k in atTop, (C * k) ^ k < H k := by
  sorry

end Erdos190
