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

/-
# Ben Green's Open Problem 43

*References:*
- [Gr24] [Ben Green's Open Problem 43](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.43)
- [Gr18] Green, Ben. "A note on multiplicative functions on progressions to large moduli."
  Proc. Roy. Soc. Edinburgh Sect. A 148 (2018), no. 1, 63–77. (Problem 43 is formulated here,
  [Gr18, Section 4].)
- [AP92] Alon, Noga, and Yuval Peres. "Uniform dilations." Geometric and Functional Analysis
  2 (1992), no. 1, 1–28. (Source of the favourite variant in [Gr24, Comments to Problem 43].)
-/


open Filter Topology Classical

namespace Green43

/-- The *sieved subset* of `[1, N]`: those `n ∈ [1, N]` with `n ≡ a p (mod p)` for some prime
`p` in the range `lo ≤ p < hi`. This is the set counted in `green_43`. -/
noncomputable def sievedSet (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) : Finset ℤ :=
  (Finset.Icc (1 : ℤ) (N : ℤ)).filter fun n => ∃ p, Nat.Prime p ∧
  lo ≤ (p : ℝ) ∧ (p : ℝ) < hi ∧ (p : ℤ) ∣ ((n : ℤ) - a p)

/-- The size of the sieved subset `sievedSet N a lo hi`. -/
noncomputable def sievedCard (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) : ℕ :=
  (sievedSet N a lo hi).card

/--
[Gr24, Comments to Problem 43] The statement that the lower bound `N^{1-o(1)}` holds for the
sieved set, where for each `N` the sieving primes range over `[lo N, hi N)`. Problem 43 is the
case `lo N = N^{0.51}`, `hi N = 2 N^{0.51}`; the minor variants only change this range.
-/
def SievedLowerBound (lo hi : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ a : ℕ → ℤ, (N : ℝ) ^ (1 - ε) ≤ sievedCard N a (lo N) (hi N)

/-- The exponent-`α` instance of Problem 43: the `N^{1-o(1)}` lower bound for sieving primes in
`[N^α, 2 N^α)`. Problem 43 is `SievedLowerBoundExp 0.51`. -/
def SievedLowerBoundExp (α : ℝ) : Prop :=
  SievedLowerBound (fun N => (N : ℝ) ^ α) (fun N => 2 * (N : ℝ) ^ α)

/--
Let $N$ be a large integer. For each prime $p$ with $N^{0.51} \leq p < 2N^{0.51}$, pick some
residue $a(p) \in \mathbb{Z}/p\mathbb{Z}$. Is it true that
$$\#\{n \in [N] : n \equiv a(p) \pmod{p} \text{ for some } p\} \gg N^{1-o(1)}?$$
-/
@[category research open, AMS 11]
theorem green_43 : answer(sorry) ↔ SievedLowerBoundExp (0.51 : ℝ) := by
  sorry

/-- The sieved set is a subset of `[1, N]`, so it always has at most `N` elements. -/
@[category test, AMS 11]
theorem green_43.sieved_card_le (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) :
    sievedCard N a lo hi ≤ N := by
  unfold sievedCard sievedSet
  exact le_trans (Finset.card_filter_le _ _) (by simp [Int.card_Icc])

/-- For `N = 0` the sieved set is empty, since `[1, 0]` is empty. -/
@[category test, AMS 11]
theorem green_43.sieved_card_eq_zero (a : ℕ → ℤ) (lo hi : ℝ) :
    sievedCard 0 a lo hi = 0 := by
  unfold sievedCard sievedSet
  simp

/--
If there is a prime `p` in the sieving range `[lo, hi)` with `p ≤ N`, then the sieved set is
nonempty: the residue class of `a p` modulo `p` always meets `[1, N]`. This shows that for large
`N` (where Bertrand's postulate guarantees such a prime) the cardinality in `green_43` is at
least `1`. -/
@[category test, AMS 11]
theorem green_43.sieved_nonempty (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    (sievedSet N a lo hi).Nonempty := by
  have hp0 : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  set m : ℤ := a p % (p : ℤ) with hm
  have hm_nonneg : 0 ≤ m := Int.emod_nonneg _ (by positivity)
  have hm_lt : m < (p : ℤ) := Int.emod_lt_of_pos _ hp0
  have hdvd : (p : ℤ) ∣ (m - a p) := by
    rw [hm, Int.emod_def]; exact ⟨-(a p / (p : ℤ)), by ring⟩
  -- Pick the representative of `a p mod p` inside `[1, N]`.
  refine ⟨if m = 0 then (p : ℤ) else m, ?_⟩
  unfold sievedSet
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, p, hp, hlb, hub, ?_⟩
  · split <;> omega
  · split <;> omega
  · split
    · rename_i h
      have : (p : ℤ) ∣ a p := by simpa [h] using hdvd
      exact dvd_sub (dvd_refl _) this
    · exact hdvd

/- ## Variants

The following formalise the related conjectures from the comments to Problem 43 in [Gr24]. -/

/-- A subset `A ⊆ ℤ/pℤ` has a *gap* of length `L` if there is a run of `L` consecutive residues
none of which lie in `A`. -/
def HasGap {p : ℕ} (A : Finset (ZMod p)) (L : ℕ) : Prop :=
  ∃ x : ZMod p, ∀ i : ℕ, i < L → x + (i : ZMod p) ∉ A

/-- Following Alon–Peres [AP92], a *dilation* of `A` by an integer `n` is the set
`n A = {n x : x ∈ A}` (here in `ℤ/pℤ`, with `n` reduced modulo `p`). -/
def Dilate {p : ℕ} (n : ZMod p) (A : Finset (ZMod p)) : Finset (ZMod p) :=
  A.image (fun x => n * x)

/--
[Gr24, Comments to Problem 43; AP92] One of Green's favourite related conjectures: if
`A ⊆ ℤ/pℤ` is a set of size `⌊p/2⌋`, does some dilation `n A` (`n` an integer) have no gaps of
length more than `p^{0.49}`?
-/
@[category research open, AMS 05 11]
theorem green_43.variants.alon_peres :
    answer(sorry) ↔ ∀ p : ℕ, p.Prime → ∀ A : Finset (ZMod p), A.card = p / 2 →
    ∃ n : ZMod p, ∀ L : ℕ, (p : ℝ) ^ (0.49 : ℝ) < (L : ℝ) → ¬ HasGap (Dilate n A) L := by
  sorry

/--
[Gr24, Comments to Problem 43] A minor variant of Problem 43: the same question but with `p`
ranging over `N^{0.51} ≤ p < N^{0.52}`. Obtaining the lower bound `N^{1-o(1)}` here is no harder
than Problem 43, but is not known.
-/
@[category research open, AMS 05 11]
theorem green_43.variants.range_N051_N052 :
    answer(sorry) ↔
    SievedLowerBound (fun N => (N : ℝ) ^ (0.51 : ℝ)) (fun N => (N : ℝ) ^ (0.52 : ℝ)) := by
  sorry

/--
[Gr24, Comments to Problem 43] For the range `N^{0.51} ≤ p < N^{0.52}` there may even be a
linear lower bound `c N`.
-/
@[category research open, AMS 05 11]
theorem green_43.variants.range_N051_N052_linear :
    answer(sorry) ↔ ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ a : ℕ → ℤ,
      c * N ≤ sievedCard N a ((N : ℝ) ^ (0.51 : ℝ)) ((N : ℝ) ^ (0.52 : ℝ)) := by
  sorry


/--
[Gr24, Comments to Problem 43] One can replace the exponent `0.51` by any other exponent `α`:
does the lower bound `N^{1-o(1)}` hold for sieving primes in `[N^α, 2 N^α)` for every exponent
`0 < α < 1`? Problem 43 is the case `α = 0.51`; the regime `α < 1/2` is the solved special case
`green_43.variants.general_exponent_lt_half`, while progress for `α ≈ 1` would imply Kakeya.
-/
@[category research open, AMS 05 11]
theorem green_43.variants.general_exponent :
    answer(sorry) ↔ ∀ α : ℝ, 0 < α → α < 1 → SievedLowerBoundExp α := by
  sorry

/--
[Gr24, Comments to Problem 43] For exponents `α < 1/2` the lower bound `N^{1-o(1)}` is
straightforward (by an inclusion–exclusion or Cauchy–Schwarz argument). This is the solved
special case of `green_43.variants.general_exponent`.
-/
@[category research solved, AMS 05 11]
theorem green_43.variants.general_exponent_lt_half :
    ∀ α : ℝ, 0 < α → α < 1 / 2 → SievedLowerBoundExp α := by
  sorry


-- TODO: [Gr24, Comments to Problem 43] The toy problem (arising from a study of Problem 48):
-- for each prime `p` with `X ≤ p < 2X` choose a residue `a(p) (mod p)`; for distinct primes
-- `p₁, p₂` in this range let `f(p₁, p₂) ∈ ℤ/p₁p₂ℤ` be the unique CRT solution of
-- `f ≡ a(pᵢ) (mod pᵢ)`. What can be said about `a` if
-- `|E_{X ≤ p₁,p₂ < 2X} e(f(p₁,p₂)/(p₁ p₂))| ≥ 0.99` (more ambitiously `≥ 0.01`, or smaller)?
-- Green only asks the open-ended "what can be said about `a`?", suggesting "perhaps `a` must be
-- almost constant". Since "almost constant" is not made precise and a faithful encoding would
-- require choosing an interpretation, this is left as a TODO to formalize.

-- TODO: [Gr24, Comments to Problem 43] Green observes (unpublished) that, by arguments of
-- Bourgain, progress for `α ≈ 1` would imply the Kakeya conjecture. Formalising this implication
-- requires a precise statement of the Kakeya conjecture and is left for future work.

-- TODO: Check the primary sources for further variants. (1) The favourite variant is "raised in
-- [AP92]" (Alon–Peres, *Uniform dilations*, GAFA 1992); that paper is not freely available and
-- has not been checked here for additional uniform-dilation conjectures. (2) [Gr18, Section 4]
-- (where Problem 43 is formulated) raises, in the remarks to its bilinear estimate, the related
-- auxiliary open problem `∑_{n ≤ X} μ(n) Λ(n - 1) = o(X)` ("the heart of the matter"). These
-- are left as TODOs to formalize.

end Green43
