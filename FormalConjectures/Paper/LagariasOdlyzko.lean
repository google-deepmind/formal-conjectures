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
# Lagarias–Odlyzko: sharpness of the low-density subset-sum attack

Lagarias and Odlyzko attack a subset-sum instance `(a, M)`, `M = ∑ eᵢ aᵢ` with `e ∈ {0,1}ⁿ`, by
finding a shortest vector of the lattice `L(a, M)`, which contains the planted vector `(e, 0)`.
They prove (Thm 3.3) that for density `d(a) = n / log₂ max aᵢ < 1/1.54725 = 0.6463…` the planted
vector is the shortest nonzero vector for almost all `a`, and in §5(2) they conjecture that this
is sharp, with critical density `β₀ = 1/c₀`:

> "(2) We conjecture that Theorem 3.3 is sharp in the sense that there is a critical density β₀
> below which Theorem 3.3 is true for "almost all" subset sum problems of density d(a) ≤ β for any
> β < β₀ and true for "almost no" subset sum problems with d(a) ≥ β for any fixed β > β₀; here we
> average not only over all sets a₁, …, aₙ of the given density, but also over all binary vectors
> e, so that Σ eᵢ ~ n/2 holds for almost all of them. Furthermore, we conjecture that this critical
> density is β₀ = (c₀)⁻¹ = 0.645…, …" [LO85, §5(2), pp. 242–243]

(Quotation transcribed from an OCR text of the journal scan; ellipses as in our transcription.)
Here `c₀ = lim (1/n) log₂ #{x ∈ ℤⁿ : ‖x‖² ≤ n/2} = 1.5472433…` [LO85, (5.1)], so
`β₀ = 0.6463107…`; LO's printed decimal "0.645…" is not the expansion of `(c₀)⁻¹`, and we use the
defining expression `(c₀)⁻¹`.

This file states the "almost no" half: above density `1/c₀`, for almost every weight vector
`a ∈ [1, B]ⁿ` with `B = ⌊2^{n/d}⌋` (i.e. among all `a` of density `≥ d`), *no* 0/1 vector `e` of
weight `≥ (1/2 − δ)n` makes `(e, 0)` a shortest vector of `L(a, M(a, e))`. This is uniform in `e`,
hence implies the version averaged over `e` with `∑ eᵢ ~ n/2`. The "almost all" half for
`β < 1/c₀` is LO's Theorem 3.3 (for `∑ eᵢ ≤ n/2`), and is not stated here.

*References:*
* [LO85] Lagarias, J. C., and Odlyzko, A. M. (1985). "Solving low-density subset sum problems."
  *J. ACM* 32(1), pp. 229--246. [doi:10.1145/2455.2461](https://doi.org/10.1145/2455.2461)
-/

@[expose] public section

namespace LagariasOdlyzko

/-- The basis of the Lagarias–Odlyzko lattice [LO85, (2.4)]: `b_i = (u_i, -a_i)` for `i ≤ n`
(`u_i` the `i`-th unit vector) and `b_{n+1} = (0, M)`, as vectors in `ℤⁿ × ℤ`. -/
def basis {n : ℕ} (a : Fin n → ℤ) (M : ℤ) : Fin n ⊕ Unit → (Fin n → ℤ) × ℤ
  | .inl i => (Pi.single i 1, -a i)
  | .inr _ => (0, M)

/-- The Lagarias–Odlyzko lattice `L(a, M) ⊆ ℤⁿ × ℤ` spanned by `basis a M` [LO85, (2.4)]. -/
def lattice {n : ℕ} (a : Fin n → ℤ) (M : ℤ) : Submodule ℤ ((Fin n → ℤ) × ℤ) :=
  Submodule.span ℤ (Set.range (basis a M))

/-- The subset-sum target `M(a, e) = ∑ eᵢ aᵢ` of the planted solution `e` [LO85, (3.2)]. -/
def target {n : ℕ} (a e : Fin n → ℤ) : ℤ := ∑ i, e i * a i

/-- The squared Euclidean norm on `ℤⁿ × ℤ`. -/
def sqNorm {n : ℕ} (v : (Fin n → ℤ) × ℤ) : ℤ := (∑ i, v.1 i ^ 2) + v.2 ^ 2

/-- The planted vector `(e, 0) ∈ L(a, M(a, e))` [LO85, (3.4)] is *a* shortest nonzero vector of
the lattice: no nonzero lattice vector is strictly shorter. Ties are allowed, so this is the
weakest reading of "`e` is the nonzero vector of shortest Euclidean norm in `L`" [LO85, Thm 3.3],
and "almost no `a` satisfy it" is the strongest reading of the "almost no" half of [LO85, §5(2)].
In particular it is implied by "`±(e, 0)` are the only shortest nonzero vectors". -/
def PlantedIsShortest {n : ℕ} (a e : Fin n → ℤ) : Prop :=
  ∀ w ∈ lattice a (target a e), w ≠ 0 → sqNorm ((e, 0) : (Fin n → ℤ) × ℤ) ≤ sqNorm w

/-- The Jacobi theta function `θ(s) = ∑_{k ∈ ℤ} e^{-s k²}` (for `s > 0`). -/
noncomputable def theta (s : ℝ) : ℝ := ∑' k : ℤ, Real.exp (-s * (k : ℝ) ^ 2)

/-- The constant `c₀ = inf_{s > 0} (log₂ θ(s) + s · (1/2) / ln 2) = 1.5472433…`.
By the saddle-point (Chernoff) bound and its converse, this infimum is
`lim_{n → ∞} (1/n) log₂ #{x ∈ ℤⁿ : ‖x‖² ≤ n/2}`, which is how [LO85, (5.1)] defines `c₀`
(this equality is proved in Lean as `PaperResults.lemma0` in the repository linked below); LO's
Thm 3.2 evaluates the same expression at `s = x₀ = 0.997994` to get `c₀ ≤ 1.54725`.
The conjectured critical density is `β₀ = 1/c₀ = 0.6463107…`. -/
noncomputable def c₀ : ℝ :=
  ⨅ s : Set.Ioi (0 : ℝ), (Real.logb 2 (theta s) + s * (1 / 2) / Real.log 2)

/-- The sample space of LO's weights `a ∈ [1, B]ⁿ` [LO85, (3.3)]. -/
noncomputable def sampleBox (n B : ℕ) : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => Finset.Icc (1 : ℤ) B

set_option linter.style.formal_proof_palomar false in
open Classical in
/--
**The "almost no" half of the Lagarias–Odlyzko sharpness conjecture** [LO85, §5(2)].

For every density `d > 1/c₀ = 0.6463…` there is `δ > 0` such that for every `η > 0` and all large
`n`, among the weight vectors `a ∈ [1, B]ⁿ`, `B = ⌊2^{n/d}⌋`, at most a fraction `η` admit some
`e ∈ {0,1}ⁿ` with `∑ eᵢ ≥ (1/2 − δ)n` for which the planted vector `(e, 0)` is a shortest nonzero
vector of the lattice `L(a, ∑ eᵢ aᵢ)`.
-/
@[category research solved, AMS 11 52 68, formal_proof using lean4 at
  "https://github.com/Attia-Ahmed/formal-proofs/blob/main/PNP/PaperResults.lean#L5378"]
theorem almost_no_above_critical_density (d : ℝ) (hd : 1 / c₀ < d) :
    ∃ δ > 0, ∀ η > 0, ∀ᶠ n in Filter.atTop,
      (((sampleBox n ⌊(2 : ℝ) ^ ((n : ℝ) / d)⌋₊).filter fun a =>
          ∃ e : Fin n → ℤ, (∀ i, e i = 0 ∨ e i = 1) ∧ (1 / 2 - δ) * (n : ℝ) ≤ ∑ i, (e i : ℝ) ∧
            PlantedIsShortest a e).card : ℝ) ≤
        η * (⌊(2 : ℝ) ^ ((n : ℝ) / d)⌋₊ : ℝ) ^ n := by
  sorry

end LagariasOdlyzko
