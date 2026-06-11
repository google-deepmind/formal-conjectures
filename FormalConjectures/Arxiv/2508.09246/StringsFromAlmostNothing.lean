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
import FormalConjectures.Arxiv.«2502.20372».VirasoroShapiro

/-!
# Strings from Almost Nothing

*Reference:* [arxiv/2508.09246](https://arxiv.org/abs/2508.09246)
**Strings from Almost Nothing**
by *Clifford Cheung, Grant N. Remmen, Francesco Sciotti, Michele Tarquini*

Any tree-level, crossing-symmetric, unitary four-point amplitude with poles at masses
`μ(n)` and maximal spin `J(n)` at level `n`, and Regge behavior `A(s,t) ~ f(t) s^{α(t)}`,
is forced by consistency to have residues vanishing on the "Regge zeros" `α(t) + r = 0`
(eq. 6). The paper's uniqueness argument: assuming
(i) *ultrasoftness* — the Regge trajectory `α` is bijective for `t < 0` with
    `α(t) → -∞` as `t → -∞`, and
(ii) *minimal zeros* — the residues consist of Regge zeros and nothing more, i.e.
    `R(n,t) = c(n) ∏_{r=1}^{N(n)} (α(t) + r)^h` (eq. 12),
the spectrum and trajectory are forced to be linear, `μ(n) ~ J(n) ~ n`, `α(t) ~ t`
(eq. 13), and the amplitude is *uniquely* the Veneziano amplitude
`Γ(-s)Γ(-t)/Γ(-s-t)`; the nonplanar analogue lands on Virasoro–Shapiro.

The string residues themselves (eq. 7) are `R_str(n,t) = (1/n!) ∏_{r=1}^{n} (t+r)`,
with Regge zeros at `t = -1, …, -n`; these we formalise concretely. See
`FormalConjectures/Arxiv/2502.20372/VenezianoPositivity.lean` for the companion
positivity benchmark for the same amplitude.
-/

namespace Arxiv.«2508.09246»

open Polynomial

/--
Eq. (7): the level-`n` residue of the (bosonic-convention) string amplitude,
$$R_{\mathrm{str}}(n,t) = \frac{1}{n!} \prod_{r=1}^{n} (t+r).$$
-/
noncomputable def stringResidue (n : ℕ) : ℝ[X] :=
  C ((n.factorial : ℝ)⁻¹) * ∏ r ∈ Finset.range n, (X + C ((r : ℝ) + 1))

/-- The string residue at level `n` has its Regge zeros at `t = -1, …, -n` (eq. 6/7). -/
@[category test, AMS 81]
theorem stringResidue_regge_zero {n r : ℕ} (h1 : 1 ≤ r) (hn : r ≤ n) :
    (stringResidue n).eval (-(r : ℝ)) = 0 := by
  have hmem : r - 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have hzero : (-(r : ℝ)) + (((r - 1 : ℕ) : ℝ) + 1) = 0 := by
    have : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      push_cast [Nat.cast_sub h1]; ring
    rw [this]; ring
  simp only [stringResidue, eval_mul, eval_prod, eval_add, eval_C, eval_X]
  rw [Finset.prod_eq_zero hmem hzero, mul_zero]

/-- The Regge zeros of the string residue are *exactly* `t = -1, …, -n`: assumption (ii)
("minimal zeros") holds for the string — the residues contain the consistency-mandated zeros
and nothing more. Strengthens `stringResidue_regge_zero` to a characterization. -/
@[category test, AMS 81]
theorem stringResidue_eval_eq_zero_iff {n : ℕ} {t : ℝ} :
    (stringResidue n).eval t = 0 ↔ ∃ r : ℕ, 1 ≤ r ∧ r ≤ n ∧ t = -(r : ℝ) := by
  simp only [stringResidue, eval_mul, eval_prod, eval_add, eval_C, eval_X]
  rw [mul_eq_zero]
  constructor
  · rintro (hfac | hprod)
    · exact absurd hfac (by positivity)
    · obtain ⟨i, hi, hzero⟩ := Finset.prod_eq_zero_iff.mp hprod
      refine ⟨i + 1, by omega, by have := Finset.mem_range.mp hi; omega, ?_⟩
      push_cast
      linarith
  · rintro ⟨r, h1, hn, rfl⟩
    right
    apply Finset.prod_eq_zero (Finset.mem_range.mpr (show r - 1 < n by omega))
    have : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by push_cast [Nat.cast_sub h1]; ring
    rw [this]
    ring

/-- For `t > 0` the string residue is strictly positive — there are no residue zeros in the
physical region (as noted below eq. 6). -/
@[category test, AMS 81]
theorem stringResidue_pos {n : ℕ} {t : ℝ} (ht : 0 < t) : 0 < (stringResidue n).eval t := by
  simp only [stringResidue, eval_mul, eval_prod, eval_add, eval_C, eval_X]
  have hfac : (0 : ℝ) < ((n.factorial : ℝ))⁻¹ := by positivity
  refine mul_pos hfac (Finset.prod_pos fun r _ => ?_)
  positivity

/--
**Main theorem, algebraic core (eq. 12 ⟹ eq. 13).** Suppose every level-`n` residue is
built entirely out of Regge zeros of a polynomial trajectory `α` with constant multiplicity
`h ≥ 1` (the minimal-zero ansatz, eq. 12), the maximal spin at level `n` equals the residue's
degree and matches the trajectory at the pole (`α(μ n) = J n`, eq. 2), with infinitely many
levels. Then ultrasoftness forces a *linear* Regge trajectory: `h = 1` and `deg α = 1`.
-/
@[category research solved, AMS 81]
theorem trajectory_linear (α : ℝ[X]) (hα : 1 ≤ α.natDegree)
    (μ : ℕ → ℝ) (hμ : StrictMono μ) (hμtop : Filter.Tendsto μ Filter.atTop Filter.atTop)
    (J N : ℕ → ℕ) (c : ℕ → ℝ) (h : ℕ)
    (hh : 1 ≤ h) (hc : ∀ n, c n ≠ 0) (hN : Filter.Tendsto N Filter.atTop Filter.atTop)
    (R : ℕ → ℝ[X])
    (hR : ∀ n, R n = C (c n) * ∏ r ∈ Finset.range (N n), (α + C ((r : ℝ) + 1)) ^ h)
    (hdeg : ∀ n, (R n).natDegree = J n)
    (hspin : ∀ n, α.eval (μ n) = J n)
    -- Regge scaling (eq. 5): in the Regge region the residues scale as `μ(n)^{α(t)}`, i.e.
    -- `log |R(n,t)| / log μ(n) → α(t)`. Without this hypothesis the statement is false
    -- (e.g. `α = X²`, `h = 2` satisfies all the algebraic conditions).
    (hRegge : ∀ t : ℝ, t < 0 → (∀ n, (R n).eval t ≠ 0) →
      Filter.Tendsto (fun n => Real.log |(R n).eval t| / Real.log (μ n))
        Filter.atTop (nhds (α.eval t))) :
    h = 1 ∧ α.natDegree = 1 := by
  sorry

/--
**Uniqueness of the Veneziano amplitude (four-point planar), residue form.** Under the
minimal-zero ansatz and ultrasoftness, the residues are — up to an overall normalization and
the linear reparametrization `α(t) = t` fixed by eq. 13 — precisely the string residues of
eq. 7: bootstrapping zeros alone lands on the Veneziano amplitude.
-/
@[category research solved, AMS 81]
theorem veneziano_uniqueness (α : ℝ[X]) (hα : α = X)
    (μ : ℕ → ℝ) (hμ : ∀ n, μ n = n) (N : ℕ → ℕ) (hN : ∀ n, N n = n) (c : ℕ → ℝ)
    (hc : ∀ n, 0 < c n)
    (R : ℕ → ℝ[X])
    (hR : ∀ n, R n = C (c n) * ∏ r ∈ Finset.range (N n), (α + C ((r : ℝ) + 1)))
    -- normalization: unit residue at the first pole, as for `Γ(-s)Γ(-t)/Γ(-s-t)`
    (hnorm : ∀ n, (R n).leadingCoeff = (n.factorial : ℝ)⁻¹) :
    ∀ n, R n = stringResidue n := by
  sorry

/--
**Nonplanar endpoint: Virasoro–Shapiro.** The nonplanar bootstrap of this paper (eqs. 14–18)
lands on the Virasoro–Shapiro amplitude, whose partial-wave positivity in `D ≤ 10` is the
shared statement formalised with the companion paper arXiv:2502.20372 (§3.1). Pointer per
repository convention.
-/
@[category research solved, AMS 33 81]
theorem virasoro_shapiro_positivity :
    type_of% @Arxiv.«2502.20372».virasoro_shapiro_positivity := by
  sorry

end Arxiv.«2508.09246»
