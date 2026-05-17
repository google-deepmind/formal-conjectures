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

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

/-!
# The Lovász Local Lemma

**Verbatim statement (symmetric form, Erdős–Lovász 1975):**
> Let $A_1, \ldots, A_n$ be events, each of probability at most $p$, and suppose each $A_i$
> is independent of all but at most $d$ of the others. If $e \cdot p \cdot (d + 1) \leq 1$,
> then $\Pr\!\left(\bigcap_i A_i^{\mathsf c}\right) > 0$.

That is: under the hypothesis, with positive probability none of the "bad" events occur,
so a configuration avoiding all of them exists.

The **general (asymmetric) form** replaces the "at most $d$" bound by a *dependency graph*
$G$ on $\{1,\ldots,n\}$ — each $A_i$ is jointly independent of $\{A_j : j \notin \Gamma(i)\}$ —
and the hypothesis by the existence of reals $0 \leq x_i < 1$ with
$\Pr(A_i) \leq x_i \prod_{j \in \Gamma(i)} (1 - x_j)$.

## Reference

- [EL75] Erdős, P. and Lovász, L. (1975). "Problems and results on 3-chromatic hypergraphs and
  some related questions." In *Infinite and Finite Sets* (A. Hajnal, ed.), North-Holland,
  pp. 609--627.
-/

namespace Probability.LovaszLocalLemma

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Real-analytic core bound for the symmetric LLL.**

For every natural number `d`,
  `(1 - 1/(d+1))^d ≥ 1/e`.

This is the key real-analytic inequality used in the symmetric form of the Lovász Local
Lemma: it shows that the symmetric hypothesis `e · p · (d+1) ≤ 1` implies the asymmetric
hypothesis with `x_i := 1/(d+1)`. The sequence `((d/(d+1))^d)_{d≥1}` decreases to `1/e`
from above, so finite terms all lie above the limit.

**Proof.** For `d = 0` the left side is `0^0 = 1`, which exceeds `1/e`. For `d ≥ 1` use
Mathlib's `Real.add_one_le_exp (1/d)`: rearranging gives `(d+1)/d ≤ exp(1/d)`, hence
`d/(d+1) ≥ exp(-1/d)`, and raising to the `d`-th power yields
`(d/(d+1))^d ≥ exp(-1) = 1/e`. -/
lemma Real.one_sub_one_div_succ_pow_ge_inv_exp (d : ℕ) :
    1 / Real.exp 1 ≤ (1 - 1 / (d + 1 : ℝ)) ^ d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- d = 0: right side = 1, left side = 1/e ≤ 1.
    subst hd
    simp only [pow_zero]
    rw [div_le_one (Real.exp_pos _)]
    exact Real.one_le_exp (by norm_num)
  · -- d ≥ 1. Let `D := (d : ℝ)`. Then `D > 0`.
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    -- Step 1: `add_one_le_exp` at `1/d` gives `(d+1)/d ≤ exp(1/d)`, i.e. `1 + 1/d ≤ exp(1/d)`.
    have h1 : 1 / (d : ℝ) + 1 ≤ Real.exp (1 / d) := Real.add_one_le_exp _
    -- Hence `exp(1/d) > 0` (obvious) and `1 + 1/d > 0`, so reciprocals reverse the inequality:
    have hposL : (0 : ℝ) < 1 / (d : ℝ) + 1 := by positivity
    have hposR : (0 : ℝ) < Real.exp (1 / d) := Real.exp_pos _
    -- Rewrite `1 + 1/d = (d+1)/d` and show `d/(d+1) = 1 - 1/(d+1)`:
    have hrecip : 1 - 1 / ((d : ℝ) + 1) = d / (d + 1) := by
      have hne : ((d : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    -- Step 2: take reciprocals in `1 + 1/d ≤ exp(1/d)`.
    -- Gives `1 / exp(1/d) ≤ 1 / (1 + 1/d)`, i.e. `exp(-1/d) ≤ d/(d+1)`.
    have h2 : 1 / Real.exp (1 / d) ≤ 1 / (1 / (d : ℝ) + 1) :=
      one_div_le_one_div_of_le hposL h1
    have h3 : 1 / (1 / (d : ℝ) + 1) = d / (d + 1) := by
      have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdR
      have hne : ((d : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    -- Combined: `1 / exp(1/d) ≤ d / (d + 1)`.
    have h4 : 1 / Real.exp (1 / d) ≤ (d : ℝ) / (d + 1) := h2.trans_eq h3
    -- Nonnegativity of LHS needed for `pow_le_pow_left₀`.
    have hLHS_nn : (0 : ℝ) ≤ 1 / Real.exp (1 / d) := by positivity
    -- Step 3: raise both sides to the `d`-th power (both nonnegative).
    have h5 : (1 / Real.exp (1 / d)) ^ d ≤ ((d : ℝ) / (d + 1)) ^ d :=
      pow_le_pow_left₀ hLHS_nn h4 d
    -- Step 4: compute `(1 / exp(1/d))^d = 1 / exp 1`.
    have h6 : (1 / Real.exp (1 / (d : ℝ))) ^ d = 1 / Real.exp 1 := by
      rw [div_pow, one_pow, ← Real.exp_nat_mul]
      have : ((d : ℝ)) * (1 / d) = 1 := by
        field_simp
      rw [this]
    -- Finish: combine h5, h6, hrecip.
    calc 1 / Real.exp 1
        = (1 / Real.exp (1 / (d : ℝ))) ^ d := h6.symm
      _ ≤ ((d : ℝ) / (d + 1)) ^ d := h5
      _ = (1 - 1 / ((d : ℝ) + 1)) ^ d := by rw [hrecip]

/-- Neighbourhood condition: `i` and `j` are "dependent". In the symmetric form this means
the event `A j` lies in the dependency set of `A i`. We encode dependency by an arbitrary
symmetric relation; the canonical choice in the statement below is mutual independence of
`A i` from the family `{A j | ¬ dep i j}`. -/
def DependencySet (n : ℕ) := Fin n → Fin n → Prop

/-- The "bad" event intersection property: we seek to show `μ (⋂ i, (A i)ᶜ) > 0`. -/
def avoidsAll {n : ℕ} (A : Fin n → Set Ω) : Set Ω :=
  ⋂ i, (A i)ᶜ

/-- **API lemma**: `avoidsAll A = (⋃ i, A i)ᶜ`. Rewriting the intersection of complements as
the complement of the union makes many measure-theoretic manipulations easier. -/
lemma avoidsAll_eq_compl_iUnion {n : ℕ} (A : Fin n → Set Ω) :
    avoidsAll A = (⋃ i, A i)ᶜ := by
  unfold avoidsAll
  exact Set.compl_iUnion _ |>.symm

/-- **Arithmetic reduction from symmetric to asymmetric LLL hypothesis.**

Given the symmetric hypothesis `e · p · (d + 1) ≤ 1` (with `0 ≤ p`), the asymmetric
hypothesis with `x_i := 1/(d+1)` is satisfied: `p ≤ (1/(d+1)) · (1 - 1/(d+1))^d`.

This is the key arithmetic step linking the two forms of the LLL: it says that choosing
`x_i = 1/(d+1)` realizes the asymmetric bound from the symmetric constant `p`.

**Proof.** From `e · p · (d+1) ≤ 1` and `e, d+1 > 0`, `p ≤ 1 / (e · (d+1))`. Combine with
`1/e ≤ (1 - 1/(d+1))^d` (the core bound `one_sub_one_div_succ_pow_ge_inv_exp`) to conclude. -/
lemma sym_bound_le_asym_bound {p : ℝ} {d : ℕ}
    (_hp : 0 ≤ p) (hBound : Real.exp 1 * p * (d + 1 : ℝ) ≤ 1) :
    p ≤ (1 / ((d : ℝ) + 1)) * (1 - 1 / ((d : ℝ) + 1)) ^ d := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  -- Step 1: from `e * p * (d+1) ≤ 1` and `e * (d+1) > 0`, `p ≤ 1 / (e * (d+1))`.
  have hep : (0 : ℝ) < Real.exp 1 * ((d : ℝ) + 1) := by positivity
  have hpUB : p ≤ 1 / (Real.exp 1 * ((d : ℝ) + 1)) := by
    rw [le_div_iff₀ hep]
    linarith [hBound]
  -- Step 2: `1 / (e * (d+1)) = (1 / (d+1)) * (1 / e)`.
  have hRewrite : 1 / (Real.exp 1 * ((d : ℝ) + 1)) = (1 / ((d : ℝ) + 1)) * (1 / Real.exp 1) := by
    rw [one_div_mul_one_div, mul_comm]
  -- Step 3: multiply `1/e ≤ (1 - 1/(d+1))^d` by `1/(d+1) ≥ 0`.
  have hCore : 1 / Real.exp 1 ≤ (1 - 1 / ((d : ℝ) + 1)) ^ d :=
    Real.one_sub_one_div_succ_pow_ge_inv_exp d
  have hInvd1 : (0 : ℝ) ≤ 1 / ((d : ℝ) + 1) := by positivity
  have hMul : (1 / ((d : ℝ) + 1)) * (1 / Real.exp 1)
      ≤ (1 / ((d : ℝ) + 1)) * (1 - 1 / ((d : ℝ) + 1)) ^ d :=
    mul_le_mul_of_nonneg_left hCore hInvd1
  calc p ≤ 1 / (Real.exp 1 * ((d : ℝ) + 1)) := hpUB
    _ = (1 / ((d : ℝ) + 1)) * (1 / Real.exp 1) := hRewrite
    _ ≤ (1 / ((d : ℝ) + 1)) * (1 - 1 / ((d : ℝ) + 1)) ^ d := hMul

/-- **Symmetric Lovász Local Lemma** (Erdős–Lovász 1975).

Let `A_1, …, A_n` be events, each of probability at most `p`, and suppose each `A_i` is
(jointly) independent of the family `{A_j | ¬ dep i j}`. If the dependency graph has
maximum out-degree at most `d` (i.e., `#{j | dep i j} ≤ d` for all `i`) and
`e · p · (d + 1) ≤ 1`, then `μ (⋂ i, (A i)ᶜ) > 0`.

**Proof sketch (deferred).** The proof reduces to `asymmetric_LLL` via the choice
`x_i := 1/(d+1)` (for `d ≥ 1`; the case `d = 0` is trivially handled by mutual
independence directly):
1. **Arithmetic bridge.** From `e · p · (d+1) ≤ 1` we have
   `p ≤ (1/(d+1)) · (1 - 1/(d+1))^d` — this is `sym_bound_le_asym_bound`, landed
   sorry-free above. Its core is the real-analytic bound
   `Real.one_sub_one_div_succ_pow_ge_inv_exp`, also landed sorry-free.
2. **Product lower bound.** For any `Γ i ⊆ {j | dep i j ∧ j ≠ i}` with `|Γ i| ≤ d`,
   `∏ j ∈ Γ i, (1 - 1/(d+1)) = (d/(d+1))^{|Γ i|} ≥ (d/(d+1))^d = (1 - 1/(d+1))^d`,
   using `(d/(d+1)) < 1` and `|Γ i| ≤ d`.
3. **Independence transfer.** `iIndepSet` over `{j // ¬ dep i j}` restricts to
   `iIndepSet` over `{j // j ∉ Γ i ∧ j ≠ i}` via `iIndepSet.precomp` along the
   obvious subtype injection.
4. **Edge case `d = 0`.** All events are mutually independent, so
   `Pr(⋂ A_iᶜ) = ∏ Pr(A_iᶜ) ≥ (1 - 1/e)^n > 0`. This does not go through
   `asymmetric_LLL` directly (requires `x_i < 1`, which fails for `1/(d+1) = 1` at
   `d = 0`), but can be handled separately using mutual independence.

The remaining gap is the full formalisation of (2)–(4) and the underlying asymmetric form
itself (`asymmetric_LLL`). We leave this as `sorry` pending further probability-theory
infrastructure work on `ProbabilityTheory.cond`. -/
theorem symmetric_LLL {n : ℕ} [IsProbabilityMeasure μ]
    (A : Fin n → Set Ω) (hMeas : ∀ i, MeasurableSet (A i))
    (p : ℝ) (d : ℕ)
    (hp : ∀ i, (μ (A i)).toReal ≤ p)
    (dep : Fin n → Fin n → Prop)
    [DecidableRel dep]
    (hDep : ∀ i, (Finset.univ.filter fun j => dep i j).card ≤ d)
    (hIndep : ∀ i, iIndepSet (fun j : {j // ¬ dep i j} => A j.1) μ)
    (hBound : Real.exp 1 * p * (d + 1 : ℝ) ≤ 1) :
    0 < (μ (avoidsAll A)).toReal := by
  -- See module docstring for the proof outline. Executing the reduction to `asymmetric_LLL`
  -- via `x_i := 1/(d+1)` requires:
  -- * `iIndepSet.precomp` along the subtype injection
  --     `{j // j ∉ Γ i ∧ j ≠ i} → {j // ¬ dep i j}` where `Γ i := filter (dep i · ∧ · ≠ i)`.
  -- * Bounding `∏ j ∈ Γ i, (1 - 1/(d+1))` below by `(1 - 1/(d+1))^d` via `|Γ i| ≤ d` and
  --   `1 - 1/(d+1) < 1` (requires `d ≥ 1`).
  -- * Combining with `sym_bound_le_asym_bound` to discharge the asymmetric-LLL numerical
  --   hypothesis for every `i`.
  -- * A separate argument for `d = 0` (full mutual independence ⇒ explicit product).
  sorry

/-- **Asymmetric Lovász Local Lemma** (Erdős–Lovász 1975, general form).

Let `A_1, …, A_n` be events and let `Γ : Fin n → Finset (Fin n)` assign to each `i` a
"dependency neighbourhood". Suppose each `A_i` is jointly independent of
`{A_j | j ∉ Γ i ∧ j ≠ i}`. If there exist reals `0 ≤ x_i < 1` such that
`(μ (A i)).toReal ≤ x i * ∏ j ∈ Γ i, (1 - x j)`, then `μ (avoidsAll A) > 0`.

**Proof sketch (deferred).** Finite induction on subsets `S ⊆ Fin n`. Strengthened claim:
for every `S ⊆ Fin n` and every `i ∉ S`,
  `μ(A_i | ⋂_{j ∈ S} A_jᶜ) ≤ x_i`.
- **Base** `|S| = 0`: `μ(A_i) ≤ x_i · ∏_{j ∈ Γ(i)} (1 - x_j) ≤ x_i` since each
  `(1 - x_j) ≤ 1`.
- **Step.** Split `S = S₁ ⊔ S₂` where `S₁ := S ∩ Γ(i)` and `S₂ := S \ Γ(i)`. Then
    `μ(A_i | ⋂_S A_jᶜ) = μ(A_i ∩ ⋂_{S₁} A_jᶜ | ⋂_{S₂} A_jᶜ) / μ(⋂_{S₁} A_jᶜ | ⋂_{S₂} A_jᶜ)`.
  - Numerator `≤ μ(A_i | ⋂_{S₂} A_jᶜ) = μ(A_i)` by mutual independence of `A_i` from
    `{A_j : j ∉ Γ(i) ∧ j ≠ i} ⊇ {A_j : j ∈ S₂}`.
  - Denominator `≥ ∏_{j ∈ S₁} (1 - x_j)` by inductive hypothesis on `S \ {j}` for
    each `j ∈ S₁`.
  - Combined: ratio `≤ μ(A_i) / ∏_{S₁} (1 - x_j) ≤ x_i · ∏_{Γ(i)\S₁}(1 - x_j) ≤ x_i`.

Final step: `μ(⋂ A_iᶜ) = ∏_i μ(A_iᶜ | ⋂_{j<i} A_jᶜ) ≥ ∏_i (1 - x_i) > 0`.

**Status.** Deferred. Requires:
- `ProbabilityTheory.cond μ B` together with lemmas on conditional probability of
  intersections — Mathlib has `cond` but the specialized chain-rule manipulation across
  a finite split `S = S₁ ⊔ S₂` is custom bookkeeping.
- A strong-induction on `|S|` for the strengthened claim — standard `Finset.strongInductionOn`.
- A final product-telescope `μ(⋂_i A_iᶜ) = ∏_i μ(A_iᶜ | ⋂_{j<i} A_jᶜ)`.

The statement is recorded here so that downstream consumers (probabilistic Ramsey /
hypergraph colouring) can depend on its type. -/
theorem asymmetric_LLL {n : ℕ} [IsProbabilityMeasure μ]
    (A : Fin n → Set Ω) (_hMeas : ∀ i, MeasurableSet (A i))
    (Γ : Fin n → Finset (Fin n))
    (x : Fin n → ℝ)
    (_hxNonneg : ∀ i, 0 ≤ x i)
    (_hxLtOne : ∀ i, x i < 1)
    (_hIndep : ∀ i, iIndepSet
      (fun j : {j : Fin n // j ∉ Γ i ∧ j ≠ i} => A j.1) μ)
    (_hBound : ∀ i, (μ (A i)).toReal ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    0 < (μ (avoidsAll A)).toReal := by
  -- Standard finite induction. See [EL75] or any modern exposition.
  sorry

/-- **Helper** (API): in any probability space, `μ (avoidsAll A) = 1 - μ (⋃ i, A i)`. -/
lemma measure_avoidsAll_eq_one_sub {n : ℕ} [IsProbabilityMeasure μ]
    (A : Fin n → Set Ω) (hMeas : ∀ i, MeasurableSet (A i)) :
    (μ (avoidsAll A)).toReal = 1 - (μ (⋃ i, A i)).toReal := by
  rw [avoidsAll_eq_compl_iUnion]
  have hmeas : MeasurableSet (⋃ i, A i) := MeasurableSet.iUnion hMeas
  rw [prob_compl_eq_one_sub hmeas]
  rw [ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]

end Probability.LovaszLocalLemma
