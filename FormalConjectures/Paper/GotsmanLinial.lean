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
# The Gotsman–Linial conjecture

A *polynomial threshold function* of degree $d$ on the cube $\{-1, 1\}^n$ is the sign of a real
polynomial of degree at most $d$. Its *average sensitivity* is the expected number of
coordinates whose flip changes the value at a uniformly random point.

Gotsman and Linial [GL94] conjectured that the symmetric function changing sign on the $d$
middle layers of the cube has the largest average sensitivity among degree-$d$ polynomial
threshold functions. Its asymptotic form states that the average sensitivity is $O(d \sqrt{n})$.
Kane [Ka14] proved the bound $\sqrt{n} \, (\log n)^{O(d \log d)} \, 2^{O(d^2 \log d)}$.

*References:*
- [GL94] C. Gotsman and N. Linial, *Spectral properties of threshold functions*,
  Combinatorica 14 (1994), 35–50.
- [Ka14] D. M. Kane, *The correct exponent for the Gotsman–Linial conjecture*,
  Comput. Complexity 23 (2014), 151–175.
- [OAI26] OpenAI, *Average Sensitivity of Polynomial Threshold Functions*. OpenAI Math Release
  preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Average-Sensitivity-of-Polynomial-Threshold-Functions-September-25-2026/main.pdf
-/

@[expose] public section

namespace GotsmanLinial

/-- The cube `{-1, 1}ⁿ`, with `true` for `1` and `false` for `-1`. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- The `i`-th coordinate of `x` as `±1`. -/
def cubeCoord {n : ℕ} (x : Cube n) (i : Fin n) : ℝ :=
  if x i then 1 else -1

/-- Flip the `i`-th coordinate. -/
def flip {n : ℕ} (i : Fin n) (x : Cube n) : Cube n :=
  Function.update x i (!(x i))

/-- The sign of `t`, with `0 ↦ 1`. -/
noncomputable def thresholdSign (t : ℝ) : ℝ :=
  if 0 ≤ t then 1 else -1

/-- The points at which flipping the `i`-th coordinate changes `f`. -/
noncomputable def sensitiveVertices {n : ℕ} (f : Cube n → ℝ) (i : Fin n) :
    Finset (Cube n) := by
  classical
  exact Finset.univ.filter fun x => f x ≠ f (flip i x)

/-- The average sensitivity of `f`: the sum over `i` of the probability that flipping the
`i`-th coordinate changes `f`. -/
noncomputable def averageSensitivity {n : ℕ} (f : Cube n → ℝ) : ℝ :=
  ∑ i : Fin n, ((sensitiveVertices f i).card : ℝ) / (2 : ℝ) ^ n

/-- Every monomial of `p` has degree at most one in each variable. -/
def IsMultilinear {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ m ∈ p.support, ∀ i : Fin n, m i ≤ 1

/-- The value of `p` at the point `x` of the cube. -/
noncomputable def polynomialValue {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (x : Cube n) : ℝ :=
  MvPolynomial.eval (cubeCoord x) p

/-- The polynomial threshold function `x ↦ sign (p x)`. -/
noncomputable def polynomialThreshold {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Cube n → ℝ :=
  fun x => thresholdSign (polynomialValue p x)

/--
**The Gotsman–Linial conjecture**, asymptotic form [GL94]: the average sensitivity of a
polynomial threshold function of degree $d$ in $n$ variables is $O(d \sqrt{n})$.

This was proved by an internal OpenAI model in September 2026, with constant $8$ [OAI26]; see
`gotsman_linial_conjecture.variants.openai` and OpenAI's Lean proof. Multilinearity loses no
generality on the cube.
-/
@[category research solved, AMS 6 68]
theorem gotsman_linial_conjecture :
    ∃ C : ℝ, ∀ (n d : ℕ), 1 ≤ d → d ≤ n →
      ∀ p : MvPolynomial (Fin n) ℝ, IsMultilinear p → p.totalDegree ≤ d →
        averageSensitivity (polynomialThreshold p) ≤ C * d * Real.sqrt n := by
  sorry

/--
The statement of OpenAI's Lean proof [OAI26]: the bound holds with constant $8$.
-/
@[category research solved, AMS 6 68]
theorem gotsman_linial_conjecture.variants.openai :
    ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d → d ≤ n →
      ∀ p : MvPolynomial (Fin n) ℝ,
        IsMultilinear p → p.totalDegree ≤ d →
          averageSensitivity (polynomialThreshold p) ≤ 8 * (d : ℝ) * Real.sqrt (n : ℝ) := by
  sorry

/-- The bound with constant `8` gives the asymptotic form. -/
@[category test, AMS 6 68]
theorem gotsman_linial_conjecture_of_openai
    (h : type_of% gotsman_linial_conjecture.variants.openai) :
    type_of% gotsman_linial_conjecture :=
  ⟨8, fun n d hd hdn p hp hdeg => h n d (hd.trans hdn) hd hdn p hp hdeg⟩

end GotsmanLinial
