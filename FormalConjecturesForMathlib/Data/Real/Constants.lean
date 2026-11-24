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

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

/-! # Standard real valued constants

This file is for storing the definition of standard real constants that arise in conjectures.

-/

open Real

/--
**Gompertz constant**
$$\delta = -e * \int_1^∞ e^{-t}/t dt \approx 0.59634$$
-/
noncomputable def gompertzConstant : ℝ :=
  -exp 1 * ∫ (t:ℝ) in Set.Ioi 1, exp (-t) / t

/--
**Catalan's constant**
$$G = \sum_{n=0}^∞ (-1)^n / (2n + 1)^2 \approx 0.91596$$
-/
noncomputable def catalanConstant : ℝ :=
  ∑' n : ℕ, (-1)^n / (2*n + 1)^2

/-- The $k$-th decimal digit ($0$-indexed) after the radix point of Champernowne's decimal constant
$C_{10} = 0.1234567891011\dots$, read from the concatenated big-endian base-$10$ digits of
$1, 2, \dots, k + 1$. -/
def champernowneDigit (k : ℕ) : ℕ :=
  (((List.range (k + 1)).flatMap fun j => (Nat.digits 10 (j + 1)).reverse)).getD k 0

/--
**Champernowne's decimal constant**
$$C_{10} = \sum_{k=0}^{\infty} \frac{d_k}{10^{k+1}} \approx 0.1234567891$$
-/
noncomputable def champernowneConstant : ℝ :=
  ∑' k : ℕ, (champernowneDigit k : ℝ) / (10 : ℝ) ^ (k + 1)

/-- Paired Dirichlet summand $(3n + 1)^{-2} - (3n + 2)^{-2}$ in $L(2, \chi_{-3})$. -/
noncomputable def giesekingTerm (n : ℕ) : ℝ :=
  1 / (3 * (n : ℝ) + 1) ^ 2 - 1 / (3 * (n : ℝ) + 2) ^ 2

/--
**Gieseking's constant**
$$V = \frac{3\sqrt{3}}{4} \sum_{n=0}^{\infty}
  \left(\frac{1}{(3n + 1)^2} - \frac{1}{(3n + 2)^2}\right) \approx 1.01494$$
-/
noncomputable def giesekingConstant : ℝ :=
  (3 * Real.sqrt 3 / 4) * ∑' n : ℕ, giesekingTerm n

/-- Inner logarithmic integral $\mathrm{li}(x) = \int_0^x \frac{dt}{\log t}$ on $[0, 1)$. -/
noncomputable def golombDickmanInner (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, 1 / Real.log t

/--
**Golomb–Dickman constant**
$$\lambda = \int_0^1 \exp\left(\int_0^x \frac{dt}{\log t}\right) dx \approx 0.62432$$
-/
noncomputable def golombDickmanConstant : ℝ :=
  ∫ x in (0 : ℝ)..1, Real.exp (golombDickmanInner x)

/-- Factor at index $r$ in the Euler-type product for Khinchin's constant: equal to $1$ at $r = 0$,
and $\bigl(1 + \frac{1}{r(r+2)}\bigr)^{\log r / \log 2}$ for $r \ge 1$. -/
noncomputable def khinchinFactor (r : ℕ) : ℝ :=
  if r = 0 then 1
  else (1 + 1 / ((r : ℝ) * ((r : ℝ) + 2))) ^ (Real.log (r : ℝ) / Real.log 2)

/--
**Khinchin's constant**
$$K_0 = \prod_{r=1}^{\infty} \left(1 + \frac{1}{r(r + 2)}\right)^{\log_2 r} \approx 2.68545$$
-/
noncomputable def khinchinConstant : ℝ :=
  ∏' r : ℕ, khinchinFactor r
