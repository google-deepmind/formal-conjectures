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

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Twin primes and Brun's constant

This file defines the twin prime lower-member predicate `IsTwinPrimeLower` and Brun's twin prime
constant `brunConstant` (OEIS A065421).
-/

@[expose] public section

/-- `p` is the lesser member of a twin prime pair `(p, p + 2)`. -/
def IsTwinPrimeLower (p : ℕ) : Prop := p.Prime ∧ (p + 2).Prime

/-- Reciprocal-pair summand $1/p + 1/(p + 2)$ attached to a natural number $p$. -/
noncomputable def twinPrimeTerm (p : ℕ) : ℝ :=
  (1 : ℝ) / (p : ℝ) + (1 : ℝ) / ((p : ℝ) + 2)

/-- Brun's constant $B_2 = \sum_{p, p+2 \text{ prime}} (1/p + 1/(p + 2))$ (OEIS A065421, where
$1/5$ appears in both $(3, 5)$ and $(5, 7)$). -/
noncomputable def brunConstant : ℝ :=
  ∑' p : {p : ℕ // IsTwinPrimeLower p}, twinPrimeTerm p.1

theorem IsTwinPrimeLower.prime_left {p : ℕ} (h : IsTwinPrimeLower p) : p.Prime :=
  h.1

theorem IsTwinPrimeLower.prime_add_two {p : ℕ} (h : IsTwinPrimeLower p) : (p + 2).Prime :=
  h.2
