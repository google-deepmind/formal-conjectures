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

import FormalConjectures.Util.ProblemImports

/-!
# Bateman-Horn Conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Bateman%E2%80%93Horn_conjecture)
-/

/-
Note: This formalization was one-shot (with minimal cleaning) from Claude 4.0 Sonnet; see:
https://claude.ai/share/a02c2bba-7f5f-435c-ab0e-58eb5ddc0545
-/

open Polynomial Asymptotics Filter Topology

/-- Definition of irreducible polynomial with positive leading coefficient -/
def IsIrreducibleWithPosLeading (f : ℤ[X]) : Prop :=
  Irreducible f ∧ 0 < f.leadingCoeff

/-- The compatibility condition for a finite set `S` of polynomials in the Bateman-Horn conjecture. 
This states that for all primes `p`, there exists an `n` such that `∏ f ∈ S, f.eval n` is non-zero modulo `p`. -/
def SatisfiesCompatibilityCondition (polys : Finset ℤ[X]) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ∃ n : ℤ, ¬↑p ∣ (polys.prod id).eval n

/-- `OmegaP S p` counts the number of residue classes mod `p` where at least one polynomial in `S` vanishes. -/
noncomputable def OmegaP (polys : Finset ℤ[X]) (p : ℕ) : ℕ :=
  {n : ZMod p | ∃ f ∈ polys, (f.map (Int.castRingHom (ZMod p))).eval n = 0}.ncard 

/-- The Bateman-Horn constant of a set of polynomials `S`. This is defined as the infinite product over all primes: 
$$\prod_p (1 - \frac{1}{p}) ^ {|S|} (1 - \frac{\omega_p(S)}{p}$$ where $\omega_p(S)}{p}$ is the number of residue classes mod $p$ where at least one polynomial in $S$ vanishes. -/
noncomputable def BatemanHornConstant (polys : Finset ℤ[X]) : ℝ :=
  ∏' p : {p : ℕ // Nat.Prime p},
    (1 - (1 : ℝ) / p.val) ^ (-polys.card : ℤ) *
    (1 - (OmegaP polys p.val : ℝ) / p.val)

/-- `CountSimultaneousPrimes S x` counts the number of `n ≤ x` at which all polynomials in `S` attain a prime value. -/
noncomputable def CountSimultaneousPrimes (polys : Finset ℤ[X]) (x : ℝ) : ℕ :=
  Finset.card (Finset.filter
    (fun n : ℕ => ∀ f ∈ polys, (f.eval ↑n).natAbs.Prime)
    (Finset.range (⌊x⌋₊ + 1)))

/-- **The Bateman-Horn Conjecture**

Given a finite collection of distinct irreducible polynomials f₁, f₂, ..., fₖ ∈ ℤ[X] 
with positive leading coefficients that satisfy the compatibility condition, the number 
of positive integers n ≤ x for which all polynomials f₁(n), f₂(n), ..., fₖ(n) are 
simultaneously prime is asymptotic to:

    C(f₁, f₂, ..., fₖ) · x / (log x)^k

where C(f₁, f₂, ..., fₖ) is the Bateman-Horn constant given by the convergent infinite product:

    C = ∏ₚ (1 - 1/p)^(-k) · (1 - ωₚ/p)

Here ωₚ is the number of residue classes modulo p for which at least one polynomial vanishes.

The compatibility condition ensures that for each prime p, there exists some integer n 
such that p does not divide the product f₁(n)·f₂(n)·...·fₖ(n), which guarantees the 
infinite product converges to a positive value. -/
@[category research open, AMS 11 12]
theorem bateman_horn_conjecture
    (polys : Finset ℤ[X])
    (h_nonempty : polys.Nonempty)
    (h_irreducible : ∀ f ∈ polys, IsIrreducibleWithPosLeading f)
    (h_compat : SatisfiesCompatibilityCondition polys) :
    (fun x : ℝ => (CountSimultaneousPrimes polys x : ℝ)) ~[atTop]
    (fun x : ℝ => BatemanHornConstant polys * x / (Real.log x) ^ polys.card) := by
  sorry
