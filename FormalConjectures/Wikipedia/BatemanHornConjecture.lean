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

import FormalConjecturesUtil

/-!
# Bateman-Horn Conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Bateman%E2%80%93Horn_conjecture)
-/

/-
Note: This formalization was one-shot (with minimal cleaning) from Claude 4.0 Sonnet; see:
https://claude.ai/share/a02c2bba-7f5f-435c-ab0e-58eb5ddc0545
-/

open Polynomial Asymptotics Filter Topology

namespace BatemanHornConjecture

/-- `OmegaP S p` counts the number of residue classes mod `p` where at least one polynomial in `S` vanishes. -/
noncomputable def OmegaP (polys : Finset ℤ[X]) (p : ℕ) : ℕ :=
  {n : ZMod p | ∃ f ∈ polys, (f.map (Int.castRingHom (ZMod p))).eval n = 0}.ncard

/-- The product of degrees of polynomials in a finite set. -/
def DegreesProduct (polys : Finset ℤ[X]) : ℕ :=
  polys.prod (fun f => f.natDegree)

/--
The partial Euler product of the Bateman-Horn constant of a set of polynomials `S`, taken over the
primes $p < N$:
$$\prod_{p < N} (1 - \frac{1}{p})^{-|S|} (1 - \frac{\omega_p(S)}{p})$$
where $\omega_p(S)$ is the number of residue classes mod $p$ where at least one polynomial in $S$
vanishes. The Bateman-Horn constant is the limit of these partial products as $N \to \infty$;
the product is only conditionally convergent, so the order of the factors matters.
-/
noncomputable def BatemanHornPartialProduct (polys : Finset ℤ[X]) (N : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesBelow N,
    (1 - (1 : ℝ) / p) ^ (-polys.card : ℤ) * (1 - (OmegaP polys p : ℝ) / p)

/-- `CountSimultaneousPrimes S x` counts the number of `n ≤ x` at which all polynomials in `S` attain a prime value. -/
noncomputable def CountSimultaneousPrimes (polys : Finset ℤ[X]) (x : ℝ) : ℕ :=
  Finset.card (Finset.filter
    (fun n : ℕ => ∀ f ∈ polys, (f.eval ↑n).natAbs.Prime)
    (Finset.range (⌊x⌋₊ + 1)))

/--
**The Bateman-Horn Conjecture**
Given a finite collection of distinct irreducible polynomials non-constant $f_1, f_2, \dots, f_k \in \mathbb{Z}[x]$
with positive leading coefficients that satisfy the Schinzel condition, the number
of positive integers $n \leq x$ for which all polynomials $f_i$ are simultaneously prime is
asymptotic to:
$$\frac{C}{D} \frac{x}{(\log x)^k}$$
where $D = \prod_i \deg(f_i)$ and $C$ is the Bateman-Horn constant given by the convergent
infinite product:
$$C = \prod_{p\in\mathbb{P}} (1 - 1/p)^{-k} (1 - \omega_p/p)$$
Here $\omega_p$ is the number of residue classes modulo $p$ for which at least one polynomial
vanishes. The product is only conditionally convergent: it is the limit as $N \to \infty$ of the
partial products over the primes $p < N$.

The Schinzel condition ensures that for each prime $p$, there exists some integer $n$
such that $p$ does not divide the product $f_1(n) f_2(n) \dotsb f_k(n)$, which guarantees the
infinite product converges to a positive value.
-/
@[category research open, AMS 11 12]
theorem bateman_horn_conjecture
    (polys : Finset ℤ[X])
    (h_nonempty : polys.Nonempty)
    (h_irreducible : ∀ f ∈ polys, BunyakovskyCondition f)
    (h_compat : SchinzelCondition polys) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (BatemanHornPartialProduct polys) atTop (𝓝 C) ∧
      (fun x : ℝ => (CountSimultaneousPrimes polys x : ℝ)) ~[atTop]
        (fun x : ℝ => C / DegreesProduct polys * x / (Real.log x) ^ polys.card) := by
  sorry

end BatemanHornConjecture
