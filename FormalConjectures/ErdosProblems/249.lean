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
# Erdős Problem 249

*Reference:* [erdosproblems.com/249](https://www.erdosproblems.com/249)
-/

open scoped Nat

namespace Erdos249

/--
Is
$$\sum_{n} \frac{\phi(n)}{2^n}$$
irrational? Here $\phi$ is the Euler totient function.
-/
@[category research open, AMS 11]
theorem erdos_249 : answer(sorry) ↔ Irrational (∑' n : ℕ, (φ n) / (2 ^ n)) := by
  sorry

/--
Split the coefficient sequence $n \mapsto \phi(n)$ into its dyadic channels
$n \mapsto \phi(2^j n + r)$. For every $e \geq 1$ the rational span of the
channels of level at most $e$ has dimension exactly $2^e + 1$.

This is a structural fact about the coefficients of $\sum_n \phi(n)/2^n$; it
does not decide the irrationality asked about in `erdos_249`.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-lean-erdos249-257/blob/92d73cf7a84a1993817020d615b9b046c6ac4b19/adapters/FormalConjecturesVariants.lean#L276-L280"]
theorem erdos_249.variants.dyadic_kernel_rank (e : ℕ) (he : 1 ≤ e) :
    Module.finrank ℚ
        (Submodule.span ℚ (Set.range (Nat.totientKernelThroughLevelFamily e))) =
      2 ^ e + 1 := by
  sorry

/--
The rational span of all dyadic channels $n \mapsto \phi(2^j n + r)$ of the
coefficient sequence of `erdos_249` admits a basis indexed by
`Nat.TotientOddCoreIndex`.

Coons proved that this span is infinite dimensional; the statement here is that
it has an explicit basis on that index. It does not decide the irrationality
asked about in `erdos_249`.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-lean-erdos249-257/blob/92d73cf7a84a1993817020d615b9b046c6ac4b19/adapters/FormalConjecturesVariants.lean#L284-L288"]
theorem erdos_249.variants.odd_core_basis :
    Nonempty
      (Module.Basis Nat.TotientOddCoreIndex ℚ
        (Submodule.span ℚ (Set.range Nat.fullTotientKernelFamily))) := by
  sorry

/--
For every real $r$ with $0 \leq r < 1$, the ordinary generating function of
Euler's totient is the $r$-weighted mass of the lattice points visible from the
origin in the half-open first quadrant:
$$\sum_{\substack{a > 0 \\ \gcd(a,b) = 1}} r^{a+b} = \sum_n \phi(n) r^n.$$

The finite reason is exact. On the antidiagonal $a + b = n$ we have
$\gcd(a, b) = \gcd(a, n)$, so the surviving points are the $a \in [1, n]$ coprime
to $n$ -- precisely $\phi(n)$ of them. The half-open boundary is deliberate:
$(1, 0)$ is what supplies $\phi(1) = 1$, and the empty antidiagonal at $n = 0$
matches $\phi(0) = 0$.

At $r = 1/2$ the right-hand side is the series in `erdos_249`. This is an exact
re-indexing of that constant, not a step towards deciding its irrationality.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-lean-erdos249-257/blob/c04870f7f7f2166f38fc4077033792ef6486f209/Erdos249257/GeometricCoprimality.lean#L120-L151"]
theorem erdos_249.variants.visible_lattice_mass {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0) =
      ∑' n : ℕ, (φ n : ℝ) * r ^ n := by
  sorry

/--
If $\sum_n \phi(n)/2^n$ is rational, its reduced denominator exceeds
$79639646646701375323355774875831053$. Equivalently, the series is not equal
to any rational $p$ with $p.\mathrm{den}$ at most that bound.

This is a machine-checked finite exclusion for the constant in `erdos_249`.
It does not prove irrationality: a rational with a still-larger denominator
is not ruled out.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-lean-erdos249-257/blob/f88e8b686908010a43e9078dda49abbabcfc4079/Erdos249257/CertificateKernel.lean#L18384-L18389"]
theorem erdos_249.variants.denominator_gt_79639646646701375323355774875831053 :
    ∀ p : ℚ, p.den ≤ 79639646646701375323355774875831053 →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (p : ℝ) := by
  sorry

end Erdos249
