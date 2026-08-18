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

end Erdos249
