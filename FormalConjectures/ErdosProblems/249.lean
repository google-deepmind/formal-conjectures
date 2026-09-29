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

public import FormalConjecturesUtil

/-!
# Erdős Problem 249

*Reference:* [erdosproblems.com/249](https://www.erdosproblems.com/249)
-/

@[expose] public section

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
For every modulus $m \ge 3$ and integer base $B \ge 2$, the numbers
$$
1,\qquad \sum_{n \ge 1}\frac{\phi(n) \bmod m}{B^{dn}}\quad(d \ge 1)
$$
are linearly independent over $\mathbb{Q}$.

This solved variant concerns bounded least-residue coefficients. The irrationality
of the unreduced totient series in `erdos_249` remains open.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-erdos-lean/blob/d85765c9ead139e1c562c93e675ad92616923f6b/Solutions/ExternalVerification249CountableDilationIndependence.lean#L12-L19"]
theorem erdos_249.variants.least_residue_dilation_independence
    (m B : ℕ) (hm : 3 ≤ m) (hB : 2 ≤ B) :
    LinearIndependent ℚ (fun d : ℕ =>
      if d = 0 then (1 : ℝ) else
        ∑' n : ℕ, ((Nat.totient (n + 1) % m : ℕ) : ℝ) /
          ((B ^ d : ℕ) : ℝ) ^ (n + 1)) := by
  sorry

end Erdos249
