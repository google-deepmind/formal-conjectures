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
Let `f` assign rational values to residues modulo `2^k`, where `k ≥ 1`.
The binary series with coefficients `f (φ(n) mod 2^k)` is rational exactly
when `f` has the same value on every even residue class. This is a solved
variant; the series with unreduced totients above remains open.

*Source:* [Cook, Bases and Integral Relations for the $k$-Kernel of Euler's Totient, "Residue series and dyadic observables"](https://github.com/wcook04/plectis-erdos/blob/c4bff4aa152465b3c92fffe808f76b0e5f78293c/paper/249/erdos-249-binary-totient-series.tex#L297-L306).
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-erdos/blob/c4bff4aa152465b3c92fffe808f76b0e5f78293c/lean/ErdosProblems/Erdos249/PaperCompleteR7/RationalObservableClassification.lean#L221-L233"]
theorem erdos_249.variants.rational_dyadic_observable
    {k : ℕ} (hk : 1 ≤ k) (f : ZMod (2 ^ k) → ℚ) :
    (∃ q : ℚ,
      (∑' n : ℕ, (f (Nat.totient (n + 1) : ZMod (2 ^ k)) : ℝ) /
        2 ^ (n + 1)) = (q : ℝ)) ↔
      ∀ r : ℕ, r < 2 ^ k → r % 2 = 0 → f (r : ZMod (2 ^ k)) = f 0 := by
  sorry

end Erdos249
