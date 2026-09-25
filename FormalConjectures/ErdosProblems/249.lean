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
For every modulus $m \ge 3$, the series of least nonnegative residues
$\sum_{n \ge 1} (\phi(n) \bmod m)/2^n$ is irrational. The fixed base is $2$;
the claim does not settle the series with unreduced coefficients above.
The series equals $0$ for $m=1$ and $3/4$ for $m=2$.
For $m=0$, Lean's remainder leaves each coefficient unchanged, giving the open
series above.

*Source:* [Bases and Integral Relations for the $k$-Kernel of Euler's Totient, Bounded residues and rationality](https://github.com/wcook04/plectis-erdos/blob/a14777b3219873bc8343205cca0bb3bb6530e8fa/paper/249/erdos-249-binary-totient-series.tex#L292-L306).
Erick Wong's [2015 answer](https://math.stackexchange.com/a/1211557) proves the
antecedent with the base equal to the modulus; here the base stays $2$.
Yazdani's [2001 Corollary 4](https://www.numdam.org/article/JTNB_2001__13_2_651_0.pdf)
proves nonautomaticity of these residues in every integer base; this alone
does not establish irrationality of their fixed-base-$2$ sum.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-erdos/blob/7204d156d8d9433d4a7470aaddc59219f414305e/research/adapters/FormalConjecturesVariants.lean#L114-L118"]
theorem erdos_249.variants.residue_modulus_binary :
    ∀ m : ℕ, 3 ≤ m →
      Irrational (∑' n : ℕ, ((Nat.totient n % m : ℕ) : ℝ) / 2 ^ n) := by
  sorry

end Erdos249
