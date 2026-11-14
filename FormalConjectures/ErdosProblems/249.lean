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

open scoped Nat BigOperators

namespace Erdos249

/--
Is
$$\sum_{n} \frac{\phi(n)}{2^n}$$
irrational? Here $\phi$ is the Euler totient function.
-/
@[category research open, question, AMS 11]
theorem erdos_249 : Irrational (∑' n : ℕ, (φ n) / (2 ^ n)) := by
  sorry

/--
Let $B\ge 2$ be an integer, let $D\subset\mathbb{N}_{>0}$ be finite, and let
$q_0\in\mathbb{Q}$. For each $d\in D$, let $k_d\ge1$ be an integer and let
$f_d:\mathbb{Z}/2^{k_d}\mathbb{Z}\to\mathbb{Q}$. Then
$$
q_0+\sum_{d\in D}\sum_{n\ge1}
  \frac{f_d(\varphi(n)\bmod 2^{k_d})}{B^{dn}}\in\mathbb{Q}
\quad\Longleftrightarrow\quad
\forall d\in D\;\forall r\in\{0,\ldots,2^{k_d}-1\},\quad
  2\mid r\;\Longrightarrow\; f_d(r)=f_d(0).
$$
Here $\varphi$ is Euler's totient function.

[Cook, Proposition 11(b)](https://github.com/wcook04/plectis-erdos/blob/6db987f4a843ae40ab07ac782ef0cca1a95815c1/paper/249/erdos249-totient-reasoning-surface.tex#L578-L598).
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/wcook04/plectis-erdos-lean/blob/2cd19fba5298bc4d8ca9fd469962b18ecfbbca31/verification/FC249MixedModuliCurrent/FC249MixedModuliSolution.lean#L7-L19"]
theorem erdos_249.variants.rational_mixed_dyadic_observables
    (D : Finset ℕ) (k : ℕ → ℕ)
    (f : (d : ℕ) → ZMod (2 ^ (k d)) → ℚ) (B : ℕ) (q₀ : ℚ)
    (hB : 2 ≤ B)
    (hpos : ∀ d ∈ D, 0 < d)
    (hk : ∀ d ∈ D, 0 < k d) :
    (∃ q : ℚ, (q₀ : ℝ) + (∑ d ∈ D, ∑' n : ℕ,
      (f d (Nat.totient (n + 1) : ZMod (2 ^ (k d))) : ℝ) /
        ((B : ℝ) ^ d) ^ (n + 1)) = (q : ℝ)) ↔
      ∀ d ∈ D, ∀ r : ℕ, r < 2 ^ (k d) → Even r →
        f d (r : ZMod (2 ^ (k d))) = f d 0 := by
  sorry

end Erdos249
