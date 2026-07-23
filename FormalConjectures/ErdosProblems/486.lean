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
# Erdős Problem 486: Logarithmic density for sets avoiding modular subsets

*Reference:* [erdosproblems.com/486](https://www.erdosproblems.com/486)
-/

open Filter
open scoped Topology

namespace Erdos486

/-- The positive integers surviving the delayed congruence system `(A, X)`. A
modulus `n ∈ A` constrains `m` only when `n < m`, matching the "for all `n ∈ A`
with `m > n`" activation in the problem statement. -/
def survivors (A : Set ℕ) (X : (n : A) → Set (ZMod (n : ℕ))) : Set ℕ :=
  {m | 0 < m ∧ ∀ n : A, (n : ℕ) < m → (m : ZMod (n : ℕ)) ∉ X n}

/-- The logarithmic counting sum `∑_{m ∈ B, m < x} 1/m` below a real cutoff. -/
noncomputable def logSum (B : Set ℕ) (x : ℝ) : ℝ := by
  classical
  exact ∑ m ∈ Finset.range ⌈x⌉₊, if m ∈ B ∧ (m : ℝ) < x then (m : ℝ)⁻¹ else 0

/-- The normalized logarithmic average `(1/log x) ∑_{m ∈ B, m < x} 1/m`. -/
noncomputable def logAverage (B : Set ℕ) (x : ℝ) : ℝ := logSum B x / Real.log x

/-- `B` has logarithmic density `d`: the logarithmic average tends to `d`. -/
def HasLogDensity (B : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (logAverage B) atTop (nhds d)

/-- The original yes/no assertion of Erdős Problem 486: for every choice of a
modulus set `A` (with `0 ∉ A`) and residue sets `X_n ⊆ ℤ/nℤ`, the surviving set
has a logarithmic density. -/
def Erdos486Assertion : Prop :=
  ∀ (A : Set ℕ) (X : (n : A) → Set (ZMod (n : ℕ))), 0 ∉ A →
    ∃ d : ℝ, HasLogDensity (survivors A X) d

/--
Let $A\subseteq \mathbb{N}$, and for each $n\in A$ choose some $X_n\subseteq \mathbb{Z}/n\mathbb{Z}$.
Let
$$B = \{ m\in \mathbb{N} : m\not\in X_n \pmod{n}\textrm{ for all }n\in A\textrm{ with }m>n\}.$$
Must $B$ have a logarithmic density?

The answer is **no**: there is a system whose surviving set has no logarithmic
density (the logarithmic average oscillates, with `liminf ≤ 177/200` and
`limsup ≥ 49/50`).

The `m > n` activation is essential: a modulus `n ∈ A` constrains `m` only when
`n < m`. This is captured by `survivors`.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/ShouqiaoW/erdos/blob/f2ae0edb45cbdb257e135d51ef855f64caeb348b/486/lean/Erdos486/Main.lean"]
theorem erdos_486 : answer(False) ↔ Erdos486Assertion := by
  sorry

end Erdos486
