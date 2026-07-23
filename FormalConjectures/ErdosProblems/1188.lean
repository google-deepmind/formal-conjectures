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

import FormalConjecturesUtil

/-!
# Erdős Problem 1188

*Reference:* [erdosproblems.com/1188](https://www.erdosproblems.com/1188)
-/

namespace Erdos1188

open Filter
open scoped Classical Topology

/-- A congruence class `(n, a)` represents `a (mod n)`. -/
abbrev CongruenceClass := ℕ × ℕ

/-- The modulus is `> 1` and the residue is reduced. -/
def ValidClass (c : CongruenceClass) : Prop := 2 ≤ c.1 ∧ c.2 < c.1

/-- `z` lies in the class `(n, a)`. -/
def Satisfies (z : ℤ) (c : CongruenceClass) : Prop := z % (c.1 : ℤ) = (c.2 : ℤ)

/-- Every integer satisfies some congruence of `S`. -/
def Covers (S : Finset CongruenceClass) : Prop := ∀ z : ℤ, ∃ c ∈ S, Satisfies z c

/-- No two classes of `S` share a modulus. -/
def HasDistinctModuli (S : Finset CongruenceClass) : Prop :=
  ∀ ⦃c₁⦄, c₁ ∈ S → ∀ ⦃c₂⦄, c₂ ∈ S → c₁.1 = c₂.1 → c₁ = c₂

/-- A minimal distinct covering system: valid classes with distinct moduli that
cover `ℤ`, with no proper subset already covering. -/
def IsMinimalDistinctCoveringSystem (S : Finset CongruenceClass) : Prop :=
  (∀ c ∈ S, ValidClass c) ∧ HasDistinctModuli S ∧ Covers S ∧
    ∀ T : Finset CongruenceClass, T ⊂ S → ¬ Covers T

/-- All classes `(n, a)` with `2 ≤ n ≤ x` and `a < n`. -/
def ClassesUpTo (x : ℕ) : Finset CongruenceClass :=
  (Finset.Icc 2 x).biUnion fun n => (Finset.range n).image fun a => (n, a)

/-- `F(x)`: the number of minimal distinct covering systems all of whose moduli
lie in `[1, x]`. -/
noncomputable def coveringCount (x : ℕ) : ℕ :=
  ((ClassesUpTo x).powerset.filter IsMinimalDistinctCoveringSystem).card

/--
Call a set of distinct integers $1<n_1<\cdots<n_k$ with associated congruence
classes $a_i\pmod{n_i}$ a distinct covering system if every integer satisfies at
least one of these congruences. A minimal distinct covering system is one such
that no proper subset forms a covering system. Let $F(x)$ count the number of
minimal distinct covering systems with all moduli in $[1,x]$. Estimate $F(x)$.

The estimate is `log(log F(x)) / log x → 1`.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/williamjblair/lean-proofs/blob/main/starfleet/erdos-1188/Research/SparseAsymptotic.lean"]
theorem erdos_1188 :
    Tendsto (fun x : ℕ => Real.log (Real.log (coveringCount x : ℝ)) / Real.log (x : ℝ))
      atTop (𝓝 1) := by
  sorry

end Erdos1188
