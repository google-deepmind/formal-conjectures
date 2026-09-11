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
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

/-!
# Multiplicatively independent integers

Two integers $p, q \ge 2$ are *multiplicatively independent* if $\log p / \log q$ is
irrational, equivalently if $p^m = q^n$ holds only for $m = n = 0$. The condition separates
bases whose expansions carry unrelated information, as in Cobham's theorem and in
Furstenberg's $\times p$, $\times q$ problems.

## Main definitions

* `Nat.MultiplicativelyIndependent`: the relation itself.
-/

namespace Nat

/--
Two integers $p, q \ge 2$ are *multiplicatively independent* if $\log p / \log q$ is
irrational, equivalently if $p^m = q^n$ holds only for $m = n = 0$.
-/
def MultiplicativelyIndependent (p q : ℕ) : Prop := Irrational (Real.log p / Real.log q)

/-- Multiplicative independence is symmetric. -/
theorem MultiplicativelyIndependent.symm {p q : ℕ} (h : MultiplicativelyIndependent p q) :
    MultiplicativelyIndependent q p := by
  rw [MultiplicativelyIndependent, ← inv_div]
  exact Irrational.inv h

end Nat
