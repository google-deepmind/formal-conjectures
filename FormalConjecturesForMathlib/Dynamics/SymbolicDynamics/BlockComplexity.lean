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

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Data.EReal.Inv
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Data.Set.Card
public import Mathlib.Order.LiminfLimsup

/-!
# Block complexity and entropy of a sequence

The block complexity $p(n, a)$ of a sequence $a$ is the number of distinct blocks of $n$
consecutive terms of $a$. The entropy of $a$ is the exponential growth rate of $p(n, a)$.

*References:*
- [AS03] Allouche, Jean-Paul, and Jeffrey Shallit. "Automatic sequences: theory, applications,
  generalizations." Cambridge University Press, 2003. Chapter 10.
- [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
  Vol. 193. Cambridge University Press, 2012. Chapter 10.

## Main definitions

* `SymbolicDynamics.blockComplexity`: the number of distinct blocks of length `n` of a sequence.
* `SymbolicDynamics.blockEntropy`: the entropy of a sequence.
-/

@[expose] public section

open Filter

open scoped ENNReal

namespace SymbolicDynamics

/--
The block complexity $p(n, a)$ of a sequence $a$, that is, the number of distinct blocks
$a_k a_{k+1} \cdots a_{k+n-1}$ of $n$ consecutive terms of $a$. It is `⊤` when $n \ge 1$ and
$a$ takes infinitely many values.
-/
noncomputable def blockComplexity {α : Type*} (a : ℕ → α) (n : ℕ) : ℝ≥0∞ :=
  {w : Fin n → α | ∃ k, ∀ i, w i = a (k + i)}.encard

/--
The entropy of a sequence $a$,
$$E(a) = \lim_{n \to \infty} \frac{\log p(n, a)}{n}.$$
The limit exists because $n \mapsto \log p(n, a)$ is subadditive, so it agrees with the `limsup`
used here. The value is `⊤` exactly when $a$ takes infinitely many values.
-/
noncomputable def blockEntropy {α : Type*} (a : ℕ → α) : EReal :=
  limsup (fun n : ℕ ↦ (blockComplexity a n).log / (n : EReal)) atTop

/-- A constant sequence has exactly one block of each length. -/
theorem blockComplexity_const {α : Type*} (c : α) (n : ℕ) :
    blockComplexity (fun _ ↦ c) n = 1 := by
  have h : {w : Fin n → α | ∃ k : ℕ, ∀ i, w i = (fun _ : ℕ ↦ c) (k + (i : ℕ))}
      = {fun _ ↦ c} := by
    ext w
    simp [funext_iff]
  simp only [blockComplexity, h, Set.encard_singleton, ENat.toENNReal_one]

/-- A constant sequence has zero entropy. -/
theorem blockEntropy_const {α : Type*} (c : α) : blockEntropy (fun _ ↦ c) = 0 := by
  simp [blockEntropy, blockComplexity_const]

end SymbolicDynamics
