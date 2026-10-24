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
/-
Adapted definitions; original work by Shouqiao Wang.
MIT License

Copyright (c) 2026 Shouqiao Wang

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 788

*References:*
- [erdosproblems.com/788](https://www.erdosproblems.com/788)
- Shouqiao Wang, [A Proposed Solution to Erdős Problem 788](https://github.com/ShouqiaoW/erdos/blob/f2ae0ed/788/paper.tex).
- [Lean 4.33.0 proof](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos788.lean)
-/

@[expose] public section

namespace Erdos788

def I (n : ℕ) : Finset ℕ :=
  Finset.Ioo n (2 * n)

def J (n : ℕ) : Finset ℕ :=
  Finset.Ioo (2 * n) (4 * n)

def Admissible (n : ℕ) (B C : Finset ℕ) : Prop :=
  C ⊆ I n ∧
    ∀ ⦃c⦄, c ∈ C → ∀ ⦃c'⦄, c' ∈ C → c ≠ c' → c + c' ∉ B

def Guarantees (n t : ℕ) : Prop :=
  ∀ B : Finset ℕ, B ⊆ J n →
    ∃ C : Finset ℕ, Admissible n B C ∧ t ≤ B.card + C.card

def scoreBound (n : ℕ) : ℕ :=
  (J n).card + (I n).card

noncomputable def fNat (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (Guarantees n) (scoreBound n)

noncomputable def f (n : ℕ) : ℤ :=
  (fNat n : ℤ)

/-- Let $f(n)$ be maximal such that if $B\subset (2n,4n)\cap \mathbb{N}$ there
exists some $C\subset (n,2n)\cap \mathbb{N}$ such that $c_1+c_2\not\in B$ for all
$c_1\neq c_2\in C$ and $\lvert C\rvert+\lvert B\rvert \geq f(n)$.
Estimate $f(n)$. In particular is it true that $f(n)\leq n^{1/2+o(1)}$?

The linked formal proof establishes the stronger two-sided exponent statement.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos788.lean"]
theorem erdos_788 :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      (n : ℝ) ^ ((1 / 2 : ℝ) - ε) ≤ (f n : ℝ) ∧
        (f n : ℝ) ≤ (n : ℝ) ^ ((1 / 2 : ℝ) + ε) := by sorry

/-- Wang's quantitative bounds imply the exponent $1/2$ for all sufficiently large $n$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos788.lean"]
theorem erdos_788.variants.quantitative :
    (∀ n : ℕ, 3 ≤ n →
      (1 / 2000 : ℝ) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ (f n : ℝ)) ∧
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      (f n : ℝ) ≤ (n : ℝ) ^ ((1 / 2 : ℝ) + C *
        (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) ^ (1 / 3 : ℝ)) := by sorry

end Erdos788

