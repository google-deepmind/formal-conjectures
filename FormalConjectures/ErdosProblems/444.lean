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

public import FormalConjecturesUtil

/-!
# Erdős Problem 444

*References:*
- [erdosproblems.com/444](https://www.erdosproblems.com/444)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [ErSa80] Erdős, P. and Sárközy, A., *Some asymptotic formulas on generalized divisor functions.
  IV*. Studia Sci. Math. Hungar. (1980), 467-479.
-/

@[expose] public section

open Filter Finset

namespace Erdos444

open scoped Classical in
/-- $d_A(n)$ is the number of $a \in A$ which divide $n$. Only the positive divisors of $n$ are
counted, so $0 \in A$ does not change $d_A(n)$ for $n \ge 1$. -/
noncomputable def divisorCount (A : Set ℕ) (n : ℕ) : ℕ :=
  #{a ∈ n.divisors | a ∈ A}

@[category test, AMS 11]
theorem divisorCount_zero (A : Set ℕ) : divisorCount A 0 = 0 := by
  simp [divisorCount]

@[category test, AMS 11]
theorem divisorCount_zero_two_three_four_twelve : divisorCount {0, 2, 3, 4} 12 = 3 := by
  simp [divisorCount, show Nat.divisors 12 = {1, 2, 3, 4, 6, 12} by decide, filter_insert]

open scoped Classical in
/--
Let $A\subseteq\mathbb{N}$ be infinite and $d_A(n)$ count the number of $a\in A$ which divide $n$.
Is it true that, for every $k$,
$$\limsup_{x\to \infty} \frac{\max_{n<x}d_A(n)}{\left(\sum_{n\in A\cap[1,x)}\frac{1}{n}\right)^k}
=\infty?$$

This is asked in [ErGr80, p.88]. The answer is yes, proved by Erdős and Sárközy [ErSa80].

The maximum is over $1 \le n < x$, since every $a \in A$ divides $0$.
-/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos444.lean#L38"]
theorem erdos_444 : ∀ A : Set ℕ, A.Infinite → ∀ k : ℕ,
    atTop.limsup (fun x : ℝ ↦ (((Ico 1 ⌈x⌉₊).sup (divisorCount A) /
      (∑ n ∈ Ico 1 ⌈x⌉₊ with n ∈ A, (n : ℝ)⁻¹) ^ k : ℝ) : EReal)) = ⊤ := by
  sorry

end Erdos444
