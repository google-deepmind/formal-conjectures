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
# Erdős Problem 286

*References:*
- [erdosproblems.com/286](https://www.erdosproblems.com/286)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Cr01] Croot, III, Ernest S., *On unit fractions with denominators in short intervals*. Acta
  Arith. (2001), 99-114.
-/

@[expose] public section

open Filter Real

namespace Erdos286

/--
Let $k\geq 2$. Is it true that there exists an interval $I$ of width $(e-1+o(1))k$ and integers
$n_1<\cdots<n_k\in I$ such that
$$1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}?$$

The answer is yes, proved by Croot [Cr01].
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos286.lean#L163"]
theorem erdos_286 : answer(True) ↔ ∃ o : ℕ → ℝ, Tendsto o atTop (nhds 0) ∧
    ∀ᶠ k : ℕ in atTop, ∃ a b : ℝ, b - a = (exp 1 - 1 + o k) * k ∧
      ∃ S : Finset ℕ, S.card = k ∧ 0 ∉ S ∧ ∑ n ∈ S, (1 : ℝ) / n = 1 ∧
        ∀ n ∈ S, (n : ℝ) ∈ Set.Icc a b := by
  sorry

end Erdos286
