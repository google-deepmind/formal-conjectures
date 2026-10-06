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
# Erdős Problem 185

*References:*
- [erdosproblems.com/185](https://www.erdosproblems.com/185)
- [Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971)
  (1973), 117-138.
- [FuKa91] Furstenberg, H. and Katznelson, Y., *A density version of the Hales-Jewett Theorem*.
  Journal d'Analyse Mathématique (1991), 64-119.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos185

/-- $f_3(n)$ is the maximal size of a subset of $\{0,1,2\}^n$ which contains no three points on a
line (in $\mathbb{R}^n$). -/
noncomputable def f3 (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ A : Finset (Fin n → Fin 3),
    (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → x ≠ z → y ≠ z →
      ¬ Collinear ℝ ({fun i => ((x i : ℕ) : ℝ), fun i => ((y i : ℕ) : ℝ),
        fun i => ((z i : ℕ) : ℝ)} : Set (Fin n → ℝ))) ∧ A.card = m}

/--
Let $f_3(n)$ be the maximal size of a subset of $\{0,1,2\}^n$ which contains no three points on
a line. Is it true that $f_3(n)=o(3^n)$?

Originally considered by Moser. It is trivial that $f_3(n)\geq R_3(3^n)$, the maximal size of a
subset of $\{1,\ldots,3^n\}$ without a three-term arithmetic progression. Moser showed that
$$f_3(n) \gg \frac{3^n}{\sqrt{n}}.$$

The answer is yes, which is a corollary of the density Hales-Jewett theorem, proved by
Furstenberg and Katznelson [FuKa91].
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos185.lean#L49"]
theorem erdos_185 : answer(True) ↔ (fun n : ℕ => (f3 n : ℝ)) =o[atTop] fun n : ℕ => (3 : ℝ) ^ n := by
  sorry

/-- Moser showed that $f_3(n) \gg \frac{3^n}{\sqrt{n}}$. -/
@[category research solved, AMS 5 11]
theorem erdos_185.variants.moser :
    (fun n : ℕ => (3 : ℝ) ^ n / √n) =O[atTop] fun n : ℕ => (f3 n : ℝ) := by
  sorry

end Erdos185
