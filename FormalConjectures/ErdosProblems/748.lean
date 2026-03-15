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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 748

*Reference:* [erdosproblems.com/748](https://www.erdosproblems.com/748)

The Cameron-Erdős Conjecture. Let $f(n)$ count the number of sum-free subsets
$A \subseteq \{1, \ldots, n\}$, i.e., $A$ contains no three elements $a$, $b$, $c$ with
$a = b + c$. Is it true that $f(n) = 2^{(1+o(1)) n/2}$?

The lower bound $f(n) \geq 2^{n/2}$ is trivial (consider all subsets of
$\{\lceil n/2 \rceil, \ldots, n\}$).

This was proved independently by Green [Gr04] and Sapozhenko [Sa03], who showed
$f(n) \sim c_n \cdot 2^{n/2}$ where $c_n$ depends on the parity of $n$.

See also Problem 877 (maximal sum-free subsets) and OEIS sequence A007865.

[CaEr90] Cameron, P.J. and Erdős, P.

[Er94b] Erdős, P.

[Er98] Erdős, P.

[Gr04] Green, B., _The Cameron-Erdős conjecture_, Bull. London Math. Soc. 36 (2004), 769-778.

[Sa03] Sapozhenko, A.A., _The Cameron-Erdős conjecture_, Discrete Math. 235 (2003), 131-138.
-/

open Finset

namespace Erdos748

/-- A finite set of natural numbers is *sum-free* if it contains no three
    elements $a$, $b$, $c$ (not necessarily distinct) with $b + c = a$. Equivalently,
    for all $b, c \in A$, we have $b + c \notin A$. -/
def IsSumFree (A : Finset ℕ) : Prop :=
  ∀ b ∈ A, ∀ c ∈ A, b + c ∉ A

instance : DecidablePred IsSumFree :=
  fun A => decidable_of_iff (∀ b ∈ A, ∀ c ∈ A, b + c ∉ A) Iff.rfl

/-- The number of sum-free subsets of $\{1, \ldots, n\}$. -/
noncomputable def sumFreeSubsetCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun A => IsSumFree A)).card

/--
Erdős Problem 748 (Cameron-Erdős Conjecture) [CaEr90][Er94b][Er98]:

Let $f(n)$ count the number of sum-free subsets of $\{1, \ldots, n\}$. Then
$$f(n) = 2^{(1+o(1)) n/2}.$$

Equivalently: for every $\varepsilon > 0$, for all sufficiently large $n$,
$$2^{(1 - \varepsilon) \cdot n/2} \leq f(n) \leq 2^{(1 + \varepsilon) \cdot n/2}.$$

Proved independently by Green [Gr04] and Sapozhenko [Sa03].
-/
@[category research solved, AMS 5 11]
theorem erdos_748 : answer(True) ↔
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (2 : ℝ) ^ ((1 - ε) * (n : ℝ) / 2) ≤ (sumFreeSubsetCount n : ℝ) ∧
      (sumFreeSubsetCount n : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * (n : ℝ) / 2) := by
  sorry

end Erdos748
