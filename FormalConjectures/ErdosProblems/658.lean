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
# Erdős Problem 658

*References:*
- [erdosproblems.com/658](https://www.erdosproblems.com/658)
- [Er97e] Erdős, Paul, *Some of my favourite unsolved problems*. Math. Japon. (1997), 527-537.
- [FuKa91] Furstenberg, H. and Katznelson, Y., *A density version of the Hales-Jewett Theorem*.
  Journal d'Analyse Mathématique (1991), 64-119.
- [So04] Solymosi, J., *A Note on a Question of Erdős and Graham*. Combinatorics, Probability and
  Computing (2004), 263–267.
-/

@[expose] public section

open Filter

namespace Erdos658

/--
Let $\delta>0$ and $N$ be sufficiently large depending on $\delta$. Is it true that if
$A\subseteq \{1,\ldots,N\}^2$ has $\lvert A\rvert \geq \delta N^2$ then $A$ must contain the
vertices of a square?

A problem of Graham, if the square is restricted to be axis-aligned. (It is unclear whether in
[Er97e] had this restriction in mind.)

This qualitative statement follows from the density Hales-Jewett theorem proved by Furstenberg
and Katznelson [FuKa91]. A quantitative proof (yet with very poor bounds) was given by Solymosi
[So04].

The square is taken to be axis-aligned (Graham's version), which implies the version allowing
arbitrary squares.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos658.lean#L1516"]
theorem erdos_658 : answer(True) ↔ ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop,
    ∀ A : Finset (ℕ × ℕ), A ⊆ Finset.Icc 1 N ×ˢ Finset.Icc 1 N → δ * N ^ 2 ≤ A.card →
      ∃ a b d : ℕ, 0 < d ∧ (a, b) ∈ A ∧ (a + d, b) ∈ A ∧ (a, b + d) ∈ A ∧ (a + d, b + d) ∈ A := by
  sorry

end Erdos658
