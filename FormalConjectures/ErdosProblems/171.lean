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
# Erdős Problem 171

*References:*
- [erdosproblems.com/171](https://www.erdosproblems.com/171)
- [ErGr79] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics*. Enseign. Math. (1979), 325-344.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [FuKa91] Furstenberg, H. and Katznelson, Y., *A density version of the Hales-Jewett Theorem*.
  Journal d'Analyse Mathématique (1991), 64-119.
- [Po12] Polymath, D. H. J., *A new proof of the density Hales–Jewett theorem*. Ann. Math.
  (2012), 1283-1327.
-/

@[expose] public section

open Filter

namespace Erdos171

/--
Is it true that for every $\epsilon>0$ and integer $t\geq 1$, if $N$ is sufficiently large and
$A$ is a subset of $[t]^N$ of size at least $\epsilon t^N$ then $A$ must contain a combinatorial
line $P$ (a set $P=\{p_1,\ldots,p_t\}$ where for each coordinate $1\leq j\leq t$ the $j$th
coordinate of $p_i$ is either $i$ or constant).

The 'density Hales-Jewett' problem. This was proved by Furstenberg and Katznelson [FuKa91]. A
new elementary proof, which gives quantitative bounds, was proved by the Polymath project
[Po12].

Combinatorial lines are Mathlib's `Combinatorics.Line (Fin t) (Fin N)` (which have at least one
non-constant coordinate).
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos171.lean#L42"]
theorem erdos_171 : answer(True) ↔ ∀ ε : ℝ, 0 < ε → ∀ t : ℕ, 1 ≤ t → ∀ᶠ N : ℕ in atTop,
    ∀ A : Finset (Fin N → Fin t), ε * t ^ N ≤ A.card →
      ∃ l : Combinatorics.Line (Fin t) (Fin N), ∀ i : Fin t, l i ∈ A := by
  sorry

end Erdos171
