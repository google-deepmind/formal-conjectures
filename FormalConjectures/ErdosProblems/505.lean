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
# Erdős Problem 505

*Reference:* [erdosproblems.com/505](https://www.erdosproblems.com/505)

**Borsuk's conjecture** (1933): Is every bounded set of diameter 1 in $\mathbb{R}^n$
the union of at most $n + 1$ sets of diameter strictly less than 1?

Erdős [Er44] suspected this is false for sufficiently large $n$. Confirmed
by Kahn–Kalai [KK93], who disproved the conjecture for $n \geq 2015$.
The current best is $n \geq 64$ (Jenrich–Brouwer, 2014).

The conjecture is true for $n \leq 3$ (Eggleston [Eg55] for $n = 3$).

### References

- [Bo33] Borsuk, K. (1933). *Drei Sätze über die n-dimensionale euklidische Sphäre*.
  Fund. Math. 20, 177–190.
- [Er44] Erdős, P. (1944). Remarks on a conjecture of Borsuk.
- [Eg55] Eggleston, H. G. (1955). *Covering a three-dimensional set with sets of
  smaller diameter*. J. London Math. Soc. 30, 11–24.
- [KK93] Kahn, J., Kalai, G. (1993). *A counterexample to Borsuk's conjecture*.
  Bull. Amer. Math. Soc. 29, 60–62.

### AI disclosure

Lean 4 code in this file was drafted with assistance from Claude (Anthropic).
The mathematical content and references are the author's own work.
-/

open Metric Set Classical

namespace Erdos505

@[category test, AMS 52]
theorem erdos_505.test_dim_one
    (S : Set (EuclideanSpace ℝ (Fin 1)))
    (hS : Bornology.IsBounded S) (hd : 0 < diam S) :
    ∃ (F : Fin 2 → Set (EuclideanSpace ℝ (Fin 1))),
      S ⊆ ⋃ i, F i ∧ ∀ i, diam (F i) < diam S := by
  sorry

/-- **Erdős Problem 505** (disproved). Borsuk's conjecture is false for
sufficiently large $n$: there exists a dimension $n$ and a bounded set
$S \subseteq \mathbb{R}^n$ with positive diameter such that $S$ cannot be
covered by $n + 1$ subsets each of diameter strictly less than $\operatorname{diam}(S)$.

Erdős [Er44] suspected this. Disproved by Kahn–Kalai [KK93] for
$n \geq 2015$. Currently known to be false for $n \geq 64$.
A formal proof was formalised by Boris Alexeev using Aristotle. -/
@[category research solved, AMS 52,
  formal_proof using lean4 at
    "https://github.com/plby/lean-proofs/blob/96cd54930d844e3655e6bb89b96b65516397dae9/src/v4.24.0/ErdosProblems/Erdos505.lean#L1153"]
theorem erdos_505 : ∃ (n : ℕ),
    ∃ (S : Set (EuclideanSpace ℝ (Fin n))),
      Bornology.IsBounded S ∧ 0 < diam S ∧
        ∀ (F : Fin (n + 1) → Set (EuclideanSpace ℝ (Fin n))),
          S ⊆ ⋃ i, F i →
          ∃ i, diam S ≤ diam (F i) := by
  sorry

/-- **Borsuk's conjecture, small dimensions** (open / true for $n \leq 3$).
Every bounded set $S \subseteq \mathbb{R}^n$ with $n \leq 3$ can be
covered by $n + 1$ subsets each of strictly smaller diameter.

Trivial for $n \leq 2$; proved for $n = 3$ by Eggleston [Eg55]. -/
@[category research solved, AMS 52]
theorem erdos_505.small_dim (n : ℕ) (hn : n ≤ 3)
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS : Bornology.IsBounded S) (hd : 0 < diam S) :
    ∃ (F : Fin (n + 1) → Set (EuclideanSpace ℝ (Fin n))),
      S ⊆ ⋃ i, F i ∧ ∀ i, diam (F i) < diam S := by
  sorry

end Erdos505
