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
# Erdős Problem 63

*Reference:* [erdosproblems.com/63](https://www.erdosproblems.com/63)

Does every graph with infinite chromatic number contain a cycle of length $2^n$ for
infinitely many $n$? Proved by Liu and Montgomery [LiMo20]. See also Problem #64.

[Er93, p.342] [Er94b] [Er95] [Er95d] [Er96] [Er97b] Various papers by Erdős where this
problem appears.

[ErHa66] Erdős, P. and Hajnal, A., _On chromatic number of graphs and set-systems_.
Acta Math. Acad. Sci. Hungar. **17** (1966), 61–99.

[LiMo20] Liu, H. and Montgomery, R., _A solution to Erdős and Hajnal's odd cycle problem_.
J. Amer. Math. Soc. **36** (2023), 1191–1234.
-/

open SimpleGraph

namespace Erdos63

/--
Erdős Problem 63 (Conjectured by Mihók and Erdős [Er93,Er94b,Er95,Er95d,Er96,Er97b]):
Does every graph with infinite chromatic number contain a cycle of length $2^n$ for
infinitely many $n$? Proved by Liu and Montgomery [LiMo20].

Formalized as: for every graph $G$ with infinite chromatic number, for every bound $N$,
there exists $n \geq N$ such that $G$ contains a cycle of length $2^n$.
-/
@[category research solved, AMS 5]
theorem erdos_63 : answer(True) ↔
    ∀ (V : Type*) (G : SimpleGraph V),
      G.chromaticNumber = ⊤ →
        ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
          ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = 2 ^ n := by
  sorry

/--
Variant of Erdős Problem 63: Can $2^n$ be replaced by $n^2$ (or any sufficiently rapidly
growing sequence)? The website notes that the exponent $2^n$ might be replaceable by other
rapidly growing sequences such as perfect squares.
-/
@[category research open, AMS 5]
theorem erdos_63_variant_squares : answer(sorry) ↔
    ∀ (V : Type*) (G : SimpleGraph V),
      G.chromaticNumber = ⊤ →
        ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
          ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = n ^ 2 := by
  sorry

end Erdos63
