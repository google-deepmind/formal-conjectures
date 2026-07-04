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
# Erdős Problem 31

*References:*
- [erdosproblems.com/31](https://www.erdosproblems.com/31)
- [Er56] Erdős, P., *Problems and results in additive number theory*. Colloque sur la Théorie des
  Nombres, Bruxelles, 1955 (1956), 127-137.
- [Er59] Erdős, P., *Über einige Probleme der additiven Zahlentheorie*. Sammelband zu Ehren des 250.
  Geburtstages Leonhard Eulers (1959), 116-119.
- [Er65b] Erdős, Paul, *Some recent advances and current problems in number theory*. Lectures on
  Modern Mathematics, Vol. III (1965), 196-244.
- [Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of combinatorial
  theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971) (1973), 117-138.
- [Lo54] Lorentz, G. G., *On a problem of additive number theory*. Proc. Amer. Math. Soc.
  (1954), 838-841.
-/

namespace Erdos31

open Filter
open scoped Pointwise

/--
Given any infinite set $A\subset \mathbb{N}$ there is a set $B$ of density $0$ such that $A+B$ contains all except finitely many integers.

Conjectured by Erdős and Straus. Proved by Lorentz [Lo54].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos31.lean"]
theorem erdos_31 : ∀ A : Set ℕ, A.Infinite →
    ∃ B : Set ℕ, B.HasDensity 0 ∧ ∀ᶠ n in atTop, n ∈ A + B := by
  sorry

end Erdos31
