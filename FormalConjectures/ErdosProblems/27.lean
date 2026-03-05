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
# Erdős Problem 27

*Reference:* [erdosproblems.com/27](https://www.erdosproblems.com/27)

An $\varepsilon$-almost covering system is a set of congruences $a_i \pmod{n_i}$ for distinct
moduli $n_1 < \cdots < n_k$ such that the natural density of integers satisfying none of them
is at most $\varepsilon$.

Erdős asked whether there exists a constant $C > 1$ such that for every $\varepsilon > 0$ and
$N \geq 1$, there is an $\varepsilon$-almost covering system with $N \leq n_1 < \cdots < n_k \leq CN$.
This was disproved by Filaseta, Ford, Konyagin, Pomerance, and Yu [FFKPY07].

[FFKPY07] Filaseta, M., Ford, K., Konyagin, S., Pomerance, C., and Yu, G.,
_Sieving by large integers and covering systems of congruences_.
Journal of the American Mathematical Society (2007), 495-517.
-/

open Finset

open scoped Classical

namespace Erdos27

/-- A congruence system has distinct moduli if no two pairs share the same modulus. -/
def HasDistinctModuli (S : Finset (ℤ × ℕ)) : Prop :=
  S.card = (S.image Prod.snd).card

/-- The LCM of all moduli in a congruence system. -/
noncomputable def systemLcm (S : Finset (ℤ × ℕ)) : ℕ :=
  (S.image Prod.snd).lcm id

/--
The density of uncovered integers for a congruence system, measured as the proportion of
integers in $\{0, \ldots, L-1\}$ not covered by any congruence, where $L$ is the LCM of
all moduli.
-/
noncomputable def uncoveredDensity (S : Finset (ℤ × ℕ)) : ℝ :=
  let L := systemLcm S
  ((Finset.range L).filter (fun x =>
    ∀ p ∈ S, ¬((↑p.2 : ℤ) ∣ (↑x - p.1)))).card / (L : ℝ)

/--
There is no constant $C > 1$ such that for every $\varepsilon > 0$ and $N \geq 1$, there
exists an $\varepsilon$-almost covering system whose moduli all lie in the interval $[N, CN]$.

Erdős conjectured this was possible; it was disproved by Filaseta, Ford, Konyagin,
Pomerance, and Yu [FFKPY07].
-/
@[category research solved, AMS 11]
theorem erdos_27 :
    answer(False) ↔
    ∃ C : ℝ, C > 1 ∧
      ∀ ε : ℝ, ε > 0 →
      ∀ N : ℕ, N ≥ 1 →
      ∃ S : Finset (ℤ × ℕ),
        HasDistinctModuli S ∧
        S.Nonempty ∧
        (∀ p ∈ S, p.2 ≥ 2) ∧
        (∀ p ∈ S, N ≤ p.2 ∧ (p.2 : ℝ) ≤ C * N) ∧
        uncoveredDensity S ≤ ε := by
  sorry

end Erdos27
