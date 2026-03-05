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
# Erdős Problem 8

*Reference:* [erdosproblems.com/8](https://www.erdosproblems.com/8)

The original Erdős–Graham conjecture asked: for any finite colouring of the positive integers,
must there exist a covering system all of whose moduli are monochromatic?

The answer is **no**, as a consequence of Hough's theorem [Ho15] that every covering system
must contain a modulus below an absolute bound (at most $10^{16}$, later improved to $616000$
by Balister, Bollobás, Morris, Sahasrabudhe, and Tiba [BBMST22]). One can therefore assign a
distinct colour to each integer up to this bound and a single fresh colour to all larger integers;
any covering system must then contain a small modulus with a unique colour, making
monochromaticity impossible.

[Ho15] Hough, R. D., _The interval of covering congruences_. Ann. of Math. (2) **181** (2015),
no. 1, 361–382.

[BBMST22] Balister, P., Bollobás, B., Morris, R., Sahasrabudhe, J., and Tiba, M.,
_The Erdős covering problem: the density of the uncovered set_. Ann. of Math. (2) **198** (2023),
no. 1, 1–92.
-/

namespace Erdos8

/--
A finite system of congruences $\{(a_i, m_i)\}$ is a **covering system** if every
modulus is positive and every integer satisfies at least one congruence $n \equiv a_i \pmod{m_i}$.
-/
def IsCoveringSystem (S : Finset (ℤ × ℕ)) : Prop :=
  S.Nonempty ∧
  (∀ p ∈ S, 0 < p.2) ∧
  (∀ n : ℤ, ∃ p ∈ S, (p.2 : ℤ) ∣ (n - p.1))

/--
All moduli in a covering system are **monochromatic** under a colouring $\chi : \mathbb{N} \to \text{Fin}\, k$
if there exists a colour $c$ such that every modulus in $S$ receives colour $c$.
-/
def HasMonochromaticModuli {k : ℕ} (χ : ℕ → Fin k) (S : Finset (ℤ × ℕ)) : Prop :=
  ∃ c : Fin k, ∀ p ∈ S, χ p.2 = c

/--
The Erdős–Graham conjecture asked: for any finite colouring of the positive integers,
must there exist a covering system all of whose moduli are monochromatic?

The answer is **no**, as a consequence of Hough's theorem [Ho15] that every covering system
must contain a modulus below an absolute bound.
-/
@[category research solved, AMS 5 11]
theorem erdos_8 : answer(False) ↔
    (∀ k : ℕ, 0 < k → ∀ χ : ℕ → Fin k,
      ∃ S : Finset (ℤ × ℕ), IsCoveringSystem S ∧ HasMonochromaticModuli χ S) := by
  sorry

end Erdos8
