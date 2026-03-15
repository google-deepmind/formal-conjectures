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
# Erdős Problem 498

*Reference:* [erdosproblems.com/498](https://www.erdosproblems.com/498)

Given complex numbers $z_1, \ldots, z_n$ with $|z_i| \geq 1$, the number of sign patterns
$\varepsilon \in \{-1,1\}^n$ for which the signed sum $\sum \varepsilon_i z_i$ lands in any unit
disc is at most $\binom{n}{\lfloor n/2 \rfloor}$.

See also: Problem 395 (reverse Littlewood–Offord problem).

[Er45] Erdős, P., _On a lemma of Littlewood and Offord_. Bull. Amer. Math. Soc. **51** (1945),
898–902.

[Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. **6** (1961),
221–254.

[Kl65] Kleitman, D., _On a lemma of Littlewood and Offord on the distributions of linear
combinations of vectors_. Advances in Math. **1** (1965), 155–157.

[Kl70] Kleitman, D., _On a lemma of Littlewood and Offord on the distribution of certain sums_.
Math. Z. **90** (1970), 251–259.
-/

open Finset
open scoped BigOperators

namespace Erdos498

/-- The signed sum of complex numbers $z$ with signs $\varepsilon \in \{-1, 1\}^n$ (encoded as
`Bool`). -/
noncomputable def signedSum {n : ℕ} (z : Fin n → ℂ) (ε : Fin n → Bool) : ℂ :=
  ∑ i : Fin n, (if ε i then (1 : ℂ) else (-1 : ℂ)) * z i

/--
Erdős Problem 498 (Littlewood–Offord problem, proved by Kleitman [Kl65]):

Let $z_1, \ldots, z_n \in \mathbb{C}$ with $|z_i| \geq 1$ for all $i$. For any disc of radius $1$
centered at $w \in \mathbb{C}$, the number of sign patterns $\varepsilon \in \{-1, 1\}^n$ such that
$\varepsilon_1 z_1 + \cdots + \varepsilon_n z_n$ lies in the disc (i.e.,
$\|\sum \varepsilon_i z_i - w\| \leq 1$) is at most $\binom{n}{\lfloor n/2 \rfloor}$.

Erdős [Er45] proved the real case. Kleitman [Kl65] proved the full complex case and later
generalised the result to arbitrary Hilbert spaces [Kl70].
-/
@[category research solved, AMS 5]
theorem erdos_498 (n : ℕ) (z : Fin n → ℂ) (w : ℂ)
    (hz : ∀ i, 1 ≤ ‖z i‖) :
    (Finset.univ.filter (fun ε : Fin n → Bool =>
      ‖signedSum z ε - w‖ ≤ 1)).card ≤ n.choose (n / 2) := by
  sorry

end Erdos498
