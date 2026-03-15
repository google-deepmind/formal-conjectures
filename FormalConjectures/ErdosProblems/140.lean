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
# Erdős Problem 140

*Reference:* [erdosproblems.com/140](https://www.erdosproblems.com/140)

Let $r_3(N)$ denote the size of the largest subset of $\{1, \ldots, N\}$ that contains no
non-trivial $3$-term arithmetic progression. Is it true that $r_3(N) \ll N / (\log N)^C$ for
every $C > 0$?

See also OEIS [A003002](https://oeis.org/A003002).

[ErGr80, p.11] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
number theory*. Monographies de L'Enseignement Mathématique (1980).

[Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*.
Combinatorica (1981), 25-42.

[Er97c] Erdős, P. (1997).

[KeMe23] Kelley, Z. and Meka, R., *Strong Bounds for 3-Progressions*. arXiv:2302.05537 (2023).
-/

open Real Filter

namespace Erdos140

noncomputable abbrev r := Set.IsAPOfLengthFree.maxCard

/--
Erdős Problem 140 [ErGr80, p.11, Er81, Er97c]:
Let $r_3(N)$ be the size of the largest subset of $\{1, \ldots, N\}$ containing no
non-trivial $3$-term arithmetic progression. Then $r_3(N) \ll N / (\log N)^C$
for every $C > 0$.

Formally: for every $C > 0$ there exists a constant $K > 0$ such that
$$r_3(N) \leq K \cdot N / (\log N)^C$$
for all sufficiently large $N$.

Proved by Kelley and Meka [KeMe23].
-/
@[category research solved, AMS 5 11]
theorem erdos_140 :
    ∀ C : ℝ, 0 < C →
    ∃ K : ℝ, 0 < K ∧
    ∀ᶠ N : ℕ in atTop,
      (r 3 N : ℝ) ≤ K * (N : ℝ) / (Real.log (N : ℝ)) ^ C := by
  sorry

/--
Erdős Problem 140 — Kelley–Meka bound [KeMe23]:
There exists an absolute constant $c > 0$ such that
$$r_3(N) \leq N \cdot \exp(-c \cdot (\log N)^{1/12}).$$
This is the quantitative bound actually proved by Kelley and Meka, which implies `erdos_140`.
-/
@[category research solved, AMS 5 11]
theorem erdos_140_kelley_meka :
    ∃ c : ℝ, 0 < c ∧
    ∀ᶠ N : ℕ in atTop,
      (r 3 N : ℝ) ≤ (N : ℝ) * Real.exp (-c * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 12)) := by
  sorry

end Erdos140
