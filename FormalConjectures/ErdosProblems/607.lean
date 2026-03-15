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
# Erdős Problem 607

*Reference:* [erdosproblems.com/607](https://www.erdosproblems.com/607)

Erdős asked for an upper bound on the number of distinct line spectra achievable by
$n$-point configurations in $\mathbb{R}^2$. Szemerédi and Trotter proved it is at most
$\exp(C\sqrt{n})$ for some constant $C > 0$. Erdős noted that this bound is best possible,
i.e., the exponential order $\exp(\Theta(\sqrt{n}))$ is tight.

[Er85] Erdős, P., *Problems and results in combinatorial geometry*.

[SzTr83] Szemerédi, E. and Trotter, W. T., Jr., *Extremal problems in discrete geometry*.
Combinatorica (1983), 381-392.
-/

namespace Erdos607

open scoped Classical

/-- Three points in $\mathbb{R}^2$ are collinear: the cross product of the displacement
    vectors $(q - p)$ and $(r - p)$ vanishes. -/
noncomputable def Collinear607 (p q r : ℝ × ℝ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (r.1 - p.1) * (q.2 - p.2)

/-- Given a finite point set $P$ and two points $p, q$, the number of points in $P$
    lying on the line through $p$ and $q$. -/
noncomputable def lineIncidence607 (P : Finset (ℝ × ℝ)) (p q : ℝ × ℝ) : ℕ :=
  (P.filter (fun r => Collinear607 p q r)).card

/-- The line spectrum of a finite point set $P \subset \mathbb{R}^2$: the set of all distinct
    values $|\ell \cap P|$ as $\ell$ ranges over lines determined by $P$ (lines through at
    least two points of $P$). -/
noncomputable def lineSpectrum607 (P : Finset (ℝ × ℝ)) : Finset ℕ :=
  P.biUnion fun p =>
    (P.filter fun q => p ≠ q).image fun q => lineIncidence607 P p q

/-- The set of achievable line spectra for $n$-point configurations in $\mathbb{R}^2$. -/
noncomputable def achievableSpectra607 (n : ℕ) : Set (Finset ℕ) :=
  {S | ∃ P : Finset (ℝ × ℝ), P.card = n ∧ lineSpectrum607 P = S}

/--
**Erdős Problem 607** [Er85]:

There exists a constant $C > 0$ such that for all sufficiently large $n$, the number
$F(n)$ of distinct line spectra achievable by $n$-point configurations in $\mathbb{R}^2$
satisfies $F(n) \leq \exp(C \cdot \sqrt{n})$.

Proved by Szemerédi and Trotter [SzTr83].
-/
@[category research solved, AMS 5 52]
theorem erdos_607 :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (achievableSpectra607 n).Finite ∧
      ((achievableSpectra607 n).ncard : ℝ) ≤ Real.exp (C * Real.sqrt (n : ℝ)) := by
  sorry

/--
**Erdős Problem 607 (lower bound)** [Er85]:

There exists a constant $c > 0$ such that for infinitely many $n$, the number
$F(n)$ of distinct line spectra achievable by $n$-point configurations in $\mathbb{R}^2$
satisfies $F(n) \geq \exp(c \cdot \sqrt{n})$.

Erdős noted that this lower bound is "easy to see," confirming that the
$\exp(\Theta(\sqrt{n}))$ growth rate is tight.
-/
@[category research solved, AMS 5 52]
theorem erdos_607_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ n₀ : ℕ, ∃ n : ℕ, n₀ ≤ n ∧
      (achievableSpectra607 n).Finite ∧
      Real.exp (c * Real.sqrt (n : ℝ)) ≤ ((achievableSpectra607 n).ncard : ℝ) := by
  sorry

end Erdos607
