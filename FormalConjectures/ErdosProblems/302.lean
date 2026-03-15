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
# Erdős Problem 302

*Reference:* [erdosproblems.com/302](https://www.erdosproblems.com/302)

Let $f(N)$ be the size of the largest subset of $\{1, \ldots, N\}$ with no solution to
$\frac{1}{a} = \frac{1}{b} + \frac{1}{c}$ among distinct elements. Is $f(N) = (\frac{1}{2} + o(1))N$?

The example $A$ = all odd integers in $[1,N]$ or $A = [\frac{N}{2}, N]$ shows
$f(N) \geq (\frac{1}{2} + o(1))N$. Stijn Cambie improved this to
$f(N) \geq (\frac{5}{8} + o(1))N$. Wouter van Doorn proved
$f(N) \leq (\frac{9}{10} + o(1))N$. Zachary Hunter and Mehtaab Sawhney also
contributed to this problem.

OEIS sequence: [A390395](https://oeis.org/A390395).

Related problems: #301, #303, #327.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).
-/

open Finset

namespace Erdos302

/-- A finset $A$ of positive integers is *unit-fraction-triple-free* if there are
no distinct $a, b, c \in A$ satisfying $\frac{1}{a} = \frac{1}{b} + \frac{1}{c}$. -/
def UnitFractionTripleFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
    a ≠ b → a ≠ c → b ≠ c →
    (1 : ℝ) / (a : ℝ) ≠ (1 : ℝ) / (b : ℝ) + (1 : ℝ) / (c : ℝ)

/--
Erdős Problem 302 [ErGr80]:

Let $f(N)$ be the size of the largest $A \subseteq \{1, \ldots, N\}$ such that there are no
solutions to $\frac{1}{a} = \frac{1}{b} + \frac{1}{c}$ with distinct $a, b, c \in A$.

Is $f(N) = (\frac{1}{2} + o(1))N$?

The example $A$ = all odd integers in $[1,N]$ or $A = [\frac{N}{2}, N]$ shows
$f(N) \geq (\frac{1}{2} + o(1))N$. Stijn Cambie improved this to
$f(N) \geq (\frac{5}{8} + o(1))N$. Wouter van Doorn proved
$f(N) \leq (\frac{9}{10} + o(1))N$.

The upper bound part of the original conjecture $f(N) = (\frac{1}{2} + o(1))N$
has been disproved by Cambie's lower bound. The true asymptotic of $f(N)$ remains
open, with
$\frac{5}{8} \leq \liminf \frac{f(N)}{N} \leq \limsup \frac{f(N)}{N} \leq \frac{9}{10}$.

We formalize the original conjecture as stated: for every $\varepsilon > 0$, for all
sufficiently large $N$,
(1) every unit-fraction-triple-free $A \subseteq \{1,\ldots,N\}$ has
$|A| \leq (\frac{1}{2} + \varepsilon)N$, and
(2) there exists a unit-fraction-triple-free $A \subseteq \{1,\ldots,N\}$ with
$|A| \geq (\frac{1}{2} - \varepsilon)N$.
-/
@[category research solved, AMS 5 11]
theorem erdos_302 : answer(False) ↔
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (∀ (A : Finset ℕ), A ⊆ Finset.Icc 1 N → UnitFractionTripleFree A →
          (A.card : ℝ) ≤ (1 / 2 + ε) * (N : ℝ)) ∧
        (∃ (A : Finset ℕ), A ⊆ Finset.Icc 1 N ∧ UnitFractionTripleFree A ∧
          (A.card : ℝ) ≥ (1 / 2 - ε) * (N : ℝ)) := by
  sorry

/--
Erdős Problem 302 — Lower bound (Cambie):

Stijn Cambie proved $f(N) \geq (\frac{5}{8} + o(1))N$ by taking all odd integers
$\leq N/4$ together with all integers in $[N/2, N]$.
-/
@[category research solved, AMS 5 11]
theorem erdos_302_lower_bound :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ (A : Finset ℕ), A ⊆ Finset.Icc 1 N ∧ UnitFractionTripleFree A ∧
          (A.card : ℝ) ≥ (5 / 8 - ε) * (N : ℝ) := by
  sorry

/--
Erdős Problem 302 — Upper bound (van Doorn):

Wouter van Doorn proved $f(N) \leq (\frac{9}{10} + o(1))N$.
-/
@[category research solved, AMS 5 11]
theorem erdos_302_upper_bound :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (A : Finset ℕ), A ⊆ Finset.Icc 1 N → UnitFractionTripleFree A →
          (A.card : ℝ) ≤ (9 / 10 + ε) * (N : ℝ) := by
  sorry

/--
Erdős Problem 302 — Variant allowing $b = c$:

When $b = c$ is permitted (i.e., $\frac{1}{a} = \frac{2}{b}$), the maximum density
drops to at most $\frac{2}{3}$, since any set with $|A| > (\frac{2}{3} + o(1))N$
must contain some $n$ and $2n$. This variant asks whether the maximum size of a
subset of $\{1, \ldots, N\}$ with no solution to $\frac{1}{a} = \frac{1}{b} + \frac{1}{c}$
(allowing $b = c$) is $(\frac{2}{3} + o(1))N$.
-/
@[category research open, AMS 5 11]
theorem erdos_302_variant_equal_denominators :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (A : Finset ℕ), A ⊆ Finset.Icc 1 N →
          (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
            a ≠ b ∨ a ≠ c →
            (1 : ℝ) / (a : ℝ) ≠ (1 : ℝ) / (b : ℝ) + (1 : ℝ) / (c : ℝ)) →
          (A.card : ℝ) ≤ (2 / 3 + ε) * (N : ℝ) := by
  sorry

end Erdos302
