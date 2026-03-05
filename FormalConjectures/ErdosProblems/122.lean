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
# Erdős Problem 122

*Reference:* [erdosproblems.com/122](https://www.erdosproblems.com/122)

For which arithmetic functions $f$ is it true that the count of $n$ with $n + f(n)$ in a
short interval $(x, x + F(x))$, divided by $F(x)$, is unbounded? Erdős–Pomerance–Sárközy
proved this for $f = \tau$ (divisor count) and $f = \omega$ (distinct prime factor count).

[Er97] Erdős, P., *Some of my new and almost new problems and results in combinatorial
number theory* (1997).

[Er97e] Erdős, P., *Some problems and results on combinatorial number theory* (1997).

[EPS97] Erdős, P., Pomerance, C., and Sárközy, A., *On locally repeated values of certain
arithmetic functions, III* (1997).
-/

open scoped Classical

open Filter

namespace Erdos122

/-- The count of natural numbers $n$ such that $n + f(n)$ falls in the open real
interval $(x, x + F(x))$. Since $n \le n + f(n) < x + F(x)$ requires $n < x + F(x)$,
it suffices to search $n$ in the range $[0, x + \lceil F(x) \rceil]$. -/
noncomputable def shiftCount (f : ℕ → ℕ) (F : ℕ → ℝ) (x : ℕ) : ℕ :=
  ((Finset.range (x + ⌈F x⌉₊ + 1)).filter
    (fun (n : ℕ) => (x : ℝ) < (n : ℝ) + (f n : ℝ) ∧
              (n : ℝ) + (f n : ℝ) < (x : ℝ) + F x)).card

/-- The natural density of a set $A \subseteq \mathbb{N}$ is zero: the proportion of elements
in $\{0, \ldots, N-1\}$ belonging to $A$ tends to $0$ as $N \to \infty$. -/
def HasNaturalDensityZero (A : Set ℕ) : Prop :=
  Tendsto
    (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ))
    atTop (nhds 0)

/-- $f(n)/F(n) \to 0$ for almost all $n$ in the natural-density sense:
for every $\varepsilon > 0$, the set $\{n : f(n)/F(n) \ge \varepsilon\}$ has natural
density zero. -/
def AlmostAllRatioVanishes (f : ℕ → ℕ) (F : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → HasNaturalDensityZero {n : ℕ | ε ≤ (f n : ℝ) / F n}

/-- The Erdős-122 property of $f$: for any positive $F$ with $f(n)/F(n) \to 0$
in natural density, the ratio $\#\{n \in \mathbb{N} : n+f(n) \in (x, x+F(x))\} / F(x)$
is unbounded as $x \to \infty$ (equivalently, its limsup equals $+\infty$). -/
def HasErdos122Property (f : ℕ → ℕ) : Prop :=
  ∀ F : ℕ → ℝ, (∀ n, 0 < F n) → AlmostAllRatioVanishes f F →
    ∀ C : ℝ, ∃ᶠ x : ℕ in atTop, C < (shiftCount f F x : ℝ) / F x

/--
Erdős Problem #122 [Er97, Er97e, EPS97]

For which number-theoretic functions $f : \mathbb{N} \to \mathbb{N}$ is it true that for any
positive function $F : \mathbb{N} \to \mathbb{R}$ satisfying $f(n)/F(n) \to 0$ for almost all $n$
(in the natural density sense), there are infinitely many $x$ for which
$$\#\{n \in \mathbb{N} : n + f(n) \in (x, x + F(x))\} / F(x) \to \infty?$$

Erdős, Pomerance, and Sárközy [EPS97] proved that this holds when:
- $f(n) = \tau(n)$ = number of divisors of $n$, and
- $f(n) = \omega(n)$ = number of distinct prime divisors of $n$.

Erdős believed the property to be FALSE for:
- $f(n) = \varphi(n)$ (Euler's totient function), and
- $f(n) = \sigma(n)$ (sum of divisors).

The full characterization of which $f$ satisfy `HasErdos122Property` remains open.
The theorem below records the two proved instances.
-/
@[category research solved, AMS 11]
theorem erdos_122 :
    HasErdos122Property (fun n => (Nat.divisors n).card) ∧
    HasErdos122Property (fun n => (Nat.primeFactorsList n).toFinset.card) := by
  sorry

end Erdos122
