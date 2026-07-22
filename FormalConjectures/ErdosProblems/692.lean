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

import FormalConjecturesUtil

/-!
# Erdős Problem 692

*References:*
- [erdosproblems.com/692](https://www.erdosproblems.com/692)
- [Er79e] Erdős, Paul, Some unconventional problems in number theory. Astérisque (1979), 73-82.
- [Ob1] Erdős, P., *Oberwolfach Mathematical Problems, Volume 1*. Mathematisches
  Forschungsinstitut Oberwolfach (Various).
- [Fo08] Ford, Kevin, *The distribution of integers with a divisor in a given interval*.
  Ann. of Math. (2) (2008), 367-433.
- [Ca25] Cambie, S., *Resolution of Erdős' problems about unimodularity*.
  arXiv:2501.10333 (2025).
-/

namespace Erdos692

open Filter

/--
The set of integers with exactly one divisor in the open interval $(n, m)$.
-/
def exactlyOneDivisorIn (n m : ℕ) : Set ℕ :=
  {x | {d ∈ Set.Ioo n m | d ∣ x}.ncard = 1}

/--
$\delta_1(n,m)$ is the density of the set of integers with exactly one divisor in $(n,m)$.
-/
def IsDelta₁ (n m : ℕ) (δ : ℝ) : Prop :=
  (exactlyOneDivisorIn n m).HasDensity δ

/--
The sequence $f$ is unimodular on $(a, \infty)$ if it increases until some point and
decreases thereafter.
-/
def UnimodularOn (f : ℕ → ℝ) (a : ℕ) : Prop :=
  ∃ M > a, MonotoneOn f (Set.Ioc a M) ∧ AntitoneOn f (Set.Ici M)

/--
Let $\delta_1(n,m)$ be the density of the set of integers with exactly one divisor in $(n,m)$.
Is $\delta_1(n,m)$ unimodular for $m>n+1$ (i.e. increases until some $m$ then decreases
thereafter)?

Cambie has calculated that unimodularity fails even for $n=2$ and $n=3$.
-/
@[category research solved, AMS 11]
theorem erdos_692.parts.i : answer(False) ↔
    ∀ δ : ℕ → ℕ → ℝ, (∀ a b, IsDelta₁ a b (δ a b)) → ∀ n, UnimodularOn (δ n) (n + 1) := by
  sorry

/--
Let $\delta_1(n,m)$ be the density of the set of integers with exactly one divisor in $(n,m)$.
For fixed $n$, where does $\delta_1(n,m)$ achieve its maximum?
-/
@[category research open, AMS 11]
theorem erdos_692.parts.ii (n : ℕ) :
    ∀ δ : ℕ → ℕ → ℝ, (∀ a b, IsDelta₁ a b (δ a b)) →
      IsGreatest (δ n '' Set.Ioi (n + 1)) (δ n answer(sorry)) := by
  sorry

/--
Erdős proved that
\[\delta_1(n,m) \ll \frac{1}{(\log n)^c}\]
for all $m$, for some constant $c>0$.
-/
@[category research solved, AMS 11]
theorem erdos_692.variants.erdos_upper_bound :
    ∀ δ : ℕ → ℕ → ℝ, (∀ a b, IsDelta₁ a b (δ a b)) →
      ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ n in atTop, ∀ m, δ n m ≤ C / Real.log n ^ c := by
  sorry

/--
Cambie has calculated that unimodularity fails even for $n=2$ and $n=3$. For example,
\[\delta_1(3,6)= 0.35\quad \delta_1(3,7)\approx 0.33\quad \delta_1(3,8)\approx 0.3619.\]
-/
@[category research solved, AMS 11]
theorem erdos_692.variants.cambie_three :
    ∀ δ : ℕ → ℕ → ℝ, (∀ a b, IsDelta₁ a b (δ a b)) →
      δ 3 7 < δ 3 6 ∧ δ 3 7 < δ 3 8 := by
  sorry

/--
Cambie [Ca25] has shown that, for fixed $n$, the sequence $\delta_1(n,m)$ has superpolynomially
many local maxima $m$.
-/
@[category research solved, AMS 11]
theorem erdos_692.variants.cambie_local_maxima (k : ℕ) :
    ∀ δ : ℕ → ℕ → ℝ, (∀ a b, IsDelta₁ a b (δ a b)) →
      ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ k ≤
        ({m : ℕ | n + 1 < m ∧ δ n (m - 1) ≤ δ n m ∧ δ n (m + 1) ≤ δ n m}.ncard : ℝ) := by
  sorry

end Erdos692
