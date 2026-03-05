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
# Erdős Problem 721

*Reference:* [erdosproblems.com/721](https://www.erdosproblems.com/721)

Erdős asked for reasonable bounds on the van der Waerden number $W(3,k)$, in particular
whether $W(3,k) < \exp(k^c)$ for some $c < 1$, and for non-trivial lower bounds.

[Sc21] Schoen, T. (2021)

[BlSi23] Bloom, T. and Sisask, O. (2023)

[KeMe23] Kelley, Z. and Meka, R. (2023)

[Gr22] Green, B. (2022)

[Hu22] Hunter, Z. (2022)
-/

open Real

namespace Erdos721

/--
An arithmetic progression of length $j$ with first term $a$ and common
difference $d$ lies in $\{0, \ldots, n-1\}$ if $d \geq 1$ and all terms
$a + id$ for $i < j$ are less than $n$.
-/
def APInRange (n a d j : ℕ) : Prop :=
  d ≥ 1 ∧ ∀ i < j, a + i * d < n

/--
A 2-coloring $f : \mathbb{N} \to \text{Bool}$ of $\{0, \ldots, n-1\}$ has a monochromatic
$j$-term arithmetic progression in color $c$.
-/
def HasMonoAP (f : ℕ → Bool) (n j : ℕ) (c : Bool) : Prop :=
  ∃ a d, APInRange n a d j ∧ ∀ i < j, f (a + i * d) = c

/--
`VDWProperty j k n` asserts: every 2-coloring of $\{0, \ldots, n-1\}$ contains
either a monochromatic $j$-AP in one color or a monochromatic $k$-AP in
the other.
-/
def VDWProperty (j k n : ℕ) : Prop :=
  ∀ f : ℕ → Bool, HasMonoAP f n j true ∨ HasMonoAP f n k false

/--
The van der Waerden number $W(j, k)$ is the smallest $n$ such that
`VDWProperty j k n` holds. Defined as the infimum of all such $n$.
Van der Waerden's theorem guarantees this set is nonempty for $j, k \geq 1$.
-/
noncomputable def vanDerWaerden (j k : ℕ) : ℕ :=
  sInf {n : ℕ | VDWProperty j k n}

/--
There exists a constant $c$ with $0 < c < 1$ such that for all sufficiently
large $k$, $W(3, k) < \exp(k^c)$.

This was first proved by Schoen [Sc21]. The best known upper bound is
$W(3, k) \leq \exp(O((\log k)^9))$ due to Bloom-Sisask [BlSi23], improving
on Kelley-Meka [KeMe23].
-/
@[category research solved, AMS 5 11]
theorem erdos_721 :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧
    ∃ N₀ : ℕ, ∀ k : ℕ, k ≥ N₀ →
    (vanDerWaerden 3 k : ℝ) < Real.exp ((k : ℝ) ^ c) := by
  sorry

/--
$W(3, k)$ grows superpolynomially: for every degree $d$,
$W(3, k) > k^d$ for all sufficiently large $k$.

Green [Gr22] proved $W(3,k) \geq \exp(c(\log k)^{4/3}/(\log \log k)^{1/3})$,
improved by Hunter [Hu22] to $W(3,k) \geq \exp(c(\log k)^2/\log \log k)$.
-/
@[category research solved, AMS 5 11]
theorem erdos_721.variants.lower_bound :
    ∀ d : ℕ, ∃ N₀ : ℕ, ∀ k : ℕ, k ≥ N₀ →
    (vanDerWaerden 3 k : ℝ) > (k : ℝ) ^ (d : ℝ) := by
  sorry

end Erdos721
