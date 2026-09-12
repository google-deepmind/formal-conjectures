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
# Erdős Problem 992

*References:*
- [erdosproblems.com/992](https://www.erdosproblems.com/992)
- [Ba81] Baker, R. C., *Metric number theory and the large sieve*. J. London Math. Soc. (2) (1981),
  34--40.
- [BePh94] Berkes, István and Philipp, Walter, *The size of trigonometric and Walsh series and
  uniform distribution {${\rm mod}\ 1$}*. J. London Math. Soc. (2) (1994), 454--464.
- [Ca50] Cassels, J. W. S., *Some metrical theorems of Diophantine approximation. III*. Proc.
  Cambridge Philos. Soc. (1950), 219--225.
- [ErKo49] Erdős, P. and Koksma, J. F., *On the uniform distribution modulo {$1$} of sequences
  {$(f(n,\theta))$}*. Nederl. Akad. Wetensch., Proc. (1949), 851--854 = Indagationes Math. 11,
  299--302.
-/

open Filter MeasureTheory Real
open scoped Asymptotics

namespace Erdos992

/--
The number of indices $1\leq n\leq N$ for which $\{\alpha x_n\}$ lies in $I$.
-/
noncomputable def intervalCount (x : ℕ → ℕ) (α : ℝ) (N : ℕ) (I : Set ℝ) : ℕ :=
  open scoped Classical in
  ((Finset.Icc 1 N).filter fun n => Int.fract (α * x n) ∈ I).card

/--
The unnormalised discrepancy of the first $N$ points $\{\alpha x_n\}$, taken over closed
subintervals of $[0,1]$.
-/
noncomputable def discrepancy (x : ℕ → ℕ) (α : ℝ) (N : ℕ) : ℝ :=
  sSup { |(intervalCount x α N (Set.Icc a b) : ℝ) - (b - a) * N|
    | (a : ℝ) (b : ℝ) (_ : 0 ≤ a) (_ : a ≤ b) (_ : b ≤ 1) }

/--
Let $x_1<x_2<\cdots$ be an infinite sequence of integers. Is it true that, for almost all
$\alpha \in [0,1]$, the discrepancy
$$D(N)=\max_{I\subseteq [0,1]} \lvert \#\{ n\leq N : \{ \alpha x_n\}\in I\} - \lvert I\rvert N\rvert$$
satisfies
$$D(N) \ll N^{1/2}(\log N)^{o(1)}?$$
Or even
$$D(N)\ll N^{1/2}(\log\log N)^{O(1)}?$$

This was disproved by Berkes and Philipp [BePh94], who constructed a sequence of integers
$x_1<x_2<\cdots$ such that, for almost all $\alpha\in[0,1]$,
$$\limsup_{N\to \infty}\frac{D(N)}{(N\log N)^{1/2}}>0.$$
-/
@[category research solved, AMS 11]
theorem erdos_992 : answer(False) ↔
    ∀ x : ℕ → ℕ, StrictMono x →
      ∀ᵐ α ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        ∃ o : ℕ → ℝ, o =o[atTop] (fun _ : ℕ ↦ (1 : ℝ)) ∧
          (fun N : ℕ ↦ discrepancy x α N) =O[atTop]
            fun N ↦ sqrt N * log N ^ o N := by
  sorry

/--
Or even
$$D(N)\ll N^{1/2}(\log\log N)^{O(1)}?$$

This was disproved by Berkes and Philipp [BePh94], who constructed a sequence of integers
$x_1<x_2<\cdots$ such that, for almost all $\alpha\in[0,1]$,
$$\limsup_{N\to \infty}\frac{D(N)}{(N\log N)^{1/2}}>0.$$
-/
@[category research solved, AMS 11]
theorem erdos_992.variants.loglog : answer(False) ↔
    ∀ x : ℕ → ℕ, StrictMono x →
      ∀ᵐ α ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        ∃ C : ℝ, (fun N : ℕ ↦ discrepancy x α N) =O[atTop]
          fun N ↦ sqrt N * log (log N) ^ C := by
  sorry

/--
Erdős and Koksma [ErKo49] and Cassels [Ca50] independently proved that, for any sequence $x_i$
and almost all $\alpha$, the discrepancy satisfies
$$D(N)\ll N^{1/2}(\log N)^{5/2+o(1)}.$$
-/
@[category research solved, AMS 11]
theorem erdos_992.variants.erdos_koksma_cassels :
    ∀ x : ℕ → ℕ, StrictMono x →
      ∀ᵐ α ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        ∃ o : ℕ → ℝ, o =o[atTop] (fun _ : ℕ ↦ (1 : ℝ)) ∧
          (fun N : ℕ ↦ discrepancy x α N) =O[atTop]
            fun N ↦ sqrt N * log N ^ ((5 : ℝ) / 2 + o N) := by
  sorry

/--
Baker [Ba81] improved this to
$$D(N)\ll N^{1/2}(\log N)^{3/2+o(1)}.$$
-/
@[category research solved, AMS 11]
theorem erdos_992.variants.baker :
    ∀ x : ℕ → ℕ, StrictMono x →
      ∀ᵐ α ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        ∃ o : ℕ → ℝ, o =o[atTop] (fun _ : ℕ ↦ (1 : ℝ)) ∧
          (fun N : ℕ ↦ discrepancy x α N) =O[atTop]
            fun N ↦ sqrt N * log N ^ ((3 : ℝ) / 2 + o N) := by
  sorry

/--
Erdős and Gál (unpublished) proved $D(N) \ll N^{1/2}(\log\log N)^{O(1)}$ for almost all $\alpha$
if the sequence is lacunary - that is, $x_{i+1}/x_i > \lambda>1$ for all $i$.
-/
@[category research solved, AMS 11]
theorem erdos_992.variants.erdos_gal :
    ∀ x : ℕ → ℕ, (∃ lam : ℝ, 1 < lam ∧ ∀ i, lam * (x i : ℝ) < x (i + 1)) →
      ∀ᵐ α ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        ∃ C : ℝ, (fun N : ℕ ↦ discrepancy x α N) =O[atTop]
          fun N ↦ sqrt N * log (log N) ^ C := by
  sorry

/--
This was disproved by Berkes and Philipp [BePh94], who constructed a sequence of integers
$x_1<x_2<\cdots$ such that, for almost all $\alpha\in[0,1]$,
$$\limsup_{N\to \infty}\frac{D(N)}{(N\log N)^{1/2}}>0.$$
-/
@[category research solved, AMS 11]
theorem erdos_992.variants.berkes_philipp :
    ∃ x : ℕ → ℕ, StrictMono x ∧
      ∀ᵐ α ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        ∃ ε > 0, ∃ᶠ N : ℕ in atTop, ε * sqrt (N * log N) < discrepancy x α N := by
  sorry

end Erdos992
