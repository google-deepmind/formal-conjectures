/-
Copyright 2025 The Formal Conjectures Authors.

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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 255

*References:*
- [erdosproblems.com/255](https://www.erdosproblems.com/255)
- [Er61] Erdős, Paul, *Some unsolved problems*. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221-254.
- [Er64b] Erdős, P., *Problems and results on diophantine approximations*. Compositio Math.
  (1964), 52-65.
- [Sc68] Schmidt, Wolfgang M., *Irregularities of distribution*. Quart. J. Math. Oxford Ser. (2)
  (1968), 181-191.
- [Sc72] Schmidt, Wolfgang M., *Irregularities of distribution. VI*. Compositio Math. (1972),
  63-74.
- [TiWa80] Tijdeman, R. and Wagner, G., *A sequence has almost nowhere small discrepancy*.
  Monatsh. Math. (1980), 315-329.
-/

@[expose] public section

namespace Erdos255

/-- The discrepancy $D_N(I) = \#\{ n < N : z_n\in I\} - N\lvert I\rvert$ of the first $N$ terms
of a sequence `z` with respect to the interval $I = [a, b)$. -/
noncomputable def discrepancy (z : ℕ → ℝ) (N : ℕ) (a b : ℝ) : ℝ :=
  ({n ∈ Finset.range N | z n ∈ Set.Ico a b}.card : ℝ) - N * (b - a)

/--
Let $z_1,z_2,\ldots \in [0,1]$ be an infinite sequence, and define the discrepancy
$$D_N(I) = \#\{ n\leq N : z_n\in I\} - N\lvert I\rvert.$$
Must there exist some interval $I\subseteq [0,1]$ such that
$$\limsup_{N\to \infty}\lvert D_N(I)\rvert =\infty?$$

The answer is yes, as proved by Schmidt [Sc68], who later showed [Sc72] that in fact this is
true for all but countably many intervals of the shape $[0,x]$. Essentially the best possible
result was proved by Tijdeman and Wagner [TiWa80], who proved that, for almost all intervals of
the shape $[0,x)$, we have
$$\limsup_{N\to \infty}\frac{\lvert D_N([0,x))\rvert}{\log N}\gg 1.$$

Intervals are taken to be half-open, $I = [a, b)$, and $\limsup_N \lvert D_N(I)\rvert = \infty$
is expressed as unboundedness of $N \mapsto \lvert D_N(I)\rvert$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos255.lean#L98"]
theorem erdos_255 : answer(True) ↔ ∀ z : ℕ → ℝ, (∀ n, z n ∈ Set.Icc 0 1) →
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧
      ¬ BddAbove (Set.range fun N : ℕ => |discrepancy z N a b|) := by
  sorry

/--
Schmidt's theorem [Sc68] in the form proved by Schmidt: the interval can be taken to be of the
shape $[0,x)$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos255.lean#L98"]
theorem erdos_255.variants.anchored (z : ℕ → ℝ) (hz : ∀ n, z n ∈ Set.Icc 0 1) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, ¬ BddAbove (Set.range fun N : ℕ => |discrepancy z N 0 x|) := by
  sorry

/--
Tijdeman and Wagner [TiWa80] proved that, for almost all $x \in [0, 1]$,
$$\limsup_{N\to \infty}\frac{\lvert D_N([0,x))\rvert}{\log N}\gg 1.$$
-/
@[category research solved, AMS 11]
theorem erdos_255.variants.tijdeman_wagner : ∃ c : ℝ, 0 < c ∧ ∀ z : ℕ → ℝ,
    (∀ n, z n ∈ Set.Icc 0 1) →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)),
        ∃ᶠ N : ℕ in Filter.atTop, c * Real.log N ≤ |discrepancy z N 0 x| := by
  sorry

end Erdos255
