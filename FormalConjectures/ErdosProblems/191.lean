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
# Erdős Problem 191

*References:*
- [erdosproblems.com/191](https://www.erdosproblems.com/191)
- [ErGr79] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics*. Enseign. Math. (1979), 325-344.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*.
  Combinatorica (1981), 25-42.
- [Er82e] Erdős, Paul, *Some of my favourite problems which recently have been solved*. (1982),
  59--79.
- [Ro03] Rödl, Vojtěch, *On homogeneous sets of positive integers*. J. Combin. Theory Ser. A
  (2003), 229-240.
- [CFS13] Conlon, David and Fox, Jacob and Sudakov, Benny, *Two extensions of Ramsey's theorem*.
  Duke Math. J. (2013), 2903-2927.
-/

@[expose] public section

open Filter

namespace Erdos191

/--
Let $C>0$ be arbitrary. Is it true that, if $n$ is sufficiently large depending on $C$, then in
any $2$-colouring of $\binom{\{2,\ldots,n\}}{2}$ there exists some $X\subseteq \{2,\ldots,n\}$
such that $\binom{X}{2}$ is monochromatic and
$$\sum_{x\in X}\frac{1}{\log x}\geq C?$$

The answer is yes, which was proved by Rödl [Ro03]. In the same article Rödl also proved a lower
bound for this problem, constructing, for all $n$, a $2$-colouring of $\binom{\{2,\ldots,n\}}{2}$
such that if $X\subseteq \{2,\ldots,n\}$ is such that $\binom{X}{2}$ is monochromatic then
$$\sum_{x\in X}\frac{1}{\log x}\ll \log\log\log n.$$
In the same paper Rödl proves that the answer to the main problem is negative if we consider
$3$-colourings.

This bound is best possible, as proved by Conlon, Fox, and Sudakov [CFS13], who proved that, if
$n$ is sufficiently large, then in any $2$-colouring of $\binom{\{2,\ldots,n\}}{2}$ there exists
some $X\subseteq \{2,\ldots,n\}$ such that $\binom{X}{2}$ is monochromatic and
$$\sum_{x\in X}\frac{1}{\log x}\geq 2^{-8}\log\log\log n.$$

A $2$-colouring of the pairs of $\{2,\ldots,n\}$ is a graph `G` on this vertex set; a
monochromatic set is a clique or an independent set of `G`.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos191.lean#L1272"]
theorem erdos_191 : answer(True) ↔ ∀ C : ℝ, 0 < C → ∀ᶠ n : ℕ in atTop,
    ∀ G : SimpleGraph (Finset.Icc 2 n), ∃ X : Finset (Finset.Icc 2 n),
      (G.IsClique X ∨ G.IsIndepSet X) ∧ C ≤ ∑ x ∈ X, 1 / Real.log (x : ℕ) := by
  sorry

/--
Conlon, Fox, and Sudakov [CFS13] proved that, if $n$ is sufficiently large, then in any
$2$-colouring of $\binom{\{2,\ldots,n\}}{2}$ there exists some $X\subseteq \{2,\ldots,n\}$ such
that $\binom{X}{2}$ is monochromatic and
$$\sum_{x\in X}\frac{1}{\log x}\geq 2^{-8}\log\log\log n.$$
-/
@[category research solved, AMS 5]
theorem erdos_191.variants.conlon_fox_sudakov : ∀ᶠ n : ℕ in atTop,
    ∀ G : SimpleGraph (Finset.Icc 2 n), ∃ X : Finset (Finset.Icc 2 n),
      (G.IsClique X ∨ G.IsIndepSet X) ∧
        2 ^ (-8 : ℤ) * Real.log (Real.log (Real.log n)) ≤ ∑ x ∈ X, 1 / Real.log (x : ℕ) := by
  sorry

/--
Rödl [Ro03] constructed, for all $n$, a $2$-colouring of $\binom{\{2,\ldots,n\}}{2}$ such that
if $X\subseteq \{2,\ldots,n\}$ is such that $\binom{X}{2}$ is monochromatic then
$$\sum_{x\in X}\frac{1}{\log x}\ll \log\log\log n.$$
-/
@[category research solved, AMS 5]
theorem erdos_191.variants.rodl_upper : ∃ c : ℝ, ∀ᶠ n : ℕ in atTop,
    ∃ G : SimpleGraph (Finset.Icc 2 n), ∀ X : Finset (Finset.Icc 2 n),
      G.IsClique X ∨ G.IsIndepSet X →
        ∑ x ∈ X, 1 / Real.log (x : ℕ) ≤ c * Real.log (Real.log (Real.log n)) := by
  sorry

/--
Rödl [Ro03] proved that the answer to [erdős_191](https://www.erdosproblems.com/191) is negative
if we consider $3$-colourings: there is a constant $C$ such that for every $n$ some $3$-colouring
of $\binom{\{2,\ldots,n\}}{2}$ has $\sum_{x\in X}\frac{1}{\log x} < C$ for every monochromatic
$X$.
-/
@[category research solved, AMS 5]
theorem erdos_191.variants.three_colours : ∃ C : ℝ, ∀ n : ℕ,
    ∃ c : Sym2 (Finset.Icc 2 n) → Fin 3, ∀ X : Finset (Finset.Icc 2 n),
      (∃ i : Fin 3, ∀ x ∈ X, ∀ y ∈ X, x ≠ y → c s(x, y) = i) →
        ∑ x ∈ X, 1 / Real.log (x : ℕ) < C := by
  sorry

end Erdos191
