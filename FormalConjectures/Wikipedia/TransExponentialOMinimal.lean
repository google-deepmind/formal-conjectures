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
# O-minimal expansions of the real field and exponential boundedness

An expansion of the real ordered field $\bar{\mathbb{R}} = (\mathbb{R}, \le, +, \cdot)$ is
*exponentially bounded* if every definable function $f : \mathbb{R} \to \mathbb{R}$ satisfies
$f(t) = O(\exp_N(t))$ as $t \to +\infty$ for some compositional iterate $\exp_N$ of $\exp$.
All known o-minimal expansions of $\bar{\mathbb{R}}$ are exponentially bounded, and van den
Dries and Miller write that they do not know whether there are o-minimal structures on
$(\mathbb{R}, +, \cdot)$ that are not exponentially bounded. Wikipedia's list of unsolved
problems states the question in the form "Does there exist an o-minimal first order theory with a
trans-exponential (rapid growth) function?", where a function is *trans-exponential* if it
eventually exceeds every iterate of $\exp$; the list does not name the underlying field. We follow
the literature and formalise both forms for expansions of $\bar{\mathbb{R}}$.

Definable means definable with parameters. Expansions of $\bar{\mathbb{R}}$ are formalised as
structures on `ℝ` in a language `L` containing the order symbol `≤` and the image of the
language of rings under a language map `φ : Language.ring →ᴸ L`, such that the symbols are
interpreted in the standard way. Since $\le$ is definable from $+$ and $\cdot$, requiring it in
the language loses no generality. The languages range over arbitrary universes.

*References:*
- [Wikipedia, *List of unsolved problems in mathematics*](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Model_theory_and_formal_languages).
- L. van den Dries, C. Miller, *Geometric categories and o-minimal structures*, Duke Math. J.
  84 (1996), 497–540. See the remark following 5.5.
- C. Miller, *Exponentiation is hard to avoid*, Proc. Amer. Math. Soc. 122 (1994), 257–259
  (the growth dichotomy).
- C. Miller, S. Starchenko, [*Status of the o-minimal two-group question*](https://people.math.osu.edu/miller.1987/tg.pdf),
  note, 2003.
- Y. Fu, [*Towards trans-exponential o-minimal expansion of $(\mathbb{R}, +, \cdot, 0, 1, <)$*](https://arxiv.org/abs/2604.03477),
  arXiv:2604.03477.
- A. J. Wilkie, *Model completeness results for expansions of the ordered field of real numbers
  by restricted Pfaffian functions and the exponential function*, J. Amer. Math. Soc. 9 (1996),
  1051–1094.
-/

namespace TransExponentialOMinimal

open FirstOrder FirstOrder.Language Filter

universe u v

/--
**Tarski–Seidenberg.** The real ordered field $\bar{\mathbb{R}}$ is o-minimal: its definable
sets are the semialgebraic sets, and a semialgebraic subset of $\mathbb{R}$ is a finite union of
points and open intervals.
-/
@[category research solved, AMS 3 14]
theorem isOMinimal_real_orderedField : (Language.ring.sum Language.order).IsOMinimal ℝ := by
  sorry

/--
**Wilkie's theorem.** The real exponential field
$\mathbb{R}_{\exp} = (\mathbb{R}, +, \cdot, -, 0, 1, \le, \exp)$ is o-minimal.
-/
@[category research solved, AMS 3 12]
theorem isOMinimal_realExp : Language.orderedExpField.IsOMinimal ℝ := by
  sorry

/--
Is every o-minimal expansion of the real ordered field $\bar{\mathbb{R}}$ exponentially bounded?
That is, given an o-minimal expansion of $\bar{\mathbb{R}}$ and a definable function
$f : \mathbb{R} \to \mathbb{R}$, is there a compositional iterate $\exp_N$ of $\exp$ with
$f(t) = O(\exp_N(t))$ as $t \to +\infty$?
-/
@[category research open, AMS 3 26]
theorem oMinimal_expansion_isExponentiallyBounded :
    answer(sorry) ↔ ∀ (L : FirstOrder.Language.{u, v}) [L.Structure ℝ] [L.IsOrdered]
      (φ : Language.ring →ᴸ L) [φ.IsExpansionOn ℝ] [L.IsOMinimal ℝ],
      L.IsExponentiallyBounded := by
  sorry

/--
Does there exist an o-minimal expansion of the real ordered field $\bar{\mathbb{R}}$ with a
definable trans-exponential function, i.e. a definable $f : \mathbb{R} \to \mathbb{R}$ such that
for every $N$ we have $f(t) > \exp_N(t)$ for all sufficiently large $t$?

This is the form of the question in Wikipedia's list. By Miller's growth dichotomy, an o-minimal
expansion of $\bar{\mathbb{R}}$ that is not polynomially bounded defines $\exp$, and then by
o-minimality it is not exponentially bounded if and only if it defines a trans-exponential
function.
-/
@[category research open, AMS 3 26]
theorem exists_oMinimal_expansion_transExponential :
    answer(sorry) ↔ ∃ (L : FirstOrder.Language.{u, v}) (_ : L.Structure ℝ) (_ : L.IsOrdered)
      (φ : Language.ring →ᴸ L) (_ : φ.IsExpansionOn ℝ) (_ : L.IsOMinimal ℝ) (f : ℝ → ℝ),
      (Set.univ : Set ℝ).Definable₂ L f.graph ∧ ∀ N : ℕ, ∀ᶠ x in atTop, Real.exp^[N] x < f x := by
  sorry

end TransExponentialOMinimal
