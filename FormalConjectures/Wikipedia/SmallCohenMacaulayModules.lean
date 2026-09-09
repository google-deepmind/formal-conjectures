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
# The small Cohen-Macaulay modules conjecture

Let $(R, \mathfrak m)$ be a Noetherian local ring of Krull dimension $d$. A *system of
parameters* of $R$ is a sequence $x_1, \dots, x_d$ of $d$ elements of $R$ with
$\sqrt{(x_1, \dots, x_d)} = \mathfrak m$, equivalently with $R / (x_1, \dots, x_d)$ Artinian.

A *small Cohen-Macaulay module*, also called a maximal Cohen-Macaulay module, is a finitely
generated $R$-module $M \ne 0$ such that some system of parameters of $R$ is a regular sequence
on $M$. A *balanced big Cohen-Macaulay module* is a module $W$, not necessarily finitely
generated, with $\mathfrak m W \ne W$ and on which every system of parameters is a regular
sequence. For finitely generated modules the two notions agree.

**Small Cohen-Macaulay modules conjecture.** If $R$ is complete, then $R$ has a small
Cohen-Macaulay module.

Hochster conjectured this for complete local domains in the early 1970s. In the 2000s he
conjectured the opposite, that there are complete local domains with no small Cohen-Macaulay
module [Ho17]. Small Cohen-Macaulay modules are known to exist when $\dim R \le 2$, and when $R$
is $\mathbb N$-graded over a perfect field of characteristic $p$ with an isolated
non-Cohen-Macaulay point at the origin, a case first observed by Hartshorne and rediscovered by
Peskine and Szpiro [Ho75b]. In dimension at least three the conjecture is open in every
characteristic, although classes of examples keep being found there, such as three-dimensional
$F$-pure complete local $\mathbb F_p$-algebras, due to Schoutens, and three-dimensional
completions of $\mathbb N$-graded rings over a field of characteristic $p$, due to Hochster; both
are listed, with references, in [ST23]. The analogous statement for
algebras is false: Bhatt constructed complete local normal domains of characteristic $p$
admitting no module-finite extension ring that is Cohen-Macaulay [Bh14].

Balanced big Cohen-Macaulay modules, by contrast, are now known to exist over every Noetherian
local ring, by Hochster in equal characteristic and by André in mixed characteristic.

Systems of parameters and Cohen-Macaulay modules are defined in
`FormalConjecturesForMathlib.RingTheory.SystemOfParameters` and
`FormalConjecturesForMathlib.RingTheory.CohenMacaulayModule`.

*References:*
- [Wikipedia, Homological conjectures in commutative
  algebra](https://en.wikipedia.org/wiki/Homological_conjectures_in_commutative_algebra),
  conjectures 8 and 14.
- [Ho75a] M. Hochster, *Topics in the homological theory of modules over commutative rings*,
  C.B.M.S. Regional Conf. Ser. in Math. 24, Amer. Math. Soc., 1975.
- [Ho75b] M. Hochster, *Big Cohen-Macaulay modules and algebras and embeddability in rings of
  Witt vectors*, Queen's Papers in Pure and Applied Math. 42, 1975, 106-195.
- [Ho17] M. Hochster, *Homological conjectures and lim Cohen-Macaulay sequences*, in Homological
  and Computational Methods in Commutative Algebra, Springer INdAM Ser. 20, Springer, 2017.
  [PDF](https://sites.lsa.umich.edu/hochster/wp-content/uploads/sites/1337/2024/08/DSlim2.pdf),
  Conjectures 2.1 and 2.2.
- [An18] Y. André, *La conjecture du facteur direct*, Publ. Math. IHÉS 127 (2018), 71-93.
  [arXiv:1609.00345](https://arxiv.org/abs/1609.00345). This is the paper [Ho17] credits with the
  existence of big Cohen-Macaulay algebras; it rests on the perfectoid Abhyankar lemma of
  *Le lemme d'Abhyankar perfectoïde*, Publ. Math. IHÉS 127 (2018), 1-70.
- [Stacks, Tag 00N6](https://stacks.math.columbia.edu/tag/00N6), on regular sequences in a
  Cohen-Macaulay module.
- [ST23] K. Shimomoto, E. Tavanfar, *Remarks on the Small Cohen-Macaulay conjecture and new
  instances of maximal Cohen-Macaulay modules*, J. Algebra 634 (2023), 667-697.
  [arXiv:2203.10368](https://arxiv.org/abs/2203.10368)
- [Bh14] B. Bhatt, *On the non-existence of small Cohen-Macaulay algebras*, J. Algebra 411
  (2014), 1-11. [arXiv:1207.5413](https://arxiv.org/abs/1207.5413)
-/

open IsLocalRing Module

namespace SmallCohenMacaulayModules

universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable (M : Type*) [AddCommGroup M] [Module R M]

omit [IsNoetherianRing R] in
/--
Over a local ring of Krull dimension zero, the small Cohen-Macaulay modules are exactly the
nonzero finitely generated modules.
-/
@[category test, AMS 13]
theorem isSmallCohenMacaulay_iff_of_krullDimLE_zero [Ring.KrullDimLE 0 R] :
    IsSmallCohenMacaulay R M ↔ Module.Finite R M ∧ Nontrivial M := by
  refine ⟨fun h => ⟨h.finite, h.nontrivial⟩, fun h => ⟨h.1, [], isSystemOfParameters_nil R, ?_⟩⟩
  have := h.2
  exact RingTheory.Sequence.IsRegular.nil R M

/--
**The small Cohen-Macaulay modules conjecture.** If $R$ is a complete Noetherian local ring, then
there is a finitely generated $R$-module $M \ne 0$ such that some system of parameters of $R$ is
a regular sequence on $M$.

Hochster stated the conjecture for complete local domains [Ho17, Conjecture 2.1]. The two forms
are equivalent: for a minimal prime $P$ of $R$ with $\dim R/P = \dim R$, a small Cohen-Macaulay
module over the complete local domain $R/P$ is one over $R$. In the 2000s Hochster conjectured
the opposite, that some complete local domain has no small Cohen-Macaulay module
[Ho17, Conjecture 2.2], so this statement may well be false.
-/
@[category research open, AMS 13]
theorem exists_isSmallCohenMacaulay [IsAdicComplete (maximalIdeal R) R] :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module R M), IsSmallCohenMacaulay R M := by
  sorry

/--
The conjecture holds in dimension at most $2$. For a complete local domain the integral closure
is a small Cohen-Macaulay module [Ho17]; the general case follows by passing to $R/P$ for a
minimal prime $P$ with $\dim R/P = \dim R$.
-/
@[category research solved, AMS 13]
theorem exists_isSmallCohenMacaulay.variants.ringKrullDim_le_two
    [IsAdicComplete (maximalIdeal R) R] (hR : ringKrullDim R ≤ 2) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module R M), IsSmallCohenMacaulay R M := by
  sorry

/--
A finitely generated module is a balanced big Cohen-Macaulay module if and only if it is a small
Cohen-Macaulay module [Ho17]. In particular, if one system of parameters is a regular sequence on
a finitely generated nonzero module, then every system of parameters is; this is the
"some (equivalently every)" of the Wikipedia statement. Its main ingredient is
[Stacks, Tag 00N6], applied to a system of parameters of $R$ once $M$ is known to be
Cohen-Macaulay.
-/
@[category textbook, AMS 13]
theorem isBalancedBigCohenMacaulay_iff_isSmallCohenMacaulay [Module.Finite R M] :
    IsBalancedBigCohenMacaulay R M ↔ IsSmallCohenMacaulay R M := by
  sorry

/--
**Existence of balanced big Cohen-Macaulay modules.** Every Noetherian local ring has a balanced
big Cohen-Macaulay module: conjecture 8 of the Wikipedia list, and Theorem CMM of [Ho17]. Proved
by Hochster in equal characteristic [Ho75a], and, using perfectoid methods, by André in mixed
characteristic [An18].
-/
@[category research solved, AMS 13]
theorem exists_isBalancedBigCohenMacaulay :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module R W), IsBalancedBigCohenMacaulay R W := by
  sorry

end SmallCohenMacaulayModules
