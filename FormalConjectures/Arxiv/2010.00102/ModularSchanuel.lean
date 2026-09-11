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
# Modular Schanuel conjecture

The modular Schanuel conjecture is the analogue of Schanuel's conjecture for the modular
$j$-function $j : \mathbb{H} \to \mathbb{C}$. A point $z \in \mathbb{H}$ is a *CM point* (or
*special point*) if it satisfies a non-trivial quadratic equation with integer coefficients. The
group $\mathrm{GL}_2^+(\mathbb{Q})$ of rational matrices with positive determinant acts on
$\mathbb{H}$ by Möbius transformations, and $j(z)$, $j(gz)$ are related by a modular polynomial
whenever $g \in \mathrm{GL}_2^+(\mathbb{Q})$.

The conjecture states that if $z_1, \dots, z_n \in \mathbb{H}$ are not CM points and lie in distinct
$\mathrm{GL}_2^+(\mathbb{Q})$-orbits, then
$$\operatorname{tr.deg.}_{\mathbb{Q}}
  \mathbb{Q}(z_1, \dots, z_n, j(z_1), \dots, j(z_n)) \ge n.$$
The version with derivatives states that under the same hypotheses
$$\operatorname{tr.deg.}_{\mathbb{Q}}
  \mathbb{Q}(z_i, j(z_i), j'(z_i), j''(z_i) : 1 \le i \le n) \ge 3n.$$
Higher derivatives add nothing, since $j'''$ is algebraic over $\mathbb{Q}(j, j', j'')$.

Both statements follow from the generalised period conjecture of Grothendieck–André, via
Bertolin's *conjecture modulaire*. The case $n = 1$ without derivatives is Schneider's theorem.

The reference states both conjectures for arbitrary $z_1, \dots, z_n \in \mathbb{H}$, with $n$
replaced by the number of $\mathrm{GL}_2^+(\mathbb{Q})$-orbits of non-CM points among the $z_i$.
That form is equivalent to the one stated here. Under the hypotheses below the number of such
orbits is $n$; conversely, the general form follows by applying the statement below to one
representative of each orbit of non-CM points, since adjoining further generators cannot lower
the transcendence degree. Neither reduction is formalised.

*Reference:* [arxiv/2010.00102](https://arxiv.org/abs/2010.00102)
**A closure operator respecting the modular $j$-function**
by *Vahagn Aslanyan, Sebastian Eterović, Jonathan Kirby*, Israel J. Math. 253 (2023), 321–357,
§6.3: Conjecture 6.16 (MSC, without derivatives) and Conjecture 6.14 (MSCD, with derivatives).

*Further references:*
- [J. Pila, *Functional transcendence via o-minimality*, in *O-minimality and Diophantine
  geometry*, LMS Lecture Note Ser. 421 (2015), 66–99, Conjectures 8.4 and
  8.3](https://doi.org/10.1017/CBO9781316106839.004)
- [C. Bertolin, *Périodes de 1-motifs et transcendance*, J. Number Theory 97 (2002),
  204–221](https://doi.org/10.1016/S0022-314X(02)00002-1)
- [J. Pila, J. Tsimerman, *Ax–Schanuel for the $j$-function*, Duke Math. J. 165 (2016),
  2587–2605](https://doi.org/10.1215/00127094-3620005)
  ([arXiv](https://arxiv.org/abs/1412.8255))
-/

open IntermediateField UpperHalfPlane ModularForm
open scoped MatrixGroups

namespace Arxiv.«2010.00102»

/--
**Modular Schanuel conjecture.** Let $z_1, \dots, z_n \in \mathbb{H}$ be points that are not CM
points, lying in distinct $\mathrm{GL}_2^+(\mathbb{Q})$-orbits. Then
$$\operatorname{tr.deg.}_{\mathbb{Q}} \mathbb{Q}(z_1, \dots, z_n, j(z_1), \dots, j(z_n)) \ge n.$$
This is Conjecture 6.16 (MSC) of the reference.
-/
@[category research open, AMS 11]
theorem modular_schanuel_conjecture (n : ℕ) (z : Fin n → ℍ) (hz : ∀ i, ¬ IsCMPoint (z i))
    (hz' : Pairwise fun i k ↦ ¬ IsGLPosRatEquiv (z i) (z k)) :
    n ≤ Algebra.trdeg ℚ (adjoin ℚ (Set.range (fun i ↦ (z i : ℂ)) ∪ Set.range (j ∘ z))) := by
  sorry

/--
**Modular Schanuel conjecture with derivatives.** Let $z_1, \dots, z_n \in \mathbb{H}$ be points
that are not CM points, lying in distinct $\mathrm{GL}_2^+(\mathbb{Q})$-orbits. Then
$$\operatorname{tr.deg.}_{\mathbb{Q}}
  \mathbb{Q}(z_1, \dots, z_n, j(z_1), \dots, j(z_n), j'(z_1), \dots, j'(z_n),
  j''(z_1), \dots, j''(z_n)) \ge 3n.$$
Here $j'$ and $j''$ are the first and second complex derivatives of $j$, computed by extending
$j$ to $\mathbb{C}$ via `UpperHalfPlane.ofComplex`. This is Conjecture 6.14 (MSCD) of the
reference.
-/
@[category research open, AMS 11]
theorem modular_schanuel_conjecture_with_derivatives (n : ℕ) (z : Fin n → ℍ)
    (hz : ∀ i, ¬ IsCMPoint (z i)) (hz' : Pairwise fun i k ↦ ¬ IsGLPosRatEquiv (z i) (z k)) :
    3 * n ≤ Algebra.trdeg ℚ (adjoin ℚ (Set.range (fun i ↦ (z i : ℂ)) ∪ Set.range (j ∘ z) ∪
      Set.range (fun i ↦ iteratedDeriv 1 (j ∘ ofComplex) (z i)) ∪
      Set.range (fun i ↦ iteratedDeriv 2 (j ∘ ofComplex) (z i)))) := by
  sorry

end Arxiv.«2010.00102»
