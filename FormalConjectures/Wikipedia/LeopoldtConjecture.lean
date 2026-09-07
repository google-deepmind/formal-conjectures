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

import FormalConjecturesUtil

/-!
# Leopoldt's conjecture

Let $K$ be a number field with $r_1$ real and $r_2$ pairs of complex embeddings, and let $p$ be a
prime. For each prime $\mathfrak{p}$ of $K$ above $p$, let $U_{1, \mathfrak{p}}$ be the group of
principal units of the completion $K_\mathfrak{p}$, that is, the units congruent to $1$ modulo the
maximal ideal, and set $U_1 = \prod_{\mathfrak{p} \mid p} U_{1, \mathfrak{p}}$. Let $E_1$ be the
group of global units $\varepsilon \in \mathcal{O}_K^\times$ whose diagonal image lies in $U_1$,
i.e. with $\varepsilon \equiv 1 \pmod{\mathfrak{p}}$ for every $\mathfrak{p} \mid p$. The group
$E_1$ has finite index in $\mathcal{O}_K^\times$, so it has rank $r = r_1 + r_2 - 1$ by
Dirichlet's unit theorem.

**Leopoldt's conjecture** states that the $\mathbb{Z}_p$-rank of the closure $\overline{E_1}$ of
$E_1$ in $U_1$ is also $r_1 + r_2 - 1$. Equivalently, the *Leopoldt defect*
$\delta(K, p) = (r_1 + r_2 - 1) - \operatorname{rank}_{\mathbb{Z}_p} \overline{E_1}$ vanishes.

## The formalisation

The statement `leopoldt_conjecture` below is an equivalent form of the conjecture which needs
neither a $\mathbb{Z}_p$-module structure on $U_1$ nor a $p$-adic logarithm.

Fix units $\varepsilon_1, \dots, \varepsilon_r \in E_1$ that generate a subgroup of finite index
in $\mathcal{O}_K^\times$ (`IsMaxRank`). Each $U_{1, \mathfrak{p}}$ is a pro-$p$ group, so a
principal unit $u$ has a $p$-adic power $u^a = \lim_n u^{c_n}$ for $a \in \mathbb{Z}_p$ and
integers $c_n \to a$. This gives a continuous $\mathbb{Z}_p$-linear map
$$\varphi_\varepsilon : \mathbb{Z}_p^r \to U_1, \qquad a \mapsto \prod_i \varepsilon_i^{a_i},$$
whose image is the closure of $\langle \varepsilon_1, \dots, \varepsilon_r \rangle$, a subgroup
of finite index in $\overline{E_1}$. Rank is insensitive to finite index, so
$$\operatorname{rank}_{\mathbb{Z}_p} \overline{E_1}
  = r - \operatorname{rank}_{\mathbb{Z}_p} \ker \varphi_\varepsilon,
\qquad \text{i.e.} \qquad
\delta(K, p) = \operatorname{rank}_{\mathbb{Z}_p} \ker \varphi_\varepsilon.$$
The kernel is a submodule of the free module $\mathbb{Z}_p^r$, so its rank is zero if and only
if it is zero. Hence Leopoldt's conjecture says exactly that $\varphi_\varepsilon$ is injective:
the only $a \in \mathbb{Z}_p^r$ with $\prod_i \varepsilon_i^{a_i} = 1$ in every $K_\mathfrak{p}$
with $\mathfrak{p} \mid p$ is $a = 0$. The dictionary between the two formulations is:

- $r_1 + r_2 - 1$ is `rank K`;
- membership in $E_1$ is `IsPrincipalUnitAbove K p`;
- the generators $\varepsilon_1, \dots, \varepsilon_r$ are `ε : Fin (rank K) → (𝓞 K)ˣ`, with
  `IsMaxRank ε` and `∀ i, IsPrincipalUnitAbove K p (ε i)`;
- the exponent vector $a \in \mathbb{Z}_p^r$ is `a : Fin (rank K) → ℤ_[p]`;
- the relation $\prod_i \varepsilon_i^{a_i} = 1$ in $U_1$ is `IsPadicRelation K p ε a`, which
  spells out each $\mathbb{Z}_p$-power as a limit of integer powers using `PadicInt.appr`;
- $\operatorname{rank}_{\mathbb{Z}_p} \overline{E_1} = r_1 + r_2 - 1$ is the conclusion `a = 0`
  for every such relation.

Quantifying over all families $\varepsilon$ loses nothing. The rank of $\overline{E_1}$ does not
depend on the family, so injectivity of $\varphi_\varepsilon$ for one family implies it for all.
Such a family always exists (`exists_isMaxRank_isPrincipalUnitAbove`).

Taking $p$-adic logarithms turns $\prod_i \varepsilon_i^{a_i} = 1$ into
$\sum_i a_i \log_p \varepsilon_i = 0$, so the statement also says that the $p$-adic logarithms
of the $\varepsilon_i$ are $\mathbb{Z}_p$-linearly independent, the $p$-adic analogue of the
hypothesis `IsMaxRank ε` that their real logarithms are $\mathbb{R}$-linearly independent.

*References:*
- [Wikipedia, *Leopoldt's conjecture*](https://en.wikipedia.org/wiki/Leopoldt%27s_conjecture):
  "Leopoldt's conjecture states that the $\mathbb{Z}_p$-module rank of the closure of $E_1$
  embedded diagonally in $U_1$ is also $r_1 + r_2 - 1$".
- D. Nelson, *A Variation on Leopoldt's Conjecture: Some Local Units instead of All Local Units*,
  [arXiv:1308.4637](https://arxiv.org/abs/1308.4637), §3, Conjecture 3.1 (the formulation used
  here, with $X = \Delta^{-1}(\prod_{\mathfrak{p} \mid p} \mathcal{O}^*_{\mathfrak{p}, 1})$ and the
  closure of $\Delta(X)$), and Lemma 4.2 (the reading of $\mathbb{Z}_p$-powers used here).
- P. Mihăilescu, *Leopoldt's Conjecture for CM fields*,
  [arXiv:1105.4544](https://arxiv.org/abs/1105.4544), §1: the closure is
  $\bar{E} = \bigcap_{n > 0} \iota(E) \cdot U^{p^n}$ and the *Leopoldt defect* is
  $\mathcal{D}_l(K) = \operatorname{rank}_{\mathbb{Z}} E - \operatorname{rank}_{\mathbb{Z}_p}
  \bar{E}$.
- G. Gras et al., *Applications of representation theory and of explicit units to Leopoldt's
  conjecture*, [arXiv:2301.05700](https://arxiv.org/abs/2301.05700), §1: Leopoldt's conjecture
  holds iff $\lambda_{K, p} : \mathbb{Z}_p \otimes_{\mathbb{Z}} \mathcal{O}_K^\times \to
  \prod_{\mathfrak{p} \mid p} U_{1, \mathfrak{p}}$ is injective, iff $\delta(K, p) = 0$.
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer 2008,
  Theorem 10.3.6: for odd $p$, the conjecture is equivalent to injectivity of
  $\mathcal{O}_K^\times \otimes \mathbb{Z}_p \to \prod_{\mathfrak{p} \mid p}
  \hat{\mathcal{O}}_\mathfrak{p}^\times$. The statement below needs no parity hypothesis: it maps
  into the *principal* units and quantifies over a torsion-free family.
- J. Ax, *On the units of an algebraic number field*, Illinois J. Math. **9** (1965), 584-589, and
  A. Brumer, *On the units of algebraic number fields*, Mathematika **14** (1967), 121-124: the
  conjecture holds for abelian extensions of $\mathbb{Q}$.
-/

open Filter IsDedekindDomain NumberField NumberField.Units

open scoped NumberField

namespace Leopoldt

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/--
`IsPrincipalUnitAbove K p u` says that the unit $u \in \mathcal{O}_K^\times$ is congruent to $1$
modulo every prime $\mathfrak{p}$ of $\mathcal{O}_K$ above $p$. Equivalently, the image of $u$ in
each completion $K_\mathfrak{p}$ with $\mathfrak{p} \mid p$ is a principal unit, i.e. lies in
$U_{1, \mathfrak{p}} = 1 + \mathfrak{m}_\mathfrak{p}$.

This is membership in the group $E_1$ of
[Wikipedia](https://en.wikipedia.org/wiki/Leopoldt%27s_conjecture), the global units whose
diagonal image lies in $U_1 = \prod_{\mathfrak{p} \mid p} U_{1, \mathfrak{p}}$, and in the group
$X$ of [Nelson, §3]. Since $E_1$ is the kernel of reduction to the finite group
$\prod_{\mathfrak{p} \mid p} (\mathcal{O}_K / \mathfrak{p})^\times$, it has finite index in
$\mathcal{O}_K^\times$.
-/
def IsPrincipalUnitAbove (u : (𝓞 K)ˣ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → (u : 𝓞 K) - 1 ∈ v.asIdeal

/--
`IsPadicRelation K p ε a` says that $\prod_i \varepsilon_i^{a_i} = 1$ in $U_1$, i.e. in every
completion $K_\mathfrak{p}$ with $\mathfrak{p} \mid p$. Here $\varepsilon_1, \dots, \varepsilon_r$
are global units, $a = (a_1, \dots, a_r) \in \mathbb{Z}_p^r$ is a vector of $p$-adic exponents,
and $\varepsilon_i^{a_i}$ is the $\mathbb{Z}_p$-power of a principal unit.

The $\mathbb{Z}_p$-power is spelled out as the limit that defines it. The natural number
`(a i).appr n` satisfies `(a i).appr n ≡ a i (mod p ^ n)` (`PadicInt.appr_spec`), so it tends to
$a_i$ in $\mathbb{Z}_p$ as $n \to \infty$, and the condition is that
$\prod_i \varepsilon_i^{(a_i).\mathrm{appr}\, n} \to 1$ in $K_\mathfrak{p}$. When every
$\varepsilon_i$ satisfies `IsPrincipalUnitAbove K p`, it lies in the pro-$p$ group
$U_{1, \mathfrak{p}}$, so this sequence converges to $\prod_i \varepsilon_i^{a_i}$ and the limit
does not depend on the choice of integers approximating $a_i$. Without that hypothesis the
sequence need not converge, e.g. for a root of unity of order prime to $p$.

This is how [Nelson, Lemma 4.2] reads a $\mathbb{Z}_p$-relation: "there exists $a_{j,n} \in
\mathbb{Z}$ such that $p$-adically $a_{j,n} \to a_j$ and $u_1^{a_{1,n}} \cdots u_t^{a_{t,n}} \to 1$
in $M_\mathfrak{p}$".
-/
def IsPadicRelation (ε : Fin (rank K) → (𝓞 K)ˣ) (a : Fin (rank K) → ℤ_[p]) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal →
    Tendsto (fun n : ℕ ↦ ((∏ i, (ε i : K) ^ (a i).appr n : K) : v.adicCompletion K))
      atTop (nhds 1)

/--
**Leopoldt's conjecture.** Let $K$ be a number field and $p$ a prime. Let
$\varepsilon_1, \dots, \varepsilon_r$, with $r = r_1 + r_2 - 1$, be units of $\mathcal{O}_K$ that
generate a subgroup of finite index in $\mathcal{O}_K^\times$ and are principal units at every
prime above $p$, i.e. lie in $E_1$. Then the only $a \in \mathbb{Z}_p^r$ with
$\prod_i \varepsilon_i^{a_i} = 1$ in every completion $K_\mathfrak{p}$ with $\mathfrak{p} \mid p$
is $a = 0$.

In other words, the map $\varphi_\varepsilon : \mathbb{Z}_p^r \to U_1$,
$a \mapsto \prod_i \varepsilon_i^{a_i}$, is injective. Its image has finite index in the closure
$\overline{E_1}$ of $E_1$ in $U_1$, so
$\operatorname{rank}_{\mathbb{Z}_p} \overline{E_1} = r - \operatorname{rank}_{\mathbb{Z}_p}
\ker \varphi_\varepsilon$, and injectivity is equivalent to the statement
$\operatorname{rank}_{\mathbb{Z}_p} \overline{E_1} = r_1 + r_2 - 1$ of Wikipedia, i.e. to the
vanishing of the Leopoldt defect. See the module docstring for details.
-/
@[category research open, AMS 11]
theorem leopoldt_conjecture (ε : Fin (rank K) → (𝓞 K)ˣ) (hmax : IsMaxRank ε)
    (hone : ∀ i, IsPrincipalUnitAbove K p (ε i))
    {a : Fin (rank K) → ℤ_[p]} (ha : IsPadicRelation K p ε a) :
    a = 0 := by
  sorry

/--
**Ax-Brumer theorem.** Leopoldt's conjecture holds when $K$ is an abelian extension of
$\mathbb{Q}$. This is `leopoldt_conjecture` with the extra hypothesis `IsAbelianGalois ℚ K`.

Ax reduced the abelian case to a $p$-adic analogue of Baker's theorem on linear forms in
logarithms, which Brumer then proved.
-/
@[category research solved, AMS 11]
theorem leopoldt_conjecture.variants.abelian [IsAbelianGalois ℚ K]
    (ε : Fin (rank K) → (𝓞 K)ˣ) (hmax : IsMaxRank ε)
    (hone : ∀ i, IsPrincipalUnitAbove K p (ε i))
    {a : Fin (rank K) → ℤ_[p]} (ha : IsPadicRelation K p ε a) :
    a = 0 := by
  sorry

/--
The hypotheses of `leopoldt_conjecture` can be satisfied: there is always a family of
$r_1 + r_2 - 1$ units of maximal rank which are principal units above $p$. Indeed, if $N$ is the
order of the finite group $(\mathcal{O}_K / p\mathcal{O}_K)^\times$, then the $N$-th powers of a
fundamental system of units will do.
-/
@[category API, AMS 11]
theorem exists_isMaxRank_isPrincipalUnitAbove :
    ∃ ε : Fin (rank K) → (𝓞 K)ˣ, IsMaxRank ε ∧ ∀ i, IsPrincipalUnitAbove K p (ε i) := by
  sorry

end Leopoldt
