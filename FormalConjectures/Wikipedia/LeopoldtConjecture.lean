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
group of global units $\varepsilon \in \mathcal{O}_K^\times$ whose diagonal image lies in $U_1$.
The group $E_1$ has finite index in $\mathcal{O}_K^\times$, so it has rank $r = r_1 + r_2 - 1$ by
Dirichlet's unit theorem.

**Leopoldt's conjecture** states that the $\mathbb{Z}_p$-rank of the closure $\overline{E_1}$ of
$E_1$ in $U_1$ is also $r_1 + r_2 - 1$. Equivalently, the *Leopoldt defect*
$\delta(K, p) = (r_1 + r_2 - 1) - \operatorname{rank}_{\mathbb{Z}_p} \overline{E_1}$ vanishes.

## The statements in this file

This file collects every formulation of the conjecture, together with only the mathematics needed
to *state* them. That they agree is proved in `LeopoldtConjecture/`, one equivalence per file,
with `LeopoldtConjecture.All` chaining them together. The supporting mathematics is in
`FormalConjecturesForMathlib.Leopoldt`.

* `leopoldt_conjecture`: the only $p$-adic relation among units of maximal rank in $E_1$ is
  the trivial one.
* `leopoldt_conjecture.variants.abelian`: the same for abelian $K/\mathbb{Q}$; a theorem of Ax
  and Brumer.
* `LeopoldtConjecture`: the elementary form, in which congruences modulo
  $p^M \mathcal{O}_K$ force divisibility of the exponents.
* `leopoldt_conjecture.variants.padicRegulator`: the matrix of $p$-adic logarithms of a
  fundamental system has full rank.
* `leopoldt_conjecture.variants.padicRegulator_ne_zero`: $R_p(K) \neq 0$ for totally real $K$.
* `leopoldt_conjecture.variants.zpRank`: Wikipedia's form,
  $\operatorname{rank}_{\mathbb{Z}_p} \overline{E_1} = r_1 + r_2 - 1$.
* `Mihailescu.LeopoldtConjecture`: Mihăilescu's form, in which the *Leopoldt defect*
  $\mathcal{D}_L(K) = \mathbb{Z}\text{-rk}(E) - \mathbb{Z}_p\text{-rk}(\overline{E})$
  vanishes, $\overline{E}$ being the closure of the global units in the *semilocal* units.

## The dictionary

* $r_1 + r_2 - 1$ is `rank K`;
* membership in $E_1$ is `IsPrincipalUnitAbove K p`, and $E_1$ itself is `E₁ K p`;
* a prime $\mathfrak{p} \mid p$ is `v : PrimesAbove K p`, and $K_\mathfrak{p}$ is
  `v.1.adicCompletion K`;
* $U_{1, \mathfrak{p}}$ is `oneUnits (v.1.adicCompletion K)`, whose $\mathbb{Z}_p$-module
  structure $u^a = \lim_n u^{a_n}$ is `OneUnits.instModule`;
* $U_1$ is `U₁ K p`, the diagonal embedding $E_1 \to U_1$ is `diag K p`, and the closure
  $\overline{E_1}$ is `closureE₁ K p`;
* the exponent vector $a \in \mathbb{Z}_p^r$ is `a : Fin (rank K) → ℤ_[p]`, and the relation
  $\prod_i \varepsilon_i^{a_i} = 1$ in $U_1$ is `IsPadicRelation K p ε a`, which spells out each
  $\mathbb{Z}_p$-power as a limit of integer powers using `PadicInt.appr`;
* the matrix $(\log_p \sigma(\varepsilon_i))$ is `logMatrix K p`, and Washington's regulator
  $R_p(K)$ is `padicRegulator K p σ₀ e`.

Mihăilescu's form uses none of these, so it carries its own dictionary. [Mihăilescu, §1.1] writes
$E = E(K) = \mathcal{O}(K)^\times$ for the units of $K$ and
$P = \{\wp \subset \mathcal{O}(K) : (p) \subset \wp\}$ for the set of primes above $p$; puts
$K_p = \prod_{\wp \in P} K_\wp = K \otimes_\mathbb{Q} \mathbb{Q}_p$, with diagonal embedding
$\iota : K \to K_p$ and $U \subset K_p^\times$ "the group of units, thus the product of local
units at the same completions"; and defines the $p$-adic closure of the global units and the
*Leopoldt defect* as
$$\overline{E} = \overline{\iota(E)} = \bigcap_{n > 0} \iota(E) \cdot U^{p^n}, \qquad
\mathcal{D}_L(K) = \mathbb{Z}\text{-rk}(E) - \mathbb{Z}_p\text{-rk}(\overline{E}).$$
Note that this works inside the full semilocal unit group $U$, not the principal units $U_1$.

* $P$ is `Mihailescu.PrimesOver p K` and $U$ is `Mihailescu.SemilocalUnits p K`;
* $\iota$ is `Mihailescu.diagonalUnits p K` and $\overline{E}$ is `Mihailescu.unitClosure p K`,
  the intersection written exactly as in the source;
* $\mathbb{Z}_p\text{-rk}$ is `Mihailescu.zpRankBelow`, which measures the rank from below by
  continuous injections of $\mathbb{Z}_p^n$ rather than with `Module.finrank`;
* $\mathcal{D}_L(K)$ is `Mihailescu.defect p K`, and $\mathcal{D}_L(K) = 0$ is
  `Mihailescu.LeopoldtConjecture p K`.

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
  \hat{\mathcal{O}}_\mathfrak{p}^\times$. The statements below need no parity hypothesis: they map
  into the *principal* units and quantify over a torsion-free family.
- L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Springer 1997, Chapter 5, §5.5
  (*The $p$-adic regulator*): the definition of $R_p(K)$ as a determinant of $p$-adic logarithms
  of units and the statement "Leopoldt's conjecture: $R_p(K) \neq 0$".
- J. Ax, *On the units of an algebraic number field*, Illinois J. Math. **9** (1965), 584-589, and
  A. Brumer, *On the units of algebraic number fields*, Mathematika **14** (1967), 121-124: the
  conjecture holds for abelian extensions of $\mathbb{Q}$.
-/

open Filter IsDedekindDomain NumberField NumberField.Units Topology

open scoped NumberField Valued

namespace Leopoldt

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/- ## The `p`-adic-relation form -/

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

/-
## Auxiliary lemmas

The remaining results relate `leopoldt_conjecture` to the elementary formulation
`LeopoldtConjecture` below. The lemmas in this section are the ingredients of that equivalence:
congruences of units modulo powers of $p$, the passage between such congruences and convergence
in the completions $K_\mathfrak{p}$ with $\mathfrak{p} \mid p$, and the passage between a family
of units of maximal rank and the fundamental system `fundSystem K`.
-/

/--
The hypotheses of `leopoldt_conjecture` can be satisfied: there is always a family of
$r_1 + r_2 - 1$ units of maximal rank which are principal units above $p$. Indeed, if $N$ is the
order of the finite group $(\mathcal{O}_K / p\mathcal{O}_K)^\times$, then the $N$-th powers of a
fundamental system of units will do.
-/
@[category API, AMS 11]
theorem exists_isMaxRank_isPrincipalUnitAbove :
    ∃ ε : Fin (rank K) → (𝓞 K)ˣ, IsMaxRank ε ∧ ∀ i, IsPrincipalUnitAbove K p (ε i) := by
  obtain ⟨Q, hQ0, hQ⟩ := exists_pow_sub_one_dvd (K := K) (p := p)
  exact ⟨fun i ↦ fundSystem K i ^ Q, isMaxRank_pow (isMaxRank_fundSystem K) hQ0,
    fun i v hv ↦ Ideal.mem_of_dvd _ (hQ _) hv⟩

/- ## The elementary form -/

/-- An elementary form of **Leopoldt's conjecture**

Let `K` be a number field and let `p` be a prime number.

Let `r` be the rank of the unit group of `K`, and let
Let `e i` (`i : Fin r`) be a system of fundamental units of `K`.

The conjecture: for all naturals `N` there is a natural `M` such that,
whenever `n : Fin r → ℤ` satisfies `∏ i, e i ^ n i = 1` mod  `p ^ M 𝓞 K`,
then all the `n i` are divisible by `p ^ N`.

This says that the topology on the unit group `(𝓞 K)ˣ` (modulo torsion) induced from
`∏_{v ∣ p} (𝓞_v)ˣ` is the `p`-adic topology, which is equivalent to injectivity of
`𝓞 Kˣ ⊗ ℤ_p → ∏_{v ∣ p} 𝓞_vˣ`, i.e. to the usual form of Leopoldt's conjecture. -/
def LeopoldtConjecture (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ N : ℕ, ∃ M : ℕ, ∀ n : Fin (Units.rank K) → ℤ,
    (p : 𝓞 K) ^ M ∣ (↑(∏ i, Units.fundSystem K i ^ n i) : 𝓞 K) - 1 →
      ∀ i, (p : ℤ) ^ N ∣ n i

/- ## The `p`-adic-regulator form -/

/--
The matrix $(\log_p \sigma(\varepsilon_i))_{i, \sigma}$ of Iwasawa logarithms of a fundamental
system of units $\varepsilon_1, \dots, \varepsilon_r$ of $K$, over all embeddings
$\sigma : K \to \mathbb{C}_p$. Its rows are indexed by `Fin (rank K)` and its columns by
`K →+* ℂ_[p]`; the entries are the classical $p$-adic logarithms by `logMatrix_apply_eq_div`.
-/
noncomputable def logMatrix : Matrix (Fin (rank K)) (K →+* ℂ_[p]) ℂ_[p] :=
  fun i σ ↦ PadicExpLog.iwasawaLog p (σ (fundSystem K i : K))

/--
The entries of `logMatrix` are the classical $p$-adic logarithms: for any $Q \geq 1$ with
$\|\sigma(\varepsilon_i)^Q - 1\| < 1$ (`hasPrincipalUnitPow_map` provides one),
$\log_p \sigma(\varepsilon_i) = \log_p(\sigma(\varepsilon_i)^Q) / Q$.
-/
@[category API, AMS 11]
theorem logMatrix_apply_eq_div (i : Fin (rank K)) (σ : K →+* ℂ_[p]) {Q : ℕ} (hQ : 0 < Q)
    (h : ‖σ (fundSystem K i : K) ^ Q - 1‖ < 1) :
    logMatrix K p i σ = PadicExpLog.padicLog (σ (fundSystem K i : K) ^ Q) / Q :=
  PadicExpLog.iwasawaLog_of_hasPrincipalUnitPow PadicExpLog.PadicComplex.norm_natCast_p_lt_one hQ h

/--
**Leopoldt's conjecture, $p$-adic regulator form.** Let $\varepsilon_1, \dots, \varepsilon_r$,
$r = r_1 + r_2 - 1$, be a fundamental system of units of $K$ and let $\sigma_1, \dots, \sigma_n$,
$n = [K : \mathbb{Q}]$, be the embeddings of $K$ into $\mathbb{C}_p$. Then the $r \times n$
matrix $(\log_p \sigma_j(\varepsilon_i))$ of $p$-adic logarithms has rank $r$.

Equivalently, some $r \times r$ minor of this matrix, a *$p$-adic regulator* $R_p(K)$, is
nonzero. For totally real $K$ one has $n = r + 1$ and each row sums to
$\log_p N_{K/\mathbb{Q}}(\varepsilon_i) = \log_p(\pm 1) = 0$ (`sum_logMatrix`), so all these
minors agree up to sign (`padicRegulator_eq_or_eq_neg`) and the statement is Leopoldt's original
$R_p(K) \neq 0$, see `padicRegulator` and `leopoldt_conjecture.variants.padicRegulator_ne_zero`
([Wikipedia](https://en.wikipedia.org/wiki/Leopoldt%27s_conjecture): "Leopoldt's conjecture
... states that the $p$-adic regulator of a number field does not vanish"; Washington, §5.5).
For general $K$ the rank formulation avoids choosing a minor. The entries of the matrix are the
classical $p$-adic logarithms of the units by `logMatrix_apply_eq_div`, and the rank is at most
$r$ since the matrix has $r$ rows. This statement is equivalent to the other two forms of the
conjecture in this file: see `leopoldtConjecture_iff_rank` and `forall_isPadicRelation_iff_rank`.
-/
@[category research open, AMS 11]
theorem leopoldt_conjecture.variants.padicRegulator : (logMatrix K p).rank = rank K := by
  sorry

/--
For totally real $K$ the embeddings $K \to \mathbb{C}_p$ other than a given one $\sigma_0$ are
$[K : \mathbb{Q}] - 1 = r_1 - 1 = r$ in number.
-/
@[category API, AMS 11]
theorem card_ne_eq_rank [IsTotallyReal K] (σ₀ : K →+* ℂ_[p]) :
    Nat.card {σ : K →+* ℂ_[p] // σ ≠ σ₀} = rank K := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Embeddings.card K ℂ_[p],
    IsTotallyReal.finrank, rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]

/-- For totally real `K`, the embeddings `K → ℂ_p` other than `σ₀` can be indexed by
`Fin (rank K)`. -/
@[category API, AMS 11]
theorem nonempty_equiv_fin_rank [IsTotallyReal K] (σ₀ : K →+* ℂ_[p]) :
    Nonempty (Fin (rank K) ≃ {σ : K →+* ℂ_[p] // σ ≠ σ₀}) := by
  classical
  exact ⟨(Fintype.equivFinOfCardEq
    (by rw [← Nat.card_eq_fintype_card, card_ne_eq_rank K p σ₀])).symm⟩

/--
The **$p$-adic regulator** of a totally real number field $K$ (Washington, §5.5). Let
$\varepsilon_1, \dots, \varepsilon_r$ be the fundamental system of units `fundSystem K` and let
$\sigma_0$ be one of the $r + 1 = [K : \mathbb{Q}]$ embeddings $K \to \mathbb{C}_p$. Then
$$R_p(K) = \det\big(\log_p \sigma(\varepsilon_i)\big)_{i,\, \sigma \neq \sigma_0},$$
where the columns $\sigma \neq \sigma_0$ are indexed by `Fin (rank K)` through `e`. Up to sign
the value depends neither on $\sigma_0$ nor on `e` (`padicRegulator_eq_or_eq_neg`), because the
rows of `logMatrix K p` sum to zero (`sum_logMatrix`). The definition makes sense for any `K`,
but an equivalence `e` exists only when `K` is totally real (`nonempty_equiv_fin_rank`).
-/
noncomputable def padicRegulator (σ₀ : K →+* ℂ_[p])
    (e : Fin (rank K) ≃ {σ : K →+* ℂ_[p] // σ ≠ σ₀}) : ℂ_[p] :=
  ((logMatrix K p).submatrix id fun j ↦ (e j : K →+* ℂ_[p])).det

/--
**Leopoldt's conjecture for totally real fields, regulator form** [Washington, §5.5]: the
$p$-adic regulator $R_p(K)$ of a totally real number field $K$ does not vanish.

By `padicRegulator_eq_or_eq_neg` the statement does not depend on the choice of the omitted
embedding $\sigma_0$ or of the ordering `e`, and by `padicRegulator_ne_zero_iff` it is
`leopoldt_conjecture.variants.padicRegulator` specialised to totally real `K`; by
`leopoldtConjecture_iff_padicRegulator_ne_zero` it is also equivalent to the elementary form
`LeopoldtConjecture`.
-/
@[category research open, AMS 11]
theorem leopoldt_conjecture.variants.padicRegulator_ne_zero [IsTotallyReal K]
    (σ₀ : K →+* ℂ_[p]) (e : Fin (rank K) ≃ {σ : K →+* ℂ_[p] // σ ≠ σ₀}) :
    Leopoldt.padicRegulator K p σ₀ e ≠ 0 := by
  sorry

/- ## The $\mathbb{Z}_p$-rank form -/

section completion

variable {K}

/-- The completion $K_\mathfrak{p}$ has characteristic zero. -/
instance (v : HeightOneSpectrum (𝓞 K)) : CharZero (v.adicCompletion K) :=
  charZero_of_injective_algebraMap (algebraMap K _).injective

end completion

/-- The primes $\mathfrak{p}$ of $\mathcal{O}_K$ above $p$. -/
abbrev PrimesAbove : Type _ := {v : HeightOneSpectrum (𝓞 K) // (p : 𝓞 K) ∈ v.asIdeal}

omit [Fact p.Prime] in
/-- `‖p‖ < 1` in $K_\mathfrak{p}$ for $\mathfrak{p} \mid p$. -/
@[category API, AMS 11]
theorem norm_natCast_lt_one (v : PrimesAbove K p) : ‖((p : ℕ) : v.1.adicCompletion K)‖ < 1 := by
  have h : ((p : ℕ) : v.1.adicCompletion K)
      = algebraMap (𝓞 K) (v.1.adicCompletion K) (p : 𝓞 K) := by
    push_cast
    ring
  rw [h]
  show ‖FinitePlace.embedding v.1 (algebraMap (𝓞 K) K (p : 𝓞 K))‖ < 1
  exact (FinitePlace.norm_lt_one_iff_mem K v.1 (p : 𝓞 K)).2 v.2

instance (v : PrimesAbove K p) : Fact (‖((p : ℕ) : v.1.adicCompletion K)‖ < 1) :=
  ⟨norm_natCast_lt_one K p v⟩

/-- $U_1 = \prod_{\mathfrak{p} \mid p} U_{1, \mathfrak{p}}$, written additively, as a
$\mathbb{Z}_p$-module. -/
abbrev U₁ : Type _ := ∀ v : PrimesAbove K p, Additive (oneUnits (v.1.adicCompletion K))

/-- $E_1$: the global units $\varepsilon \equiv 1 \pmod{\mathfrak{p}}$ for all
$\mathfrak{p} \mid p$, i.e. those whose diagonal image lies in $U_1$
([Wikipedia]: "the set of global units $\varepsilon$ that map to $U_1$ via the diagonal
embedding"). -/
def E₁ : Subgroup (𝓞 K)ˣ where
  carrier := {u | IsPrincipalUnitAbove K p u}
  mul_mem' {a b} ha hb v hv := by
    have h : ((a * b : (𝓞 K)ˣ) : 𝓞 K) - 1
        = (a : 𝓞 K) * ((b : 𝓞 K) - 1) + ((a : 𝓞 K) - 1) := by
      push_cast
      ring
    rw [h]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hb v hv)) (ha v hv)
  one_mem' v hv := by simp
  inv_mem' {a} ha v hv := by
    have hinv : ((a⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (a : 𝓞 K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h : ((a⁻¹ : (𝓞 K)ˣ) : 𝓞 K) - 1
        = -((a⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * ((a : 𝓞 K) - 1) := by
      linear_combination hinv
    rw [h]
    exact Ideal.mul_mem_left _ _ (ha v hv)

omit [NumberField K] [Fact p.Prime] in
@[category API, AMS 11]
theorem mem_E₁_iff {u : (𝓞 K)ˣ} : u ∈ E₁ K p ↔ IsPrincipalUnitAbove K p u := Iff.rfl

omit [Fact p.Prime] in
/-- A unit of $E_1$ is a principal unit in every $K_\mathfrak{p}$, $\mathfrak{p} \mid p$. -/
@[category API, AMS 11]
theorem norm_algebraMap_sub_one_lt {u : (𝓞 K)ˣ} (hu : IsPrincipalUnitAbove K p u)
    (v : PrimesAbove K p) : ‖algebraMap (𝓞 K) (v.1.adicCompletion K) u - 1‖ < 1 := by
  rw [← map_one (algebraMap (𝓞 K) (v.1.adicCompletion K)), ← map_sub]
  show ‖FinitePlace.embedding v.1 (algebraMap (𝓞 K) K ((u : 𝓞 K) - 1))‖ < 1
  exact (FinitePlace.norm_lt_one_iff_mem K v.1 _).2 (hu v.1 v.2)

/-- The diagonal embedding $E_1 \to U_1$, $\varepsilon \mapsto (\varepsilon)_{\mathfrak{p} \mid p}$
([Wikipedia]: "$E_1$ embedded diagonally in $U_1$"). -/
noncomputable def diag : Additive (E₁ K p) →+ U₁ K p where
  toFun u v := Additive.ofMul
    ⟨Units.map (algebraMap (𝓞 K) (v.1.adicCompletion K)).toMonoidHom (u.toMul : (𝓞 K)ˣ),
      OneUnits.mem_oneUnits_iff.2 (norm_algebraMap_sub_one_lt K p u.toMul.2 v)⟩
  map_zero' := by
    funext v
    refine OneUnits.ext_of_coe ?_
    simp
  map_add' u w := by
    funext v
    refine OneUnits.ext_of_coe ?_
    show ((Units.map (algebraMap (𝓞 K) (v.1.adicCompletion K)).toMonoidHom
        (((u.toMul * w.toMul : E₁ K p)) : (𝓞 K)ˣ) : (v.1.adicCompletion K)ˣ)
          : v.1.adicCompletion K) = _
    rw [Subgroup.coe_mul, map_mul]
    rfl

omit [Fact p.Prime] in
@[category API, AMS 11]
theorem coe_diag_apply (u : Additive (E₁ K p)) (v : PrimesAbove K p) :
    (((diag K p u v).toMul : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) =
      algebraMap (𝓞 K) (v.1.adicCompletion K) ((u.toMul : (𝓞 K)ˣ) : 𝓞 K) := rfl

/-- `a • x = lim (a.appr n) • x` in $U_1$. -/
@[category API, AMS 11]
theorem tendsto_appr_nsmul (a : ℤ_[p]) (x : U₁ K p) :
    Tendsto (fun n ↦ a.appr n • x) atTop (𝓝 (a • x)) :=
  tendsto_pi_nhds.2 fun v ↦ OneUnits.tendsto_appr_nsmul a (x v)

/-- Integer `p`-adic powers are ordinary powers, componentwise in $U_1$. -/
@[category API, AMS 11]
theorem U₁.natCast_smul (n : ℕ) (x : U₁ K p) : (n : ℤ_[p]) • x = n • x :=
  funext fun v ↦ OneUnits.natCast_smul n (x v)

@[category API, AMS 11]
theorem U₁.intCast_smul (n : ℤ) (x : U₁ K p) : (n : ℤ_[p]) • x = n • x :=
  funext fun v ↦ OneUnits.intCast_smul n (x v)

/-- The closure $\overline{E_1}$ of the diagonal image of $E_1$ in $U_1$, as a
$\mathbb{Z}_p$-submodule of $U_1$ ([Wikipedia]: "the closure of $E_1$ embedded diagonally in
$U_1$"; [Nelson, §3]: "the topological closure of $\Delta(X)$ in
$\prod_{\mathfrak{p} \mid p} \mathcal{O}^*_{\mathfrak{p}, 1}$"). A closed subgroup of $U_1$ is
automatically a $\mathbb{Z}_p$-submodule. -/
noncomputable def closureE₁ : Submodule ℤ_[p] (U₁ K p) where
  toAddSubmonoid := (diag K p).range.topologicalClosure.toAddSubmonoid
  smul_mem' a x hx :=
    AddSubgroup.smul_mem_of_isClosed (AddSubgroup.isClosed_topologicalClosure _) hx
      (tendsto_appr_nsmul K p a x)

@[category API, AMS 11]
theorem coe_closureE₁ : (closureE₁ K p : Set (U₁ K p)) = closure (Set.range (diag K p)) := by
  show ((diag K p).range.topologicalClosure : Set (U₁ K p)) = _
  rw [AddSubgroup.topologicalClosure_coe, AddMonoidHom.coe_range]

/--
**Leopoldt's conjecture, $\mathbb{Z}_p$-rank form.** Let $K$ be a number field and $p$ a prime.
The $\mathbb{Z}_p$-rank of the closure $\overline{E_1}$ of $E_1$ embedded diagonally in
$U_1 = \prod_{\mathfrak{p} \mid p} U_{1, \mathfrak{p}}$ is $r_1 + r_2 - 1$.

This is the statement of [Wikipedia] verbatim. It is equivalent to `leopoldt_conjecture` by
`Leopoldt.zpRank_iff`. The rank is finite, at most $r_1 + r_2 - 1$ (`rank_closureE₁_eq`), so
`Module.finrank` is the honest rank here.
-/
@[category research open, AMS 11]
theorem leopoldt_conjecture.variants.zpRank : Module.finrank ℤ_[p] (closureE₁ K p) = rank K := by
  sorry

end Leopoldt

/- ## Mihăilescu's form -/

namespace Leopoldt.Mihailescu

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]

/-- The set `P = {℘ ⊂ 𝓞(K) : (p) ⊂ ℘}` of primes of `𝓞 K` above `p`. -/
abbrev PrimesOver := {v : HeightOneSpectrum (𝓞 K) // (p : 𝓞 K) ∈ v.asIdeal}

instance : Finite (PrimesOver p K) := by
  have hpne : (p : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out (p := p.Prime)).ne_zero
  have hp0 : Ideal.span {(p : 𝓞 K)} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hpne
  apply Set.Finite.to_subtype
  refine (Ideal.finite_factors (R := 𝓞 K) hp0).subset ?_
  intro v hv
  exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv)

/-- `U`: the group of semilocal units at `p`, that is the product `∏_{℘ | p} 𝓞_℘^×` of the
local units at the primes above `p`. -/
abbrev SemilocalUnits := ∀ v : PrimesOver p K, (v.1.adicCompletionIntegers K)ˣ

/-- `ι : E(K) → U`, the diagonal embedding of the global units into the semilocal units. -/
noncomputable def diagonalUnits : (𝓞 K)ˣ →* SemilocalUnits p K :=
  MonoidHom.pi fun v => Units.map (algebraMap (𝓞 K) (v.1.adicCompletionIntegers K)).toMonoidHom

/-- `Ē = ⋂_{n > 0} ι(E) · U^{p^n}`, the `p`-adic closure of the image of the global units
inside the semilocal units, exactly as the intersection is written in the source. -/
noncomputable def unitClosure : Subgroup (SemilocalUnits p K) :=
  ⨅ n : ℕ, ((diagonalUnits p K).range ⊔ (powMonoidHom (p ^ (n + 1))).range)

/-- The free `ℤ_p`-rank of a subgroup `H` of a commutative topological group, computed as the
largest `n ≤ bound` for which `ℤ_p^n` admits a continuous injective homomorphism into `H`.

For a closed subgroup of the semilocal units this is the usual free `ℤ_p`-rank: such a subgroup
is isomorphic to `Δ × ℤ_p^d` with `Δ` finite, and continuous injections from `ℤ_p^n` exist
exactly for `n ≤ d`.  Continuity is essential — as abstract groups `ℤ_p^n` embeds into `ℤ_p`
for every `n`; and since `ℤ_p^n` is compact and the target Hausdorff, a continuous injection is
automatically a closed embedding.

The `bound` is carried only so that the supremum is visibly taken over a bounded set and never
falls back on the junk value of `sSup` on an unbounded set of naturals.  Any `bound` at least as
large as the true rank yields the true rank. -/
noncomputable def zpRankBelow {G : Type*} [CommGroup G] [TopologicalSpace G]
    (bound : ℕ) (H : Subgroup G) : ℕ :=
  sSup {n : ℕ | n ≤ bound ∧ ∃ f : Multiplicative (Fin n → ℤ_[p]) →* G,
    Function.Injective f ∧ Continuous f ∧ ∀ x, f x ∈ H}

/-- The **Leopoldt defect** `𝒟_L(K) = ℤ-rk(E) - ℤ_p-rk(Ē)` of `K` at `p`.

`ℤ-rk(E) = r₁ + r₂ - 1` is Dirichlet's unit rank, which Mathlib provides as
`NumberField.Units.rank`.  The `ℤ_p`-rank of `Ē` is bounded by that of the whole semilocal unit
group `U`, which is `[K : ℚ]`, so taking `[K : ℚ]` as the bound never constrains it. -/
noncomputable def defect : ℕ :=
  Units.rank K - zpRankBelow p (Module.finrank ℚ K) (unitClosure p K)

/-- `defect` unfolded. Stated here so that downstream files can rewrite with it without
re-elaborating the instance arguments of `zpRankBelow`. -/
@[category API, AMS 11]
theorem defect_eq_sub :
    defect p K = Units.rank K - zpRankBelow p (Module.finrank ℚ K) (unitClosure p K) := rfl

/--
**Leopoldt's conjecture, Mihăilescu's form.** Let $K$ be a number field and $p$ a prime. The
Leopoldt defect $\mathcal{D}_L(K) = \mathbb{Z}\text{-rk}(E) -
\mathbb{Z}_p\text{-rk}(\overline{E})$ of [Mihăilescu, §1.1] vanishes.

It is equivalent to the $\mathbb{Z}_p$-rank form by
`Leopoldt.Mihailescu.leopoldtConjecture_iff_finrank`, and so to every other formulation above.
-/
def LeopoldtConjecture : Prop := defect p K = 0

/-- `LeopoldtConjecture` unfolded. -/
@[category API, AMS 11]
theorem leopoldtConjecture_iff_defect : LeopoldtConjecture p K ↔ defect p K = 0 := Iff.rfl

end Leopoldt.Mihailescu
