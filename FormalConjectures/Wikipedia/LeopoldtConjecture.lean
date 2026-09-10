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
The group $E_1$ has finite index in $\mathcal{O}_K^\times$, so it has rank $r_1 + r_2 - 1$ by
Dirichlet's unit theorem.

Each $U_{1, \mathfrak{p}}$ is a pro-$p$ group, hence a $\mathbb{Z}_p$-module: for
$a \in \mathbb{Z}_p$ and integers $a_n \to a$, $u^a = \lim_n u^{a_n}$. **Leopoldt's conjecture**
states that the $\mathbb{Z}_p$-rank of the closure $\overline{E_1}$ of $E_1$ in $U_1$ is also
$r_1 + r_2 - 1$. Equivalently, the *Leopoldt defect*
$\delta(K, p) = (r_1 + r_2 - 1) - \operatorname{rank}_{\mathbb{Z}_p} \overline{E_1}$ vanishes.

## The statements in this file

* `leopoldt_conjecture`: Wikipedia's form, $\operatorname{rank}_{\mathbb{Z}_p} \overline{E_1} =
  r_1 + r_2 - 1$, together with `leopoldt_conjecture.variants.abelian`, the theorem of Ax and
  Brumer for abelian $K / \mathbb{Q}$;
* `leopoldt_conjecture.variants.padicRegulator`: Wikipedia's other form, that the $p$-adic
  regulator of $K$ does not vanish, stated as: the matrix of $p$-adic logarithms of a family of
  units of maximal rank in $E_1$ has full rank;
* `leopoldt_conjecture.variants.padicRelation`: the only $p$-adic relation among units of maximal
  rank in $E_1$ is the trivial one;
* `leopoldt_conjecture.variants.elementary`: congruences modulo $p^M \mathcal{O}_K$ force
  divisibility of the exponents;
* `leopoldt_conjecture.variants.mihailescu`: Mihăilescu's form, in which the *Leopoldt defect*
  $\mathcal{D}_L(K) = \mathbb{Z}\text{-rk}(E) - \mathbb{Z}_p\text{-rk}(\overline{E})$ vanishes,
  $\overline{E}$ being the closure of the global units in the *semilocal* units.

The `padicRelation` and `elementary` forms are low-level: they are stated using nothing beyond
mathlib, at the cost of not being Wikipedia's formulation verbatim.

## The dictionary

* $r_1 + r_2 - 1$ is `NumberField.Units.rank K`;
* a prime $\mathfrak{p} \mid p$ is `v : NumberField.PrimesAbove K p`, and $K_\mathfrak{p}$ is
  `v.1.adicCompletion K`;
* $U_{1, \mathfrak{p}}$ is `oneUnits (v.1.adicCompletion K)`, and its $\mathbb{Z}_p$-module
  structure $u^a = \lim_n u^{a_n}$ is `OneUnits.instModule`, from
  `FormalConjecturesForMathlib.NumberTheory.Padics.OneUnits`; that $K_\mathfrak{p}$ has residue
  characteristic $p$, and that a unit of $E_1$ lands in $U_{1, \mathfrak{p}}$, are
  `IsDedekindDomain.HeightOneSpectrum.norm_natCast_lt_one` and `…norm_algebraMap_sub_one_lt`
  from `FormalConjecturesForMathlib.NumberTheory.NumberField.PrimesAbove`;
* $U_1$ is `U₁ K p`, written additively so that it is a `ℤ_[p]`-module;
* $E_1$ is `E₁ K p`, and membership in it is `IsPrincipalUnitAbove K p`;
* the diagonal embedding $E_1 \to U_1$ is `diag K p`, and the closure $\overline{E_1}$ is
  `closureE₁ K p`, a `ℤ_[p]`-submodule of `U₁ K p`;
* $\operatorname{rank}_{\mathbb{Z}_p} \overline{E_1}$ is `Module.rank ℤ_[p] (closureE₁ K p)`;
* the exponent vector $a \in \mathbb{Z}_p^r$ is `a : Fin (rank K) → ℤ_[p]`, and the relation
  $\prod_i \varepsilon_i^{a_i} = 1$ in $U_1$ is `IsPadicRelation K p ε a`, which spells out each
  $\mathbb{Z}_p$-power as a limit of integer powers using `PadicInt.appr`;
* that $\varepsilon_1, \dots, \varepsilon_r$ generate a subgroup of finite index in
  $\mathcal{O}_K^\times$ is `NumberField.Units.IsMaxRank ε` — such families exist inside $E_1$
  by `exists_isMaxRank_isPrincipalUnitAbove` — and the fundamental system of the elementary
  form is `NumberField.Units.fundSystem K`;
* the $p$-adic logarithm $\log_p$ is `NormedSpace.log`, vendored from
  [mathlib#43670](https://github.com/leanprover-community/mathlib4/pull/43670) as
  `FormalConjecturesForMathlib.Analysis.Normed.Algebra.Logarithm`, and the matrix
  $(\log_p \sigma(\varepsilon_i))_{i, \sigma}$ is `logMatrix K p ε`.

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

* $P$ is `NumberField.PrimesAbove K p`, and $U$ is `Mihailescu.SemilocalUnits K p`;
* $\iota$ is `Mihailescu.diagonalUnits K p`, and $\overline{E}$ is `Mihailescu.unitClosure K p`,
  the intersection written exactly as in the source;
* $\mathbb{Z}_p\text{-rk}$ is `Mihailescu.zpRankBelow`, which measures the rank from below by
  continuous injections of $\mathbb{Z}_p^n$ rather than with `Module.finrank`;
* $\mathcal{D}_L(K)$ is `Mihailescu.defect K p`.

*References:*
- [Wikipedia, *Leopoldt's conjecture*](https://en.wikipedia.org/wiki/Leopoldt%27s_conjecture):
  "Leopoldt's conjecture states that the $\mathbb{Z}_p$-module rank of the closure of $E_1$
  embedded diagonally in $U_1$ is also $r_1 + r_2 - 1$", and, in the lead, "Leopoldt's
  conjecture ... states that the $p$-adic regulator of a number field does not vanish. The
  $p$-adic regulator is an analogue of the usual regulator defined using $p$-adic logarithms
  instead of the usual logarithms".
- D. Nelson, *A Variation on Leopoldt's Conjecture: Some Local Units instead of All Local Units*,
  [arXiv:1308.4637](https://arxiv.org/abs/1308.4637), §3, Conjecture 3.1 (the same formulation,
  with $X = \Delta^{-1}(\prod_{\mathfrak{p} \mid p} \mathcal{O}^*_{\mathfrak{p}, 1})$ and the
  closure of $\Delta(X)$), and Lemma 4.2 (the reading of $\mathbb{Z}_p$-powers as limits of
  integer powers used here).
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
  \hat{\mathcal{O}}_\mathfrak{p}^\times$. The statement below needs no parity hypothesis: it
  works inside the *principal* units, whose $\mathbb{Z}_p$-module structure is unconditional.
- L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Springer 1997, Chapter 5, §5.5
  (*The $p$-adic regulator*): the definition of $R_p(K)$ as a determinant of $p$-adic logarithms
  of units, and the statement "Leopoldt's conjecture: $R_p(K) \neq 0$".
- J. Ax, *On the units of an algebraic number field*, Illinois J. Math. **9** (1965), 584-589, and
  A. Brumer, *On the units of algebraic number fields*, Mathematika **14** (1967), 121-124: the
  conjecture holds for abelian extensions of $\mathbb{Q}$.
-/

open Filter IsDedekindDomain NumberField NumberField.Units Topology

open scoped NumberField Valued

namespace Leopoldt

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/-
## The group $E_1$

Membership in $E_1$ is used by every formulation below, so it sits outside the sections, together
with the fact that $E_1$ contains a family of units of maximal rank: this is what keeps the
hypotheses of `leopoldt_conjecture.variants.padicRegulator` and
`leopoldt_conjecture.variants.padicRelation` from being vacuous.
-/

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

omit [NumberField K] in
/-- Reduction of the units of $\mathcal{O}_K$ modulo $d$, the map
$\mathcal{O}_K^\times \to (\mathcal{O}_K / d)^\times$. -/
noncomputable
def redUnits (d : 𝓞 K) : (𝓞 K)ˣ →* (𝓞 K ⧸ Ideal.span {d})ˣ :=
  Units.map (Ideal.Quotient.mk (Ideal.span {d}) : 𝓞 K →* 𝓞 K ⧸ Ideal.span {d})

omit [NumberField K] in
@[category API, AMS 11]
theorem redUnits_eq_one_iff (d : 𝓞 K) (u : (𝓞 K)ˣ) :
    redUnits K d u = 1 ↔ d ∣ (u : 𝓞 K) - 1 := by
  rw [redUnits, Units.ext_iff, Units.coe_map, Units.val_one, MonoidHom.coe_coe, ← sub_eq_zero,
    ← map_one (Ideal.Quotient.mk (Ideal.span {d})), ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

@[category API, AMS 11]
theorem exists_pow_sub_one_dvd :
    ∃ Q : ℕ, Q ≠ 0 ∧ ∀ u : (𝓞 K)ˣ, (p : 𝓞 K) ∣ ((u ^ Q : (𝓞 K)ˣ) : 𝓞 K) - 1 := by
  have := Ideal.finiteQuotientOfFreeOfNeBot (Ideal.span {(p : 𝓞 K)}) (by simp [NeZero.ne p])
  exact ⟨_, Nat.card_pos.ne',
    fun u ↦ (redUnits_eq_one_iff K _ _).1 ((map_pow _ u _).trans pow_card_eq_one')⟩


@[category API, AMS 11]
theorem isMaxRank_pow {ε : Fin (rank K) → (𝓞 K)ˣ} (hε : IsMaxRank ε) {Q : ℕ} (hQ : Q ≠ 0) :
    IsMaxRank (fun i ↦ ε i ^ Q) := by
  convert hε.units_smul fun _ ↦ Units.mk0 (Q : ℝ) (Nat.cast_ne_zero.2 hQ) using 1
  aesop

/--
The hypotheses of `leopoldt_conjecture.variants.padicRegulator` and
`leopoldt_conjecture.variants.padicRelation` can be satisfied: there is always a family of
$r_1 + r_2 - 1$ units of maximal rank which are principal units above $p$. Indeed, if $Q$ is the
order of the finite group $(\mathcal{O}_K / p\mathcal{O}_K)^\times$, then the $Q$-th powers of
a fundamental system of units will do.
-/
@[category API, AMS 11]
theorem exists_isMaxRank_isPrincipalUnitAbove :
    ∃ ε : Fin (rank K) → (𝓞 K)ˣ, IsMaxRank ε ∧ ∀ i, IsPrincipalUnitAbove K p (ε i) := by
  obtain ⟨Q, hQ0, hQ⟩ := exists_pow_sub_one_dvd K p
  exact ⟨fun i ↦ fundSystem K i ^ Q, isMaxRank_pow K (isMaxRank_fundSystem K) hQ0,
    fun i v hv ↦ Ideal.mem_of_dvd _ (hQ _) hv⟩

section Wikipedia_ModuleRank

/-
## The $\mathbb{Z}_p$-module rank formulation

Wikipedia's statement: the $\mathbb{Z}_p$-rank of the closure of $E_1$, embedded diagonally in
$U_1$, is $r_1 + r_2 - 1$.
-/

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
    suffices ((a * b : (𝓞 K)ˣ) : 𝓞 K) - 1 = (a : 𝓞 K) * ((b : 𝓞 K) - 1) + ((a : 𝓞 K) - 1) by
      simpa only [this] using Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hb v hv)) (ha v hv)
    simp; ring
  one_mem' v hv := by simp
  inv_mem' {a} ha v hv := by
    suffices ((a⁻¹ : (𝓞 K)ˣ) : 𝓞 K) - 1 = -((a⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * ((a : 𝓞 K) - 1) by
      simpa only [this] using Ideal.mul_mem_left _ _ (ha v hv)
    grind [Units.inv_mul]

omit [NumberField K] [Fact p.Prime] in
@[category API, AMS 11]
theorem mem_E₁_iff {u : (𝓞 K)ˣ} : u ∈ E₁ K p ↔ IsPrincipalUnitAbove K p u := Iff.rfl

/-- The diagonal embedding $E_1 \to U_1$, $\varepsilon \mapsto (\varepsilon)_{\mathfrak{p} \mid p}$
([Wikipedia]: "$E_1$ embedded diagonally in $U_1$"). -/
noncomputable def diag : Additive (E₁ K p) →+ U₁ K p where
  toFun u v := Additive.ofMul
    ⟨Units.map (algebraMap (𝓞 K) (v.1.adicCompletion K)).toMonoidHom (u.toMul : (𝓞 K)ˣ),
      OneUnits.mem_oneUnits_iff.2 (v.1.norm_algebraMap_sub_one_lt (u.toMul.2 v.1 v.2))⟩
  map_zero' := by
    funext v
    exact OneUnits.ext_of_coe (by simp)
  map_add' u w := by
    funext v
    exact OneUnits.ext_of_coe (by simp)

omit [Fact p.Prime] in
@[category API, AMS 11]
theorem coe_diag_apply (u : Additive (E₁ K p)) (v : PrimesAbove K p) :
    (((diag K p u v).toMul : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) =
      algebraMap (𝓞 K) (v.1.adicCompletion K) ((u.toMul : (𝓞 K)ˣ) : 𝓞 K) := rfl

/-- The closure $\overline{E_1}$ of the diagonal image of $E_1$ in $U_1$, as a
$\mathbb{Z}_p$-submodule of $U_1$ ([Wikipedia]: "the closure of $E_1$ embedded diagonally in
$U_1$"; [Nelson, §3]: "the topological closure of $\Delta(X)$ in
$\prod_{\mathfrak{p} \mid p} \mathcal{O}^*_{\mathfrak{p}, 1}$"). A closed subgroup of $U_1$ is
automatically a $\mathbb{Z}_p$-submodule. -/
noncomputable def closureE₁ : Submodule ℤ_[p] (U₁ K p) where
  toAddSubmonoid := (diag K p).range.topologicalClosure.toAddSubmonoid
  smul_mem' a x hx :=
    AddSubgroup.smul_mem_of_isClosed (AddSubgroup.isClosed_topologicalClosure _) hx
      (OneUnits.tendsto_appr_nsmul_pi a x)

@[category API, AMS 11]
theorem coe_closureE₁ : (closureE₁ K p : Set (U₁ K p)) = closure (Set.range (diag K p)) := by
  show ((diag K p).range.topologicalClosure : Set (U₁ K p)) = _
  rw [AddSubgroup.topologicalClosure_coe, AddMonoidHom.coe_range]

/--
**Leopoldt's conjecture.** Let $K$ be a number field and $p$ a prime. The $\mathbb{Z}_p$-rank of
the closure $\overline{E_1}$ of $E_1$ embedded diagonally in
$U_1 = \prod_{\mathfrak{p} \mid p} U_{1, \mathfrak{p}}$ is $r_1 + r_2 - 1$.

This is the statement of [Wikipedia] verbatim. The rank is `Module.rank`, the supremum of the
cardinalities of the $\mathbb{Z}_p$-linearly independent subsets of $\overline{E_1}$. Since
$U_1$ is a finitely generated $\mathbb{Z}_p$-module, so is its submodule $\overline{E_1}$, and
this is its free rank, at most $r_1 + r_2 - 1$. Using `Module.rank` rather than `Module.finrank`
avoids the junk value $0$ that the latter takes on modules of infinite rank, which is not ruled
out here.
-/
@[category research open, AMS 11]
theorem leopoldt_conjecture : Module.rank ℤ_[p] (closureE₁ K p) = rank K := by
  sorry

/--
**Ax–Brumer theorem.** Leopoldt's conjecture holds when $K$ is an abelian extension of
$\mathbb{Q}$. This is `leopoldt_conjecture` with the extra hypothesis `IsAbelianGalois ℚ K`.

Ax reduced the abelian case to a $p$-adic analogue of Baker's theorem on linear forms in
logarithms, which Brumer then proved.
-/
@[category research solved, AMS 11]
theorem leopoldt_conjecture.variants.abelian [IsAbelianGalois ℚ K] :
    Module.rank ℤ_[p] (closureE₁ K p) = rank K := by
  sorry

end Wikipedia_ModuleRank

section Wikipedia_Regulator

/-
## The $p$-adic regulator formulation

Wikipedia's lead sentence: the $p$-adic regulator of $K$ does not vanish. It is stated here as
the matrix of $p$-adic logarithms of the units having full rank, which is what non-vanishing of
a regulator amounts to without having to choose which minor to call *the* regulator.

### Design note: why the units are taken in $E_1$

The classical statement takes the logarithms of a fundamental system of units, using Iwasawa's
$p$-adic logarithm, which is defined on all of $\mathbb{C}_p^\times$ by $\log_p p = 0$ and
$\log_p x = \log_p(x^Q) / Q$ for any $Q \geq 1$ with $\|x^Q - 1\| < 1$. The logarithm available
here is `NormedSpace.log`, vendored from mathlib#43670: the series
$\sum_n (-1)^{n + 1} (x - 1)^n / n$, with the junk value $0$ wherever it diverges, and no
extension. For a unit $\varepsilon$ of $\mathcal{O}_K$ the series at $\sigma(\varepsilon)$
converges exactly when $\varepsilon \equiv 1$ modulo the prime $\mathfrak{p} \mid p$ that $\sigma$
induces, so on a fundamental system the entries would in general be junk and the statement
false, not merely weaker: for $K = \mathbb{Q}(\sqrt 2)$, $\varepsilon = 1 + \sqrt 2$ and $p = 3$
the $1 \times 2$ matrix is zero.

The hypothesis `IsPrincipalUnitAbove` in `leopoldt_conjecture.variants.padicRegulator` keeps every
$\sigma(\varepsilon_i)$ inside the disc of convergence, so the entries are honest logarithms;
`IsMaxRank` makes the rank independent of the family, so nothing is lost (see the docstring of
the statement); and `exists_isMaxRank_isPrincipalUnitAbove` shows that such families exist.

Dropping the hypothesis, i.e. stating the conjecture on `fundSystem K` with Iwasawa's logarithm,
depends on the following, none of which is in mathlib and all of which mathlib#43670 lists as
future work:

1. convergence of the series on $\|x - 1\| < 1$ in a complete ultrametric field of
   characteristic zero;
2. additivity $\log(xy) = \log x + \log y$ on that disc, hence $\log(x^n) = n \log x$;
3. the extension $\log_p x = \log_p(x^Q) / Q$, its independence of $Q$, and the fact that every
   unit of $\mathbb{C}_p$ has a power in the disc (its residue field is algebraic over
   $\mathbb{F}_p$).

Once they land, replace `NormedSpace.log` by the extended logarithm and state the conjecture on
`fundSystem K` with no hypotheses; this section then needs neither `IsMaxRank` nor
`IsPrincipalUnitAbove`.
-/

/--
The matrix $(\log_p \sigma(\varepsilon_i))_{i, \sigma}$ of $p$-adic logarithms of a family of
units $\varepsilon_1, \dots, \varepsilon_r$ of $K$, over all the embeddings
$\sigma : K \to \mathbb{C}_p$. Its rows are indexed by `Fin (rank K)` and its columns by
`K →+* ℂ_[p]`.

The logarithm is `NormedSpace.log`, the sum of $\sum_n (-1)^{n + 1} (x - 1)^n / n$, which takes
the junk value $0$ where that series diverges. The entries are genuine $p$-adic logarithms as
soon as each $\varepsilon_i$ is a principal unit at every prime above $p$: an embedding
$\sigma : K \to \mathbb{C}_p$ induces on $K$ the $\mathfrak{p}$-adic absolute value of the prime
$\mathfrak{p} \mid p$ it comes from, so $\|\sigma(\varepsilon_i) - 1\| < 1$ and the series
converges. This is why the statement below carries `IsPrincipalUnitAbove`; the design note at the
head of this section records what dropping it depends on.
-/
noncomputable def logMatrix (ε : Fin (rank K) → (𝓞 K)ˣ) :
    Matrix (Fin (rank K)) (K →+* ℂ_[p]) ℂ_[p] :=
  fun i σ ↦ NormedSpace.log (σ (ε i : K))

/--
**Leopoldt's conjecture, $p$-adic regulator form.** Let $K$ be a number field and $p$ a prime.
Let $\varepsilon_1, \dots, \varepsilon_r$, with $r = r_1 + r_2 - 1$, be units of $\mathcal{O}_K$
that generate a subgroup of finite index in $\mathcal{O}_K^\times$ and are principal units at
every prime above $p$, i.e. lie in $E_1$, and let $\sigma_1, \dots, \sigma_n$,
$n = [K : \mathbb{Q}]$, be the embeddings of $K$ into $\mathbb{C}_p$. Then the $r \times n$
matrix $(\log_p \sigma_j(\varepsilon_i))$ of $p$-adic logarithms has rank $r$.

Its rank is at most $r$, the number of rows, so this says that some $r \times r$ minor — a
$p$-adic regulator of $K$ — is nonzero, which is [Wikipedia]'s "the $p$-adic regulator of a
number field does not vanish". For totally real $K$ one has $n = r + 1$ and each row sums to
$\log_p N_{K/\mathbb{Q}}(\varepsilon_i) = \log_p(\pm 1) = 0$, so the $n$ minors agree up to sign
and the statement is Leopoldt's original $R_p(K) \neq 0$ [Washington, §5.5]; for general $K$ the
rank formulation avoids choosing a minor.

The rank does not depend on the family: two families of maximal rank differ by a matrix over
$\mathbb{Z}$ that is invertible over $\mathbb{Q}$, and $\log_p$ turns the passage from
$\varepsilon_i$ to $\varepsilon_i^Q$ into multiplication of a row by $Q$. Taking the
$\varepsilon_i$ inside $E_1$ costs nothing for the same reason, and is what keeps the entries in
the disc where the logarithmic series converges.
-/
@[category research open, AMS 11]
theorem leopoldt_conjecture.variants.padicRegulator (ε : Fin (rank K) → (𝓞 K)ˣ)
    (hmax : IsMaxRank ε) (hone : ∀ i, IsPrincipalUnitAbove K p (ε i)) :
    (logMatrix K p ε).rank = rank K := by
  sorry

end Wikipedia_Regulator

section LowLevel

/-
## The low-level formulations

Two forms of the conjecture stated with nothing beyond mathlib: that the only $p$-adic relation
among units of maximal rank in $E_1$ is the trivial one, and an elementary form in which
congruences modulo $p^M \mathcal{O}_K$ force divisibility of the exponents. Both are equivalent
to `leopoldt_conjecture` above.
-/

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
    Tendsto (fun n : ℕ ↦ ((∏ i, (ε i : K) ^ (a i).appr n : K) : v.adicCompletion K)) atTop (nhds 1)

/--
**Leopoldt's conjecture, $p$-adic-relation form.** Let $K$ be a number field and $p$ a prime. Let
$\varepsilon_1, \dots, \varepsilon_r$, with $r = r_1 + r_2 - 1$, be units of $\mathcal{O}_K$ that
generate a subgroup of finite index in $\mathcal{O}_K^\times$ and are principal units at every
prime above $p$, i.e. lie in $E_1$. Then the only $a \in \mathbb{Z}_p^r$ with
$\prod_i \varepsilon_i^{a_i} = 1$ in every completion $K_\mathfrak{p}$ with $\mathfrak{p} \mid p$
is $a = 0$.

In other words, the map $\varphi_\varepsilon : \mathbb{Z}_p^r \to U_1$,
$a \mapsto \prod_i \varepsilon_i^{a_i}$, is injective. Its image has finite index in the closure
$\overline{E_1}$ of $E_1$ in $U_1$, so
$\operatorname{rank}_{\mathbb{Z}_p} \overline{E_1} = r - \operatorname{rank}_{\mathbb{Z}_p}
\ker \varphi_\varepsilon$, and injectivity is equivalent to `leopoldt_conjecture`, i.e. to the
vanishing of the Leopoldt defect.
-/
@[category research open, AMS 11]
theorem leopoldt_conjecture.variants.padicRelation (ε : Fin (rank K) → (𝓞 K)ˣ)
    (hmax : IsMaxRank ε) (hone : ∀ i, IsPrincipalUnitAbove K p (ε i))
    {a : Fin (rank K) → ℤ_[p]} (ha : IsPadicRelation K p ε a) : a = 0 := by
  sorry

/--
**Leopoldt's conjecture, elementary form.** Let $K$ be a number field, $p$ a prime, $r$ the rank
of the unit group of $K$, and $\varepsilon_1, \dots, \varepsilon_r$ the fundamental system
`fundSystem K`. For every $N$ there is an $M$ such that any $n \in \mathbb{Z}^r$ with
$\prod_i \varepsilon_i^{n_i} \equiv 1 \pmod{p^M \mathcal{O}_K}$ has all its $n_i$ divisible by
$p^N$.

This says that the topology induced on $\mathcal{O}_K^\times$ (modulo torsion) by
$\prod_{\mathfrak{p} \mid p} \mathcal{O}_\mathfrak{p}^\times$ is the $p$-adic topology, which is
equivalent to injectivity of $\mathcal{O}_K^\times \otimes \mathbb{Z}_p \to
\prod_{\mathfrak{p} \mid p} \mathcal{O}_\mathfrak{p}^\times$, i.e. to `leopoldt_conjecture`.
-/
@[category research open, AMS 11]
theorem leopoldt_conjecture.variants.elementary (N : ℕ) :
    ∃ M : ℕ, ∀ n : Fin (rank K) → ℤ,
      (p : 𝓞 K) ^ M ∣ ((∏ i, fundSystem K i ^ n i : (𝓞 K)ˣ) : 𝓞 K) - 1 →
      ∀ i, (p : ℤ) ^ N ∣ n i := by
  sorry

end LowLevel

section Mihailescu_Defect

/-
## Mihăilescu's form

The vanishing of the Leopoldt defect
$\mathcal{D}_L(K) = \mathbb{Z}\text{-rk}(E) - \mathbb{Z}_p\text{-rk}(\overline{E})$ of
[Mihăilescu, §1.1]. Unlike the formulations above this one works inside the full semilocal unit
group $U = \prod_{\mathfrak{p} \mid p} \mathcal{O}_\mathfrak{p}^\times$ rather than the
principal units $U_1$; the module docstring carries its dictionary.
-/

namespace Mihailescu

/-- `U`: the group of semilocal units at `p`, that is the product `∏_{℘ | p} 𝓞_℘^×` of the
local units at the primes above `p`. -/
abbrev SemilocalUnits := ∀ v : PrimesAbove K p, (v.1.adicCompletionIntegers K)ˣ

/-- `ι : E(K) → U`, the diagonal embedding of the global units into the semilocal units. -/
noncomputable
def diagonalUnits : (𝓞 K)ˣ →* SemilocalUnits K p :=
  MonoidHom.pi fun v ↦ Units.map (algebraMap (𝓞 K) (v.1.adicCompletionIntegers K)).toMonoidHom

/-- `Ē = ⋂_{n > 0} ι(E) · U^{p^n}`, the `p`-adic closure of the image of the global units
inside the semilocal units, exactly as the intersection is written in the source. -/
noncomputable
def unitClosure : Subgroup (SemilocalUnits K p) :=
  ⨅ n : ℕ, ((diagonalUnits K p).range ⊔ (powMonoidHom (p ^ (n + 1))).range)

/-- The free `ℤ_p`-rank of a subgroup `H` of a commutative topological group, computed as the
largest `n ≤ bound` for which `ℤ_p^n` admits a continuous injective homomorphism into `H`.

For a closed subgroup of the semilocal units this is the usual free `ℤ_p`-rank: such a subgroup
is isomorphic to `Δ × ℤ_p^d` with `Δ` finite, and continuous injections from `ℤ_p^n` exist
exactly for `n ≤ d`. Continuity is essential — as abstract groups `ℤ_p^n` embeds into `ℤ_p`
for every `n`; and since `ℤ_p^n` is compact and the target Hausdorff, a continuous injection is
automatically a closed embedding.

The `bound` is carried only so that the supremum is visibly taken over a bounded set and never
falls back on the junk value of `sSup` on an unbounded set of naturals. Any `bound` at least as
large as the true rank yields the true rank. -/
noncomputable
def zpRankBelow {G : Type*} [CommGroup G] [TopologicalSpace G] (bound : ℕ) (H : Subgroup G) : ℕ :=
  sSup {n : ℕ | n ≤ bound ∧ ∃ f : Multiplicative (Fin n → ℤ_[p]) →* G,
    Function.Injective f ∧ Continuous f ∧ ∀ x, f x ∈ H}

/-- The **Leopoldt defect** `𝒟_L(K) = ℤ-rk(E) - ℤ_p-rk(Ē)` of `K` at `p`.

`ℤ-rk(E) = r₁ + r₂ - 1` is Dirichlet's unit rank, which mathlib provides as
`NumberField.Units.rank`. The `ℤ_p`-rank of `Ē` is bounded by that of the whole semilocal unit
group `U`, which is `[K : ℚ]`, so taking `[K : ℚ]` as the bound never constrains it. -/
noncomputable
def defect : ℕ := rank K - zpRankBelow p (Module.finrank ℚ K) (unitClosure K p)

end Mihailescu

/--
**Leopoldt's conjecture, Mihăilescu's form.** Let $K$ be a number field and $p$ a prime. The
Leopoldt defect $\mathcal{D}_L(K) = \mathbb{Z}\text{-rk}(E) -
\mathbb{Z}_p\text{-rk}(\overline{E})$ of [Mihăilescu, §1.1] vanishes, $\overline{E}$ being the
closure of the global units in the semilocal units $U$.

Since $\overline{E}$ has $\mathbb{Z}_p$-rank at most $\mathbb{Z}\text{-rk}(E) = r_1 + r_2 - 1$,
this says that the two ranks agree, which is `leopoldt_conjecture` read inside $U$ instead of
$U_1$; the two are equivalent because $U_1$ has finite index in $U$.
-/
@[category research open, AMS 11]
theorem leopoldt_conjecture.variants.mihailescu : Mihailescu.defect K p = 0 := by
  sorry

end Mihailescu_Defect

end Leopoldt
