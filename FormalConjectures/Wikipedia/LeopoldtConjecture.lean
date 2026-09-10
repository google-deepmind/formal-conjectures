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
* $\operatorname{rank}_{\mathbb{Z}_p} \overline{E_1}$ is `Module.rank ℤ_[p] (closureE₁ K p)`.

*References:*
- [Wikipedia, *Leopoldt's conjecture*](https://en.wikipedia.org/wiki/Leopoldt%27s_conjecture):
  "Leopoldt's conjecture states that the $\mathbb{Z}_p$-module rank of the closure of $E_1$
  embedded diagonally in $U_1$ is also $r_1 + r_2 - 1$".
- D. Nelson, *A Variation on Leopoldt's Conjecture: Some Local Units instead of All Local Units*,
  [arXiv:1308.4637](https://arxiv.org/abs/1308.4637), §3, Conjecture 3.1 (the same formulation,
  with $X = \Delta^{-1}(\prod_{\mathfrak{p} \mid p} \mathcal{O}^*_{\mathfrak{p}, 1})$ and the
  closure of $\Delta(X)$), and Lemma 4.2 (the reading of $\mathbb{Z}_p$-powers as limits of
  integer powers used here).
- G. Gras et al., *Applications of representation theory and of explicit units to Leopoldt's
  conjecture*, [arXiv:2301.05700](https://arxiv.org/abs/2301.05700), §1: Leopoldt's conjecture
  holds iff $\lambda_{K, p} : \mathbb{Z}_p \otimes_{\mathbb{Z}} \mathcal{O}_K^\times \to
  \prod_{\mathfrak{p} \mid p} U_{1, \mathfrak{p}}$ is injective, iff $\delta(K, p) = 0$.
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer 2008,
  Theorem 10.3.6: for odd $p$, the conjecture is equivalent to injectivity of
  $\mathcal{O}_K^\times \otimes \mathbb{Z}_p \to \prod_{\mathfrak{p} \mid p}
  \hat{\mathcal{O}}_\mathfrak{p}^\times$. The statement below needs no parity hypothesis: it
  works inside the *principal* units, whose $\mathbb{Z}_p$-module structure is unconditional.
- J. Ax, *On the units of an algebraic number field*, Illinois J. Math. **9** (1965), 584-589, and
  A. Brumer, *On the units of algebraic number fields*, Mathematika **14** (1967), 121-124: the
  conjecture holds for abelian extensions of $\mathbb{Q}$.
-/

open Filter IsDedekindDomain NumberField NumberField.Units Topology

open scoped NumberField Valued

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

end Leopoldt
