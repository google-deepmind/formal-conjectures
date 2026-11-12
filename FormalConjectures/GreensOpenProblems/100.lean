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
module

public import FormalConjecturesUtil

/-!
# Ben Green's Open Problem 100

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.100)
- [Pe08] Pestov, V. G., *Hyperlinear and sofic groups: a brief guide*. Bull. Symbolic Logic 14
  (2008), 449--480. [arXiv:0804.3968](https://arxiv.org/abs/0804.3968)
- [HJ19] Helfgott, H. A. and Juschenko, K., *Soficity, short cycles, and the Higman group*.
  Trans. Amer. Math. Soc. 371 (2019), 2771--2795.
  [arXiv:1512.02135](https://arxiv.org/abs/1512.02135)
- [Op26] OpenAI, *Non-sofic groups exist* (2026).
  https://openai.com/index/ten-advances-in-mathematics/
- [FF26] Fournier-Facio, F., *A torsion-free non-sofic group* (2026).
  [arXiv:2608.02025](https://arxiv.org/abs/2608.02025)
- [KT26] Kun, G. and Thom, A., *Nonsofic wreath products of residually finite groups* (2026).
  [arXiv:2608.06222](https://arxiv.org/abs/2608.06222)
- [Ec26] Eckhardt, C., *Non-MF groups and non-finite full group C\*-algebras* (2026).
  [arXiv:2608.28772](https://arxiv.org/abs/2608.28772)
- [Li26] Liu, J., *Nonhyperlinear groups exist* (2026).
  https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf
-/

@[expose] public section

namespace Green100

/--
The normalised Hamming distance $d(\sigma, \tau) = \frac{1}{n} \#\{i : \sigma(i) \ne \tau(i)\}$ on
the symmetric group $\mathrm{Sym}(n)$ [Pe08, Example 2.3].
-/
noncomputable def hammingDistNorm {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : ℝ :=
  (hammingDist (⇑σ) (⇑τ) : ℝ) / n

/--
The normalised Hilbert–Schmidt distance
$\|u - v\|_2 = \big(\frac{1}{n} \sum_{i, j} |u_{ij} - v_{ij}|^2\big)^{1/2}$ on the unitary group
$U(n)$, normalised so that the identity matrix has norm $1$ [Pe08, Example 2.7].
-/
noncomputable def hsDist {n : ℕ} (u v : Matrix.unitaryGroup (Fin n) ℂ) : ℝ :=
  Real.sqrt ((∑ i, ∑ j,
    ‖(u : Matrix (Fin n) (Fin n) ℂ) i j - (v : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2) / n)

/--
The distance $\|u - v\|$ on the unitary group $U(n)$ for the $\ell^2$-to-$\ell^2$ operator norm.
-/
noncomputable def opDist {n : ℕ} (u v : Matrix.unitaryGroup (Fin n) ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
    ((u : Matrix (Fin n) (Fin n) ℂ) - (v : Matrix (Fin n) (Fin n) ℂ))‖

/--
A group $G$ is *sofic* if for every finite $F \subseteq G$ and every $\varepsilon > 0$ there are
$n$ and a map $\theta : F \to \mathrm{Sym}(n)$ such that
$d(\theta(g)\theta(h), \theta(gh)) < \varepsilon$ whenever $g, h, gh \in F$,
$d(\theta(e), \mathrm{Id}) < \varepsilon$ if $e \in F$, and $d(\theta(x), \theta(y)) \ge 1/4$ for
all distinct $x, y \in F$. Here $d$ is the normalised Hamming distance.

This is the characterisation of [Pe08, Theorem 3.5]. Only the values of `θ` on `F` matter.
-/
def IsSofic (G : Type*) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (θ : G → Equiv.Perm (Fin n)),
    (∀ g ∈ F, ∀ h ∈ F, g * h ∈ F → hammingDistNorm (θ g * θ h) (θ (g * h)) < ε) ∧
    (1 ∈ F → hammingDistNorm (θ 1) 1 < ε) ∧
    ∀ x ∈ F, ∀ y ∈ F, x ≠ y → (1 / 4 : ℝ) ≤ hammingDistNorm (θ x) (θ y)

/--
A group $G$ is *hyperlinear* if for every finite $F \subseteq G$ and every $\varepsilon > 0$ there
are $n$ and a map $\theta : F \to U(n)$ such that
$\|\theta(g)\theta(h) - \theta(gh)\|_2 < \varepsilon$ whenever $g, h, gh \in F$,
$\|\theta(e) - \mathrm{Id}\|_2 < \varepsilon$ if $e \in F$, and
$\|\theta(x) - \theta(y)\|_2 \ge 1/4$ for all distinct $x, y \in F$. Here $\|\cdot\|_2$ is the
normalised Hilbert–Schmidt norm.

This is the characterisation of [Pe08, Theorem 3.6]. Only the values of `θ` on `F` matter.
-/
def IsHyperlinear (G : Type*) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (θ : G → Matrix.unitaryGroup (Fin n) ℂ),
    (∀ g ∈ F, ∀ h ∈ F, g * h ∈ F → hsDist (θ g * θ h) (θ (g * h)) < ε) ∧
    (1 ∈ F → hsDist (θ 1) 1 < ε) ∧
    ∀ x ∈ F, ∀ y ∈ F, x ≠ y → (1 / 4 : ℝ) ≤ hsDist (θ x) (θ y)

/--
The property of a group $G$ in the precise statement of [Gr24]: for every finite $A \subseteq G$
containing the identity and every $\varepsilon > 0$ there are $n$ and a map $\phi : A \to U(n)$
with $\phi(e) = I_n$, $\|\phi(a_1 a_2) - \phi(a_1)\phi(a_2)\| < \varepsilon$ whenever
$a_1, a_2, a_1 a_2 \in A$, and $\|\phi(a) - I_n\| \ge 1$ for $a \in A$, $a \ne e$. Here
$\|\cdot\|$ is the $\ell^2$-to-$\ell^2$ operator norm.
-/
def OperatorNormApprox (G : Type*) [Group G] : Prop :=
  ∀ A : Finset G, 1 ∈ A → ∀ ε : ℝ, 0 < ε →
    ∃ (n : ℕ) (φ : G → Matrix.unitaryGroup (Fin n) ℂ), φ 1 = 1 ∧
      (∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ * a₂ ∈ A → opDist (φ (a₁ * a₂)) (φ a₁ * φ a₂) < ε) ∧
      ∀ a ∈ A, a ≠ 1 → 1 ≤ opDist (φ a) 1

/--
The Higman group
$\langle a_1, a_2, a_3, a_4 \mid a_i^{a_{i+1}} = a_i^2,\ i \in \mathbb{Z}/4\mathbb{Z} \rangle$,
where $x^y = y^{-1} x y$. The generators are indexed by `ZMod 4`.
-/
abbrev HigmanGroup : Type :=
  PresentedGroup (Set.range fun i : ZMod 4 ↦
    (FreeGroup.of (i + 1))⁻¹ * FreeGroup.of i * FreeGroup.of (i + 1) * (FreeGroup.of i ^ 2)⁻¹)

/--
Is every group well-approximated by finite groups? There are really two questions here, namely
is every group sofic? and is every group hyperlinear? This is the first one: is every group sofic?

We use the characterisation of soficity in [Pe08, Theorem 3.5], see `IsSofic`. It only involves
finite subsets, so a group is sofic if all its finitely generated subgroups are. These are
countable, so it is enough to quantify over groups in `Type`.

[Gr24] lists this as open. The answer is no: OpenAI announced in 2026 that the unit group of the
binary Leavitt algebra is not sofic [Op26], and Fournier-Facio [FF26, Theorem 1.3] gives a
finitely presented torsion-free non-sofic group, using a criterion from [Op26]. Kun and Thom
[KT26] give further non-sofic groups. These results are in 2026 preprints.
-/
@[category research solved, question, AMS 20]
theorem green_100.parts.i : ¬ ∀ (G : Type) [Group G], IsSofic G := by
  sorry

/--
Is every group well-approximated by finite groups? There are really two questions here, namely
is every group sofic? and is every group hyperlinear? This is the second one: is every group
hyperlinear?

We use the characterisation of hyperlinearity in [Pe08, Theorem 3.6], see `IsHyperlinear`, with
the normalised Hilbert–Schmidt norm. [Gr24] gives a precise form of this question with the
operator norm instead, see `green_100.variants.operator_norm`. As for `green_100.parts.i`, it is
enough to quantify over groups in `Type`.

[Gr24] lists this as open. The answer is no: Liu [Li26, Theorem 1.1] constructs a countable group,
a wreath product, that is not hyperlinear. This is a 2026 preprint.
-/
@[category research solved, question, AMS 20 46]
theorem green_100.parts.ii : ¬ ∀ (G : Type) [Group G], IsHyperlinear G := by
  sorry

/--
Suppose that $G$ is a group. Is the following true? For every finite set $A \subset G$ containing
the identity $e_G$ and for every $\varepsilon > 0$, there is some unitary group $U(n)$ and a map
$\phi : A \to U(n)$ such that $\phi(e_G) = I_n$, such that $\phi$ is an 'approximate
homomorphism' in the sense that $\|\phi(a_1 a_2) - \phi(a_1)\phi(a_2)\| < \varepsilon$ for all
$a_1, a_2 \in A$ such that $a_1 a_2 \in A$, whilst $\phi$ is 'nontrivial' in the sense that
$\|\phi(a) - I_n\| \ge 1$ for all $a \in A$, $a \ne e_G$. (Here $\|-\|$ is the
$\ell^2$-to-$\ell^2$ operator norm.)

[Gr24] gives this as a precise statement of `green_100.parts.ii`. In [Pe08], hyperlinearity uses
the normalised Hilbert–Schmidt norm, and approximation in the operator norm defines a class of
groups whose relation to hyperlinear groups was open there [Pe08, Remark 8.6 and Question 8.7];
these are now usually called MF groups. We state the question as written, with the operator
norm, for every group.

[Gr24] lists this as open. The answer is no. Exhausting a countable group by finite sets
containing the identity, with errors tending to zero, the maps $\phi$ give a homomorphism into the
unitary group of $\prod_k M_{n_k}(\mathbb{C}) / \bigoplus_k M_{n_k}(\mathbb{C})$, which is
injective by the bound $\|\phi(a) - I_n\| \ge 1$. So every countable group with this property is
MF in the sense of [Ec26, Definition 4.1]. Eckhardt [Ec26, Theorem 4.3 and Examples 3.2 and 4.5]
gives a countable group that is not MF, built from a property (T) group such as
$\mathbb{Z}^3 \rtimes \mathrm{SL}_3(\mathbb{Z})$. This is a 2026 preprint.
-/
@[category research solved, question, AMS 20 46]
theorem green_100.variants.operator_norm :
    ¬ ∀ (G : Type) [Group G], OperatorNormApprox G := by
  sorry

/--
Every sofic group is hyperlinear [Pe08, Theorem 3.3], a result of Elek and Szabó. The converse is
not known [Gr24].
-/
@[category research solved, AMS 20 46]
theorem green_100.variants.sofic_isHyperlinear (G : Type*) [Group G] (hG : IsSofic G) :
    IsHyperlinear G := by
  sorry

/-- Every residually finite group is sofic [Pe08, Example 4.2]. -/
@[category research solved, AMS 20]
theorem green_100.variants.residuallyFinite_isSofic (G : Type*) [Group G]
    [Group.ResiduallyFinite G] : IsSofic G := by
  sorry

/--
Is the Higman group sofic? [Gr24] notes that the Higman group is not known to be either
hyperlinear or sofic.
-/
@[category research open, question, AMS 20]
theorem green_100.variants.higman_isSofic : IsSofic HigmanGroup := by
  sorry

/--
Is the Higman group hyperlinear? [Gr24] notes that the Higman group is not known to be either
hyperlinear or sofic.
-/
@[category research open, question, AMS 20 46]
theorem green_100.variants.higman_isHyperlinear : IsHyperlinear HigmanGroup := by
  sorry

/--
**Helfgott and Juschenko.** If the Higman group is sofic, then for every $\varepsilon > 0$ there
is $N$ such that for every odd $n \ge N$ there is a bijection $f : \mathbb{Z}/n\mathbb{Z} \to
\mathbb{Z}/n\mathbb{Z}$ with $f(x + 1) = 2 f(x)$ for at least $(1 - \varepsilon) n$ values of $x$
and $f(f(f(f(x)))) = x$ for all $x$ [HJ19, Theorem 2, case $m = 2$]. The last condition already
makes $f$ a bijection. [HJ19] presents the Higman group with the order of the generators
reversed, which gives an isomorphic group.
-/
@[category research solved, AMS 11 20]
theorem green_100.variants.helfgott_juschenko :
    IsSofic HigmanGroup → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n.Coprime 2 →
      ∃ f : ZMod n → ZMod n, (1 - ε) * n ≤ Set.ncard {x | f (x + 1) = 2 * f x} ∧
        ∀ x, f (f (f (f x))) = x := by
  sorry

end Green100
