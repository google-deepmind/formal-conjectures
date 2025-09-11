/-
Copyright 2025 Google LLC

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

-- arXiv URL: https://arxiv.org/pdf/2409.15185
import FormalConjectures.Util.ProblemImports

open Polynomial

open scoped Topology

namespace Arxiv.id240915185

section Prelims

/--
Let $\mathcal{L} = \{L_1,\ldots,L_K\}$ be a set of polynomials, where the coefficients
$a_k,b_k$ are positive integers. For a prime $p$, let $\omega_\mathcal{L}(p)$ denote
the number of roots of $\prod_{k=1}^K L_k(n)$ modulo $p$.
-/
noncomputable def ω {ι : Type*} [Fintype ι]
    (L : ι → Polynomial ℤ) (p : ℕ) [Fact (p.Prime)] : ℕ :=
  (∏ i, (L i).map (Int.castRingHom (ZMod p))).roots.card

/--
Let $\mathcal{L} = \{L_1,\ldots,L_K\}$ be a set of distinct linear forms
$L_k(n) = a_kn+b_k$, where the coefficients $a_k,b_k$ are positive integers.
We say $\mathcal{L}$ is \emph{admissible} if $\omega_\mathcal{L}(p) < p$ for
every prime $p$.
-/
structure AdmissibleLinearForm (ι : Type*) [Fintype ι] where
  L : ι → Polynomial ℤ
  linear (i : ι) : (L i).natDegree = 1
  pos (i : ι) : 0 < (L i).coeff 0 ∧ 0 < (L i).coeff 1
  injective : L.Injective
  admissible (p : ℕ) [Fact (p.Prime)] : ω L p < p

instance (ι : Type*) [Fintype ι] : FunLike (AdmissibleLinearForm ι) ι (Polynomial ℤ) where
  coe := AdmissibleLinearForm.L
  coe_injective' ℒ₁ ℒ₂ h := by cases ℒ₁; congr

/--
Let $\mathcal{L} = \{L_1,\ldots,L_K\}$ be a set of distinct linear forms
$L_k(n) = a_kn+b_k$, where the coefficients $a_k,b_k$ are positive integers.
We say $\mathcal{L}$ is \emph{bounded admissible} for some $u\in\mathbb{R}$
if it is admissible, $a_k, b_k\leq u$ for all $k$, and $K\leq\log(u)$.
-/
structure BddAdmissibleLinearForm (ι : Type*) [Fintype ι] (u : ℝ) extends AdmissibleLinearForm ι where
  coeff_le (i : ι) : (L i).coeff 0 ≤ u ∧ (L i).coeff 1 ≤ u
  card_le : Fintype.card ι ≤ u.log

instance (ι : Type*) [Fintype ι] (u : ℝ) : FunLike (BddAdmissibleLinearForm ι u) ι (Polynomial ℤ) where
  coe ℒ := (BddAdmissibleLinearForm.toAdmissibleLinearForm ℒ).L
  coe_injective' ℒ₁ ℒ₂ h := by
    rcases ℒ₁ with ⟨⟨_, _⟩, _⟩; congr

/--
Let $\mathcal{L} = \{L_1,\ldots,L_K\}$ be an admissible set of linear forms,
where $L_k(n) = a_kn+b_k$ with the $a_k,b_k$ positive integers. Define the
singular series
\begin{align*}
\mathfrak{S}(\mathcal{L}) =
  \prod_p \left(1 - \frac{\omega_\mathcal{L}(p)}{p} \right) \left(1 - \frac{1}{p} \right)^{-K}.
\end{align*}
-/
noncomputable def 𝔖 {ι : Type*} [Fintype ι] {u : ℝ}
    -- We will only apply this to bounded admissible forms later
    (ℒ : BddAdmissibleLinearForm ι u) : ℝ :=
  -- TODO(mercuris) : is `tprod` OK here? Alternatively, define this up to `n` and
  -- take limits when used later.
  ∏' (p : Subtype Nat.Prime),
    have : Fact (p.1.Prime) := ⟨p.2⟩
    (1 - ω ℒ p / p) * (1 - 1 / p) ^ Fintype.card ι

end Prelims

section PrimeKTuples

/--
[Prime $K$-tuples conjecture]
Let $\mathcal{L} = \{L_1,\ldots,L_K\}$ be an admissible set of linear forms.
Then there are infinitely many integers $n$ such that $L_1(n),\ldots,L_K(n)$
are all prime.
-/
@[problem_status open]
theorem conjecture_1_1 {ι : Type*} [Fintype ι] (ℒ : AdmissibleLinearForm ι) :
    { n | 0 < n ∧ ∀ i, (ℒ i).eval n |>.natAbs.Prime }.Infinite :=
  sorry

end PrimeKTuples

section QuantitativePrimeKTuples

open Filter in
/--
[Quantitative prime $K$-tuples conjecture]
Let $\mathcal{L} = \{L_1,\ldots,L_K\}$ be an admissible set of linear forms,
where $L_k(n) = a_kn+b_k$ with the $a_k,b_k$ positive integers.
If $x$ is sufficiently large, if $a_k,b_k \leq (\log \log x)^{100}$, and if
$K \leq 100\log \log \log x$, then
\begin{align*}
\sum_{\substack{n\leq x \\ L_k(n) \textup{ is prime for }1\leq k \leq K}} 1
  =(1+o(1)) \mathfrak{S}(\mathcal{L}) \frac{x}{(\log x)^K},
\end{align*}
where $o(1)$ denotes a quantity which goes to zero as $x$ goes to infinity.
-/
abbrev QuantitativePrimeKTuples :=
  ∀ᶠ (x : ℝ) in atTop,
    ∀ (ι : Type*) [Fintype ι] (ℒ : BddAdmissibleLinearForm ι (x.log.log ^ 100)),
      ∃ (o : ℝ → ℝ) (_ : Tendsto o atTop (𝓝 0)),
  { n : ℤ | 0 < n ∧ n ≤ x ∧ ∀ i, (ℒ i).eval n |>.natAbs.Prime }.ncard =
    (1 + o x) * 𝔖 ℒ * x / x.log ^ Fintype.card ι

/--
[Quantitative prime $K$-tuples conjecture]
Let $\mathcal{L} = \{L_1,\ldots,L_K\}$ be an admissible set of linear forms,
where $L_k(n) = a_kn+b_k$ with the $a_k,b_k$ positive integers.
If $x$ is sufficiently large, if $a_k,b_k \leq (\log \log x)^{100}$, and if
$K \leq 100\log \log \log x$, then
\begin{align*}
\sum_{\substack{n\leq x \\ L_k(n) \textup{ is prime for }1\leq k \leq K}}
  =(1+o(1)) \mathfrak{S}(\mathcal{L}) \frac{x}{(\log x)^K},
\end{align*}
where $o(1)$ denotes a quantity which goes to zero as $x$ goes to infinity.
-/
@[problem_status open]
theorem conjecture_1_2 : QuantitativePrimeKTuples := sorry

end QuantitativePrimeKTuples

open scoped ArithmeticFunction in
/--
Assume Conjecture 1.2. Then, for every integer $t\geq 2$, the number
\begin{align}
\sum_{n\geq 1} \frac{\omega(n)}{t^n}
\end{align}
is irrational.
-/
@[problem_status solved]
theorem conditional_erdos_69 {t : ℕ} (ht : 2 ≤ t) (h : QuantitativePrimeKTuples) :
    Irrational <| ∑' n, ω (n + 1) / t ^ n :=
  sorry

end Arxiv.id240915185
