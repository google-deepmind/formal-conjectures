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
# Erdős Problem 1184

*References:*
- [erdosproblems.com/1184](https://www.erdosproblems.com/1184)
- [Er76e] Erdős, P., *Problems and results on consecutive integers*. Publ. Math. Debrecen 23
  (1976), 271-282. [DOI](https://doi.org/10.5486/PMD.1976.23.3-4.15)
-/

@[expose] public section

open Filter
open scoped Topology

namespace Erdos1184

/-- $f(n,k)$ is the number of $1\le i\le k$ such that $P(n+i)>k$, where $P(m)$ is the largest
prime divisor of $m$ (`Nat.maxPrimeFac`).

Here $n+i\ge 1$. The junk value `Nat.maxPrimeFac 1 = 1` is never $>k$ for $k\ge 1$, and for
$k=0$ the range of $i$ is empty, so no junk value is reached. -/
def f (n k : ℕ) : ℕ :=
  ((Finset.Icc 1 k).filter fun i => k < (n + i).maxPrimeFac).card

/-- $f(n,k)$ counts a subset of $\{1,\ldots,k\}$, so $f(n,k)\le k$. -/
@[category test, AMS 11]
theorem f_le (n k : ℕ) : f n k ≤ k := by
  unfold f
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- `ρ` is a Dickman function: it is continuous on $[0,\infty)$, equal to $1$ on $[0,1]$, and
$$u\rho(u)=\int_{u-1}^{u}\rho(t)\,\mathrm{d}t\qquad(u\ge 1).$$
For $u>1$ this is equivalent to the delay differential equation $u\rho'(u)=-\rho(u-1)$. There
is exactly one such function on $[0,\infty)$, the Dickman function: on $[1,2]$ it is
$1-\log u$, and the identity determines it step by step on $[n,n+1]$. Its values on
$(-\infty,0)$ are not constrained and never used. -/
def IsDickman (ρ : ℝ → ℝ) : Prop :=
  ContinuousOn ρ (Set.Ici 0) ∧ (∀ u ∈ Set.Icc (0 : ℝ) 1, ρ u = 1) ∧
    ∀ u : ℝ, 1 ≤ u → u * ρ u = ∫ t in (u - 1)..u, ρ t

/-- A Dickman function takes the value $1$ at $1$. -/
@[category API, AMS 11]
theorem IsDickman.apply_one {ρ : ℝ → ℝ} (h : IsDickman ρ) : ρ 1 = 1 :=
  h.2.1 1 ⟨zero_le_one, le_rfl⟩

/--
Let $f(n,k)$ count the number of $1\leq i\leq k$ such that $P(n+i)>k$ (where $P(m)$ is the
largest prime divisor of $m$). Is it true that, if $\alpha>1$ is such that $n=k^{\alpha+o(1)}$,
then
$$f(n,k)=(1-\rho(\alpha)+o(1))k,$$
where $\rho$ is the Dickman function?

Erdős [Er76e, p. 272] writes that it seems certain that $f(n,k)=(1-c_\alpha+o(1))k$ for
$\log n=(\alpha+o(1))\log k$, where $U(k^\alpha,k)=(c_\alpha+o(1))k^\alpha$ and $U(x,k)$ counts the
$m\leq x$ with $P(m)\leq k$; so $c_\alpha=\rho(\alpha)$. He also reports that Ramachandra, Shorey
and Tijdeman proved $f(n,k)\geq k-\pi(k)$ for $n>\exp(c(\log k)^2)$.

We read $n=k^{\alpha+o(1)}$ as: $n=n(k)$ is any function of
$k$ with $\log n(k)/\log k\to\alpha$. The conclusion is $f(n(k),k)/k\to 1-\rho(\alpha)$. This is
equivalent to the uniform statement: for every $\varepsilon>0$ there are $\delta>0$ and $K$ such
that $\lvert f(n,k)/k-(1-\rho(\alpha))\rvert<\varepsilon$ whenever $k\ge K$ and
$\lvert\log n/\log k-\alpha\rvert<\delta$. The Dickman function is given by `IsDickman`, which
has exactly one solution on $[0,\infty)$, so the hypothesis `IsDickman ρ` is satisfiable and
determines $\rho(\alpha)$ for $\alpha>1$.
-/
@[category research open, AMS 11]
theorem erdos_1184 :
    ∀ ρ : ℝ → ℝ, IsDickman ρ → ∀ α : ℝ, 1 < α → ∀ n : ℕ → ℕ,
      Tendsto (fun k : ℕ => Real.log (n k) / Real.log k) atTop (𝓝 α) →
        Tendsto (fun k : ℕ => (f (n k) k : ℝ) / k) atTop (𝓝 (1 - ρ α)) := by
  sorry

/--
Erdős [Er76e, Theorem 2]: to every $\alpha>1$ there is an $\varepsilon_\alpha>0$ so that for
$k>k_0(\alpha)$ and $n>k^\alpha-k$
$$f(n,k)>k\left(1-\frac{1}{\alpha}+\varepsilon_\alpha\right).$$
Erdős gives an outline of the proof.
-/
@[category research solved, AMS 11]
theorem erdos_1184.variants.lower (α : ℝ) (hα : 1 < α) :
    ∃ ε > 0, ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, (k : ℝ) ^ α - k < n →
      k * (1 - 1 / α + ε) < (f n k : ℝ) := by
  sorry

/--
Erdős [Er76e, Theorem 3]: for $n\leq k^\alpha-k$
$$f(n,k)<k(\alpha-1)+\frac{k}{\log k}.$$
Erdős notes that this is trivial for $\alpha>2$. We take $k\geq 2$, so that $\log k>0$.
-/
@[category research solved, AMS 11]
theorem erdos_1184.variants.upper (α : ℝ) (k n : ℕ) (hk : 2 ≤ k)
    (hn : (n : ℝ) ≤ (k : ℝ) ^ α - k) :
    (f n k : ℝ) < k * (α - 1) + k / Real.log k := by
  sorry

end Erdos1184
