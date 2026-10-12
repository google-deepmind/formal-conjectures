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
# Erdős Problem 627

*References:*
- [erdosproblems.com/627](https://www.erdosproblems.com/627)
- [AFM25] Araujo, I. and Filipe, R. and Miyazaki, R., *A note on the maximum ratio between
  chromatic number and clique number*. arXiv:2512.16062 (2025).
- [Er61d] Erdős, P., *Graph theory and probability. II*. Canadian J. Math. (1961), 346-352.
- [Er67c] Erdős, P., *Some remarks on chromatic graphs*. Colloq. Math. (1967), 253-256.
- [Er69b] Erdős, P., *Problems and results in chromatic graph theory*. Proof Techniques in Graph
  Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
- [Zy52] Zykov, A. A., *On some properties of linear complexes*. Amer. Math. Soc. Translation
  (1952), 33.
-/

@[expose] public section

open Filter SimpleGraph
open scoped Topology Asymptotics

namespace Erdos627

/--
`maxChromaticCliqueRatio n` is $f(n)$, the maximum of $\chi(G)/\omega(G)$ over all graphs $G$ on
$n$ vertices.

A graph on `Fin n` is finite, so its chromatic number (an element of `ℕ∞`) is finite and
`ENat.toNat` returns it. The maximum is taken over the finitely many graphs on `Fin n`, so the
supremum is attained. For $n = 0$ the only graph is empty, with $\chi = \omega = 0$, and the
convention $0 / 0 = 0$ gives $f(0) = 0$; this does not affect any asymptotic statement below.
-/
noncomputable def maxChromaticCliqueRatio (n : ℕ) : ℝ :=
  ⨆ G : SimpleGraph (Fin n), (G.chromaticNumber.toNat : ℝ) / (G.cliqueNum : ℝ)

/--
Let $\omega(G)$ denote the clique number of $G$ and $\chi(G)$ the chromatic number. If $f(n)$ is
the maximum value of $\chi(G)/\omega(G)$, as $G$ ranges over all graphs on $n$ vertices, then
does
$$\lim_{n\to\infty}\frac{f(n)}{n/(\log_2n)^2}$$
exist?

Since $f(n) \asymp n/(\log_2 n)^2$ (see `Erdos627.erdos_627.variants.theta`), the limit, if it
exists, is a finite real number.
-/
@[category research open, AMS 5]
theorem erdos_627 : answer(sorry) ↔
    ∃ L : ℝ, Tendsto (fun n : ℕ ↦ maxChromaticCliqueRatio n / ((n : ℝ) / Real.logb 2 n ^ 2))
      atTop (𝓝 L) := by
  sorry

/--
Erdős [Er67c] proved that
$$f(n) \asymp \frac{n}{(\log_2 n)^2}.$$
-/
@[category research solved, AMS 5]
theorem erdos_627.variants.theta :
    (fun n : ℕ ↦ maxChromaticCliqueRatio n) =Θ[atTop]
      (fun n : ℕ ↦ (n : ℝ) / Real.logb 2 n ^ 2) := by
  sorry

/--
Erdős [Er67c] proved the lower bound
$$f(n) \geq \left(\frac{1}{4} + o(1)\right) \frac{n}{(\log_2 n)^2}.$$
-/
@[category research solved, AMS 5]
theorem erdos_627.variants.lower :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (1 / 4 - ε) * ((n : ℝ) / Real.logb 2 n ^ 2) ≤ maxChromaticCliqueRatio n := by
  sorry

/--
The method of Erdős [Er67c] gives the upper bound
$$f(n) \leq (4 + o(1)) \frac{n}{(\log_2 n)^2}.$$
Erdős states the constant as $1$, but Araujo, Filipe, and Miyazaki [AFM25] note that his method
gives $4$.
-/
@[category research solved, AMS 5]
theorem erdos_627.variants.upper :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      maxChromaticCliqueRatio n ≤ (4 + ε) * ((n : ℝ) / Real.logb 2 n ^ 2) := by
  sorry

/--
Consequently, if the limit in `Erdos627.erdos_627` exists, it lies in $[1/4, 4]$ [Er67c]
(with the correction of the upper constant from $1$ to $4$ noted in [AFM25]).
-/
@[category research solved, AMS 5]
theorem erdos_627.variants.limit_bounds :
    ∀ L : ℝ, Tendsto (fun n : ℕ ↦ maxChromaticCliqueRatio n / ((n : ℝ) / Real.logb 2 n ^ 2))
      atTop (𝓝 L) → 1 / 4 ≤ L ∧ L ≤ 4 := by
  sorry

/--
Araujo, Filipe, and Miyazaki [AFM25, Theorem 1.3] improved the upper bound to
$$f(n) \leq (3.71943 + o(1)) \frac{n}{(\log_2 n)^2},$$
using recent improvements in the asymptotics of Ramsey numbers. [AFM25] is an arXiv preprint.
-/
@[category research solved, AMS 5]
theorem erdos_627.variants.afm_upper :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      maxChromaticCliqueRatio n ≤ (3.71943 + ε) * ((n : ℝ) / Real.logb 2 n ^ 2) := by
  sorry

/--
Araujo, Filipe, and Miyazaki [AFM25, Theorem 1.2]: suppose that $R(s,t) \leq R(k)$ for all
$s, t, k \in \mathbb{N}$ with $st \leq k^2$ (their Conjecture 1.1), and that
$\lim_{k \to \infty} \frac{\log_2 R(k)}{k}$ exists and equals $\ell$. Then
$$f(n) = (\ell^2 + o(1)) \frac{n}{(\log_2 n)^2},$$
so the limit in `Erdos627.erdos_627` exists and equals $\ell^2$. Here $R(s,t)$ is the
two-colour Ramsey number and $R(k) = R(k,k)$ (see [77]). [AFM25] is an arXiv preprint.
-/
@[category research solved, AMS 5]
theorem erdos_627.variants.conditional (ℓ : ℝ)
    (hR : ∀ s t k : ℕ, s * t ≤ k ^ 2 → classicalRamsey s t ≤ diagonalRamsey k)
    (hlim : Tendsto (fun k : ℕ ↦ Real.logb 2 (diagonalRamsey k : ℝ) / (k : ℝ)) atTop (𝓝 ℓ)) :
    Tendsto (fun n : ℕ ↦ maxChromaticCliqueRatio n / ((n : ℝ) / Real.logb 2 n ^ 2))
      atTop (𝓝 (ℓ ^ 2)) := by
  sorry

/--
Tutte and Zykov [Zy52] independently proved that for every $k$ there is a graph with
$\omega(G) = 2$ and $\chi(G) = k$.

We require $k \geq 2$: a graph with $\omega(G) = 2$ has an edge, so $\chi(G) \geq 2$.
-/
@[category research solved, AMS 5]
theorem erdos_627.variants.tutte_zykov :
    ∀ k : ℕ, 2 ≤ k → ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.cliqueNum = 2 ∧ G.chromaticNumber = (k : ℕ∞) := by
  sorry

/--
Erdős [Er61d] proved that for every (large) $n$ there is a graph on $n$ vertices with
$\omega(G) = 2$ and
$$\chi(G) \gg \frac{n^{1/2}}{\log n},$$
whence $f(n) \gg n^{1/2}/\log n$.
-/
@[category research solved, AMS 5]
theorem erdos_627.variants.erdos_1961 :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n),
      G.cliqueNum = 2 ∧
        c * Real.sqrt (n : ℝ) / Real.log (n : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) := by
  sorry

end Erdos627
