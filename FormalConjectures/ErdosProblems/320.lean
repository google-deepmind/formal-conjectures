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
# Erdős Problem 320

*References:*
- [erdosproblems.com/320](https://www.erdosproblems.com/320)
- [BGMS25] Bettin, S., Grenié, L., Molteni, G. and Sanna, C., *A lower bound for the number of
  Egyptian fractions*. arXiv:2509.10030 (2025).
- [BlEr75] Bleicher, M. N. and Erdős, P., *The number of distinct subsums of
  $\sum_{1}^{N} 1/i$*. Math. Comp. (1975), 29-42.
- [BlEr76b] Bleicher, M. N. and Erdős, P., *Denominators of Egyptian fractions. II*. Illinois J.
  Math. (1976), 598-613.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
-/

@[expose] public section

open Filter Real

open scoped Finset

namespace Erdos320

/--
$S(N)$ is the number of distinct sums of the form $\sum_{n\in A}\frac{1}{n}$ for
$A\subseteq\{1,\ldots,N\}$.
-/
def S (N : ℕ) : ℕ :=
  #((Finset.Icc 1 N).powerset.image fun A : Finset ℕ ↦ ∑ n ∈ A, (1 : ℚ) / n)

/--
`depth N` is the least $k$ with $\log_k N < e$, where $\log_k$ is the $k$-fold iterated logarithm.

For $N \geq 3$ every earlier iterate is at least $e$, so $1 \leq \log_k N < e$ for $k$ =
`depth N`, and $\log_j N \geq 1$ for all $j \leq$ `depth N`. This is a choice of $k$ with
$\log_k N = O(1)$.
-/
noncomputable def depth (N : ℕ) : ℕ :=
  sInf {k : ℕ | log^[k] N < exp 1}

/--
The order of magnitude of $\log S(N)$:
$$\frac{N}{\log N}\prod_{j=3}^{k}\log_j N,$$
where $k$ = `depth N` is such that $\log_k N = O(1)$.
-/
noncomputable def erdos_320.answer (N : ℕ) : ℝ :=
  N / log N * ∏ j ∈ Finset.Icc 3 (depth N), log^[j] N

/--
Let $S(N)$ count the number of distinct sums of the form $\sum_{n\in A}\frac{1}{n}$ for
$A\subseteq \{1,\ldots,N\}$. Estimate $S(N)$.

The order of magnitude of $\log S(N)$ is known:
$$\log S(N) \asymp \frac{N}{\log N}\prod_{j=3}^{k}\log_j N,$$
where $k$ is chosen such that $\log_k N = O(1)$. The lower bound is due to Bettin, Grenié,
Molteni, and Sanna [BGMS25]. The upper bound was proved by GPT 5.6 Sol (prompted by Young, Zhu,
and Luo), using the iterative upper bound of Bleicher and Erdős [BlEr76b] (as reported on
erdosproblems.com).
-/
@[category research solved, question value, AMS 11]
theorem erdos_320 :
    (fun N : ℕ ↦ log (S N)) =Θ[atTop] erdos_320.answer := by
  sorry

/--
Bettin, Grenié, Molteni, and Sanna [BGMS25] proved the lower bound
$$\log S(N) \geq \frac{N}{\log N}\left(2\log 2\left(1-\frac{3/2}{\log_kN}\right)
\prod_{i=3}^k\log_iN\right),$$
valid for $k\geq 4$ and $\log_kN\geq 3/2$ (as reported on erdosproblems.com).

Since `Real.log` is defined on all of $\mathbb{R}$, the condition $\log_k N \geq 3/2$ is
formalised as $\log_i N \geq 3/2$ for all $i \leq k$. This is equivalent to it for the genuine
iterated logarithm and ensures that every intermediate iterate is positive.
-/
@[category research solved, AMS 11]
theorem erdos_320.variants.lower (N k : ℕ) (hk : 4 ≤ k) (hkN : ∀ i ≤ k, 3 / 2 ≤ log^[i] N) :
    N / log N * (2 * log 2 * (1 - 3 / 2 / log^[k] N) * ∏ i ∈ Finset.Icc 3 k, log^[i] N) ≤
      log (S N) := by
  sorry

end Erdos320
