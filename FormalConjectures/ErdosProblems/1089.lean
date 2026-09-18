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
# Erdős Problem 1089

*References:*
- [erdosproblems.com/1089](https://www.erdosproblems.com/1089)
- [Er75f] Erdős, Paul, *On some problems of elementary and combinatorial geometry*. Ann. Mat. Pura
  Appl. (4) (1975), 99-108.
- [BBS83] Bannai, Eiichi and Bannai, Etsuko and Stanton, Dennis, *An upper bound for the
  cardinality of an $s$-distance subset in real Euclidean space. II*. Combinatorica (1983),
  147-152.
-/

open Filter
open scoped Topology

namespace Erdos1089

/-- `g d n` is the least `m` such that every `m` points in `ℝ^d` determine at least `n` distinct
distances, i.e. the least `m` with `n ≤ minimalDistinctDistances (EuclideanSpace ℝ (Fin d)) m`. -/
noncomputable def g (d n : ℕ) : ℕ :=
  sInf {m : ℕ | n ≤ minimalDistinctDistances (EuclideanSpace ℝ (Fin d)) m}

/--
Let $g_d(n)$ be minimal such that every collection of $g_d(n)$ points in $\mathbb{R}^d$ determines
at least $n$ many distinct distances. Estimate $g_d(n)$. In particular, does
$$\lim_{d \to \infty} \frac{g_d(n)}{d^{n-1}}$$
exist?

A problem of Erdős [Er75f, p.105]. The answer is yes: for $n \ge 2$,
$$\binom{d+1}{n-1} + 1 \le g_d(n) \le \binom{d+n-1}{n-1} + 1,$$
where the upper bound is due to Bannai, Bannai and Stanton [BBS83] and the lower bound to a
construction of Aletheia (generalising constructions for Problem 502), so that
$g_d(n) / d^{n-1} \to 1/(n-1)!$ as $d \to \infty$.
-/
@[category research solved, AMS 51 52, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1089.lean#L769"]
theorem erdos_1089 : answer(True) ↔
    ∀ n : ℕ, 2 ≤ n → ∃ L : ℝ,
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop (𝓝 L) := by
  sorry

/--
For $n \ge 2$ one has $\binom{d+1}{n-1} + 1 \le g_d(n) \le \binom{d+n-1}{n-1} + 1$ for all
$d \ge 1$, and $g_d(n) / d^{n-1} \to 1/(n-1)!$ as $d \to \infty$.
-/
@[category research solved, AMS 51 52, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1089.lean#L769"]
theorem erdos_1089.variants.bounds_and_limit (n : ℕ) (hn : 2 ≤ n) :
    (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial)) := by
  sorry

end Erdos1089
