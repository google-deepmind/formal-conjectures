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
# Erdős Problem 926

*References:*
- [erdosproblems.com/926](https://www.erdosproblems.com/926)
- [AKS03] Alon, Noga and Krivelevich, Michael and Sudakov, Benny, *Turán numbers of bipartite graphs
  and related Ramsey-type questions*. Combin. Probab. Comput. (2003), 477-494.
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Fu91] Füredi, Zoltán, *On a Turán type problem of Erdős*. Combinatorica (1991), 75--79.
-/

open Filter SimpleGraph

namespace Erdos926

/--
Let $k\geq 4$. Is it true that
$$\mathrm{ex}(n;H_k) \ll_k n^{3/2},$$
where $H_k$ is the graph on vertices $x,y_1,\ldots,y_k,z_1,\ldots,z_{\binom{k}{2}}$, where $x$ is
adjacent to all $y_i$ and each pair of $y_i,y_j$ is adjacent to a unique $z_i$.

The answer is yes, proved by Füredi [Fu91], who proved that
$$\mathrm{ex}(n;H_k) \ll (kn)^{3/2}.$$
This was improved to
$$\mathrm{ex}(n;H_k) \ll kn^{3/2}$$
by Alon, Krivelevich, and Sudakov [AKS03].
-/
@[category research solved, AMS 5]
theorem erdos_926 : answer(True) ↔
    ∀ (k : ℕ), 4 ≤ k →
      Asymptotics.IsBigO atTop
        (fun n : ℕ => (extremalNumber n (furediH k) : ℝ))
        (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 2)) := by
  sorry

/--
It is trivial that $\mathrm{ex}(n;H_k)\gg n^{3/2}$ since $H_k$ contains a $C_4$ for $k\geq 3$.
-/
@[category research solved, AMS 5]
theorem erdos_926.variants.lower_bound :
    ∃ c > (0 : ℝ), ∀ (k : ℕ), 3 ≤ k → ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ (extremalNumber n (furediH k) : ℝ) := by
  sorry

/--
Erdős [Er71] claimed a proof for $k=3$.
-/
@[category research solved, AMS 5]
theorem erdos_926.variants.k_eq_3 :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => (extremalNumber n (furediH 3) : ℝ))
      (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 2)) := by
  sorry

/--
Füredi [Fu91] proved that
$$\mathrm{ex}(n;H_k) \ll (kn)^{3/2}.$$
-/
@[category research solved, AMS 5]
theorem erdos_926.variants.furedi :
    ∃ C ≥ (0 : ℝ), ∀ (k : ℕ), 4 ≤ k →
      Asymptotics.IsBigOWith C atTop
        (fun n : ℕ => (extremalNumber n (furediH k) : ℝ))
        (fun n : ℕ => ((k : ℝ) * n) ^ ((3 : ℝ) / 2)) := by
  sorry

/--
This was improved to
$$\mathrm{ex}(n;H_k) \ll kn^{3/2}$$
by Alon, Krivelevich, and Sudakov [AKS03].
-/
@[category research solved, AMS 5]
theorem erdos_926.variants.alon_krivelevich_sudakov :
    ∃ C ≥ (0 : ℝ), ∀ (k : ℕ), 4 ≤ k →
      Asymptotics.IsBigOWith C atTop
        (fun n : ℕ => (extremalNumber n (furediH k) : ℝ))
        (fun n : ℕ => (k : ℝ) * (n : ℝ) ^ ((3 : ℝ) / 2)) := by
  sorry


/-- Füredi's $H_k$ is bipartite. -/
@[category API, AMS 5]
theorem erdos_926.variants.furediH_isBipartite (k : ℕ) : (furediH k).IsBipartite :=
  SimpleGraph.furediH_isBipartite k



/-- For `k ≥ 1`, `χ(H_k) = 2`. -/
@[category API, AMS 5]
theorem erdos_926.variants.furediH_chromaticNumber_eq_two {k : ℕ} (hk : 1 ≤ k) :
    (furediH k).chromaticNumber = 2 :=
  SimpleGraph.furediH_chromaticNumber_eq_two hk


end Erdos926
