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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 320

*Reference:* [erdosproblems.com/320](https://www.erdosproblems.com/320)

Let $S(N)$ count the number of distinct sums of the form $\sum_{n \in A} 1/n$
for $A \subseteq \{1, \ldots, N\}$. Estimate $S(N)$.

See also [Problem 321](https://www.erdosproblems.com/321) and
[OEIS A072207](https://oeis.org/A072207).

## Known Bounds

Bleicher and Erdős proved:
* **Lower bound** [BlEr75]: $\log S(N) \geq (N/\log N)(\log 2 \cdot \prod_{i=3}^{k} \log_i N)$
* **Upper bound** [BlEr76b]: $\log S(N) \leq (N/\log N)(\log_r N \cdot \prod_{i=3}^{r} \log_i N)$

where $\log_i$ denotes the $i$-fold iterated logarithm.

Bettin, Grenié, Molteni, and Sanna [BGMS25] improved the lower bound to:
$$\log S(N) \geq (N/\log N)(2 \log 2 (1 - 3/(2 \log_k N)) \cdot \prod_{i=3}^{k} \log_i N)$$

[BlEr75] Bleicher, M. N. and Erdős, P., _The number of distinct subsums of ∑₁ᴺ 1/i_.
Mathematics of Computation (1975), 29-42.

[BlEr76b] Bleicher, M. N. and Erdős, P., _Denominators of Egyptian fractions. II_.
Illinois J. Math. (1976), 598-613.

[BGMS25] Bettin, S., Grenié, L., Molteni, G., and Sanna, C., _A lower bound for the number
of Egyptian fractions_. arXiv:2509.10030 (2025).

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial
number theory_. Monographies de L'Enseignement Mathématique (1980).
-/

open Filter Real

open scoped Finset

namespace Erdos320

/-- The set of all unit-fraction subset sums from $\{1, \ldots, N\}$:
$\left\{ \sum_{n \in A} 1/n : A \subseteq \{1, \ldots, N\} \right\}$ as a finite set of
rationals. -/
noncomputable def unitFractionSums (N : ℕ) : Finset ℚ :=
  (Finset.Icc 1 N).powerset.image
    (fun A => A.sum (fun n => (1 : ℚ) / ↑n))

/-- $S(N)$ counts the number of distinct sums $\sum_{n \in A} 1/n$
for $A \subseteq \{1, \ldots, N\}$. -/
noncomputable def erdos320_S (N : ℕ) : ℕ := (unitFractionSums N).card

/--
**Erdős Problem 320** [ErGr80, p. 43]:

Estimate $S(N)$, the number of distinct sums of the form $\sum_{n \in A} 1/n$
for $A \subseteq \{1, \ldots, N\}$.
-/
@[category research open, AMS 5 11]
theorem erdos_320 (N : ℕ) :
    erdos320_S N = answer(sorry) := by
  sorry

/-
Formalisation note: it's possible that the solution to `erdos_320` needs to be
expressed asymptotically. To handle this we include `IsTheta`, `IsBigO`
and `IsLittleO` variants below. Since a solution is not known this necessitates
the use of an `answer(sorry)` placeholder. Trivial or sub-optimal solutions
will therefore exist to the asymptotic formalisations. A true solution to
the asymptotic variants should have a degree of optimality or non-triviality to it.
-/

/--
**Erdős Problem 320** (Theta variant):

What is $\Theta(S(N))$?
-/
@[category research open, AMS 5 11]
theorem erdos_320.variants.isTheta :
    (fun N ↦ (erdos320_S N : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
**Erdős Problem 320** (Big-O variant):

Find the simplest $g(N)$ such that $S(N) = O(g(N))$.
-/
@[category research open, AMS 5 11]
theorem erdos_320.variants.isBigO :
    (fun N ↦ (erdos320_S N : ℝ)) =O[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
**Erdős Problem 320** (Little-o variant):

Find the simplest $g(N)$ such that $S(N) = o(g(N))$.
-/
@[category research open, AMS 5 11]
theorem erdos_320.variants.isLittleO :
    (fun N ↦ (erdos320_S N : ℝ)) =o[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
**Erdős Problem 320** (Known lower bound, Bleicher–Erdős 1975):

$\log S(N) \geq (N / \log N) \cdot \log 2 \cdot \prod_{i=3}^{k} \log_i N$,
valid for any $k \geq 4$ with $\log_k N \geq k$.

[BlEr75] Bleicher, M. N. and Erdős, P., _The number of distinct subsums of ∑₁ᴺ 1/i_.
Mathematics of Computation (1975), 29-42.
-/
@[category research solved, AMS 5 11]
theorem erdos_320.variants.lower (N k : ℕ) (hk : 4 ≤ k) (hkN : k ≤ log^[k] N) :
    N / log N * (log 2 * ∏ i ∈ Finset.Icc 3 k, (log^[i] N)) ≤
      log (erdos320_S N : ℝ) := by
  sorry

/--
**Erdős Problem 320** (Known upper bound, Bleicher–Erdős 1976):

$\log S(N) \leq (N / \log N) \cdot \log_r N \cdot \prod_{i=3}^{r} \log_i N$,
valid for any $r \geq 1$ with $\log_{2r} N \geq 1$.

[BlEr76b] Bleicher, M. N. and Erdős, P., _Denominators of Egyptian fractions. II_.
Illinois J. Math. (1976), 598-613.
-/
@[category research solved, AMS 5 11]
theorem erdos_320.variants.upper (N r : ℕ) (hr : 1 ≤ r) (hrN : 1 ≤ log^[2 * r] N) :
    log (erdos320_S N : ℝ) ≤
      N / log N * (log^[r] N * ∏ i ∈ Finset.Icc 3 r, (log^[i] N)) := by
  sorry

/--
**Erdős Problem 320** (Improved lower bound, BGMS 2025):

$\log S(N) \geq (N / \log N) \cdot 2 \log 2 \cdot (1 - 3/(2 \log_k N)) \cdot
\prod_{i=3}^{k} \log_i N$,
valid for any $k \geq 4$ with $\log_k N \geq k$.

[BGMS25] Bettin, S., Grenié, L., Molteni, G., and Sanna, C., _A lower bound for the number
of Egyptian fractions_. arXiv:2509.10030 (2025).
-/
@[category research solved, AMS 5 11]
theorem erdos_320.variants.lower_improved (N k : ℕ) (hk : 4 ≤ k) (hkN : k ≤ log^[k] N) :
    N / log N * (2 * log 2 * (1 - 3 / (2 * log^[k] N)) *
      ∏ i ∈ Finset.Icc 3 k, (log^[i] N)) ≤
      log (erdos320_S N : ℝ) := by
  sorry

end Erdos320
