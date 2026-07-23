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
# Erdős Problem 708

*References:*
- [erdosproblems.com/708](https://www.erdosproblems.com/708)
- [ErSu59] Erdős, Pál and Surányi, János, _Bemerkungen zu einer Aufgabe eines mathematischen
  Wettbewerbs_. Mat. Lapok (1959), 39-48.
- [Er92c] Erdős, P., _Some of my forgotten problems in number theory_. Hardy-Ramanujan J.
  (1992), 34-50.
-/

open Filter

namespace Erdos708

/--
`HasCoveringSize n k` says that for every $A \subseteq [2, \infty) \cap \mathbb{N}$ with
$|A| = n$ and every set $I$ of $\max(A)$ consecutive (positive) integers, there is some
$B \subseteq I$ with $|B| \leq k$ such that $\prod_{a \in A} a \mid \prod_{b \in B} b$.

Implementation notes:
- The window of $\max(A)$ consecutive integers starting at $m$ is `Finset.Ico m (m + A.sup id)`;
  `A.sup id` is $\max(A)$ (the junk value `0` for `A = ∅` is irrelevant since `A.card = n` is
  only instantiated at `n ≥ 1` in the statements below).
- We require `0 < m`, reading "consecutive integers" as consecutive *positive* integers.
  This matches the primary formulation in [Er92c], where the windows are
  $\{x + 1, \dots, x + a_n\}$ with $x \geq 0$. [ErSu59] phrases the windows as arbitrary
  consecutive integers, but over $\mathbb{Z}$ the value of $g$ is unchanged: a window
  containing $0$ is trivially satisfiable (any $B \ni 0$ has $\prod_{b \in B} b = 0$), and a
  window of negative integers reduces to a positive one via $b \mapsto -b$, which changes the
  product only by a sign.
- The source states $|B| = g(n)$, but we use `B.card ≤ k` so that
  `{k | HasCoveringSize n k}` is upward closed. With equality no single `k` can serve all `A`:
  e.g. $A = \{2, \dots, n+1\}$ forces windows of length $\max(A) = n + 1 < (2 - o(1))n$, so a
  `B` of the size required by the Erdős–Surányi lower bound does not even fit in the window.
  Padding `B` with extra window elements preserves divisibility, so `≤` and `=` agree whenever
  the window is long enough.
-/
def HasCoveringSize (n k : ℕ) : Prop :=
  ∀ A : Finset ℕ, A.card = n → (∀ a ∈ A, 2 ≤ a) →
    ∀ m : ℕ, 0 < m →
      ∃ B ⊆ Finset.Ico m (m + A.sup id), B.card ≤ k ∧ (∏ a ∈ A, a) ∣ ∏ b ∈ B, b

/--
`IsMinCoveringSize g` says that `g n` is the function $g(n)$ of Erdős and Surányi: the minimal
$k$ such that for any $A \subseteq [2, \infty) \cap \mathbb{N}$ with $|A| = n$ and any set $I$
of $\max(A)$ consecutive integers there exists some $B \subseteq I$ with $|B| \leq k$ (see
`HasCoveringSize` for the `≤`/`=` discussion) such that
$$\prod_{a \in A} a \mid \prod_{b \in B} b.$$

The existence of such a `g` (i.e. that some finite `k` works for every `A`) is itself a theorem
of Erdős and Surányi [ErSu59]; stating the conjectures with `IsMinCoveringSize g` as a
hypothesis sidesteps this existence question.
-/
def IsMinCoveringSize (g : ℕ → ℕ) : Prop :=
  ∀ n, IsLeast {k | HasCoveringSize n k} (g n)

/--
Let $g(n)$ be minimal such that for any $A\subseteq [2,\infty)\cap \mathbb{N}$ with
$\lvert A\rvert = n$ and any set $I$ of $\max(A)$ consecutive integers there exists some
$B\subseteq I$ with $\lvert B\rvert = g(n)$ such that
$$\prod_{a\in A} a \mid \prod_{b\in B} b.$$
Is it true that
$$g(n) \leq (2+o(1))n?$$
-/
@[category research open, AMS 11]
theorem erdos_708.parts.i : answer(sorry) ↔ ∀ g : ℕ → ℕ, IsMinCoveringSize g →
    ∃ E : ℕ → ℝ, E =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ n, (g n : ℝ) ≤ (2 + E n) * n := by
  sorry

/--
Or perhaps even $g(n)\leq 2n$?
-/
@[category research open, AMS 11]
theorem erdos_708.parts.ii : answer(sorry) ↔ ∀ g : ℕ → ℕ, IsMinCoveringSize g →
    ∀ n, g n ≤ 2 * n := by
  sorry

/--
Erdős and Surányi [ErSu59] proved that $g(n) \geq (2-o(1))n$. Their lower bound construction
takes $A$ as the set of $p_ip_j$ for $i\neq j$, where $p_1<\cdots <p_\ell$ is some set of primes
such that $2p_1^2>p_\ell^2$.
-/
@[category research solved, AMS 11]
theorem erdos_708.variants.lower_bound (g : ℕ → ℕ) (hg : IsMinCoveringSize g) :
    ∃ E : ℕ → ℝ, E =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ n, (2 - E n) * n ≤ (g n : ℝ) := by
  sorry

/--
Gallai was the first to consider problems of this type, and observed that $g(2)=2$.
-/
@[category research solved, AMS 11]
theorem erdos_708.variants.g_two (g : ℕ → ℕ) (hg : IsMinCoveringSize g) :
    g 2 = 2 := by
  sorry

/--
Erdős and Surányi [ErSu59] proved that $g(3)=4$ (Gallai had observed $g(3) \geq 4$).
-/
@[category research solved, AMS 11]
theorem erdos_708.variants.g_three (g : ℕ → ℕ) (hg : IsMinCoveringSize g) :
    g 3 = 4 := by
  sorry

/--
Sanity check for the definitions: $g(1) = 1$, since any window of $a$ consecutive positive
integers contains a multiple of $a$, while the empty product $1$ is not divisible by $a \geq 2$.
-/
@[category test, AMS 11]
theorem erdos_708.variants.g_one (g : ℕ → ℕ) (hg : IsMinCoveringSize g) :
    g 1 = 1 := by
  sorry

end Erdos708
