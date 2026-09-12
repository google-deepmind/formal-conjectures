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
# Erdős Problem 981

*References:*
- [erdosproblems.com/981](https://www.erdosproblems.com/981)
- [El69] Elliott, P. D. T. A., *A conjecture of Erdős concerning character sums*. Indag. Math.
  (1969), 164--171.
- [Er65b] Erdős, Paul, *Some recent advances and current problems in number theory*. Lectures on
  Modern Mathematics, Vol. III (1965), 196-244.
- [TaZh25] Q. Tang and H. Zhang, *Average first-passage times for character sums*.
  arXiv:2512.24631 (2025).
-/

open Filter
open scoped Asymptotics

namespace Erdos981

/--
The partial character sum $\sum_{n\le N}\left(\frac{n}{p}\right)$, as a Jacobi symbol.
This is the Legendre symbol when `p` is an odd prime.
-/
noncomputable def S (p N : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 N, jacobiSym n p

/--
`f ε p` is the smallest integer $m$ such that
$\sum_{n\le N}\left(\frac{n}{p}\right)<\epsilon N$ for all $N\ge m$.

If no such $m$ exists, this is `0`, the infimum of the empty set in `ℕ`. For odd primes such an
$m$ exists by the Pólya–Vinogradov inequality.
-/
noncomputable def f (ε : ℝ) (p : ℕ) : ℕ :=
  sInf {m | ∀ N ≥ m, (S p N : ℝ) < ε * N}

/--
The first-passage (first-time) threshold: the smallest $m$ such that
$\sum_{n\le m}\left(\frac{n}{p}\right)<\epsilon m$.

If no such $m$ exists, this is `0`.
-/
noncomputable def fFirst (ε : ℝ) (p : ℕ) : ℕ :=
  sInf {m | 0 < m ∧ (S p m : ℝ) < ε * m}

/--
Let $\epsilon>0$ and $f_\epsilon(p)$ be the smallest integer $m$ such that $\sum_{n\leq N}
\left(\frac{n}{p}\right)<\epsilon N$ for all $N\geq m$. Prove that
$$\sum_{p<x}f_\epsilon(p)\sim c_\epsilon \frac{x}{\log x}$$
for some $c_\epsilon>0$.

This was proved by Elliott [El69].
-/
@[category research solved, AMS 11]
theorem erdos_981 : ∀ ε > (0 : ℝ), ∃ c > (0 : ℝ),
    (fun x : ℕ ↦ ∑ p ∈ (Finset.range x).filter Nat.Prime, (f ε p : ℝ)) ~[atTop]
      (fun x ↦ c * x / Real.log x) := by
  sorry

/--
An earlier version of this problem on this site misstated the problem, defining $f_\epsilon(p)$
instead as the smallest integer $m$ such that $\sum_{n\leq m}\left(\frac{n}{p}\right)<\epsilon m$
(thus a 'first-time' problem rather than the 'eventual-time' problem given above). An asymptotic
for this alternate definition of $f_\epsilon$ was proved by Tang and Zhang [TaZh25].
-/
@[category research solved, AMS 11]
theorem erdos_981.variants.first_time : ∀ ε > (0 : ℝ), ∃ c > (0 : ℝ),
    (fun x : ℕ ↦ ∑ p ∈ (Finset.range x).filter Nat.Prime, (fFirst ε p : ℝ)) ~[atTop]
      (fun x ↦ c * x / Real.log x) := by
  sorry

end Erdos981
