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

import Mathlib

/-!
# Erdős Problem 950

*References:*
- [erdosproblems.com/855](https://www.erdosproblems.com/855)
- [erdosproblems.com/950](https://www.erdosproblems.com/950)
- [Er77c] Erdős, Paul, Problems and results on combinatorial number theory. III. Number theory day
  (Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43-72.
- [mathoverflow/508491](https://mathoverflow.net/questions/508491)
-/

open Filter
open scoped Asymptotics Nat.Prime

namespace Erdos950

/--
Let $f(n) = \sum_{p<n}\frac{1}{n-p}$.
-/
noncomputable def f (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range n).filter Prime, (1 : ℝ) / (n - p : ℝ)

/--
Is it true that $\liminf f(n)=1$?
-/
theorem erdos_950.parts.i :
    True ↔ atTop.liminf (fun n : ℕ ↦ (f n : EReal)) = 1 := by
  sorry

/--
Is it true that $\limsup f(n)=\infty$?
-/
theorem erdos_950.parts.ii :
    True ↔ atTop.limsup (fun n : ℕ ↦ (f n : EReal)) = ⊤ := by
  sorry

/--
Is it true that $f(n)=o(\log\log n)$ for all $n$?
-/
theorem erdos_950.parts.iii :
    True ↔ f =o[atTop] (fun n : ℕ ↦ Real.log (Real.log n)) := by
  sorry

/--
This function was considered by de Bruijn, Erdős, and Turán, who showed that
$\sum_{n<x}f(n)\sim \sum_{n<x}f(n)^2\sim x$. They gave no proofs, but a proof of the (harder) second
claim is given by Gorodetsky here [mathoverflow/508491].
-/
theorem erdos_950.variants.debruijn_erdos_turan :
    (fun x : ℕ ↦ ∑ n ∈ Finset.range x, f n) ~[atTop] (fun x : ℕ ↦ (x : ℝ)) ∧
    (fun x : ℕ ↦ ∑ n ∈ Finset.range x, (f n) ^ 2) ~[atTop] (fun x : ℕ ↦ (x : ℝ)) := by
  sorry

/--
Erdős writes that a 'weaker conjecture which is perhaps not quite inaccessible' is that,
for every $\epsilon>0$, if $x$ is sufficiently large there exists $y<x$ such that
$\pi(x)< \pi(y)+\epsilon \pi(x-y)$. Compare this to [855].
-/
theorem erdos_950.variants.weaker_pi :
    True ↔ ∀ ε > 0, ∀ᶠ x in atTop, ∃ y < x,
      (π x : ℝ) < (π y : ℝ) + ε * (π (x - y) : ℝ) := by
  sorry

/--
He notes that if $\pi(x)< \pi(y)+O\left(\frac{x-y}{\log x}\right)$ for all $y<x-(\log x)^C$ for
some constant $C>0$ then $f(n)\ll \log\log\log n$.
-/
theorem erdos_950.variants.weaker_pi_implies_f
    (h : ∃ C > (0 : ℝ), ∃ K > (0 : ℝ), ∀ᶠ x : ℕ in atTop, ∀ y : ℕ,
      (y : ℝ) < x - (Real.log x) ^ C →
      (π x : ℝ) < (π y : ℝ) + K * ((x - y : ℝ) / Real.log x)) :
    f =O[atTop] fun n : ℕ ↦ Real.log (Real.log (Real.log n)) := by
  sorry

/--
The study of $f(p)$ is even harder, and Erdős could not prove that
$\sum_{p<x}f(p)^2\sim \pi(x)$.
-/
theorem erdos_950.variants.sum_primes :
    True ↔
      (fun x : ℕ ↦ ∑ p ∈ (Finset.range x).filter Prime, (f p) ^ 2) ~[atTop]
        fun x ↦ (π x : ℝ) := by
  sorry

end Erdos950
