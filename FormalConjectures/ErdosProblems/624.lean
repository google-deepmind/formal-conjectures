/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 624

*Reference:* [erdosproblems.com/624](https://www.erdosproblems.com/624)

-/
namespace Erdos624

open Set Function Filter Nat Real Asymptotics

/--
The condition that an integer `m` ensures the existence of a function `f` covering `Fin n`
for all large enough subsets `Y`.
The property is invariant under bijection, so we use a representative `Fin n` for a finite set of size `n`.
-/
def H_property (n m : ℕ) : Prop :=
  ∃ (f : Set (Fin n) → (Fin n)),
    ∀ (Y : Set (Fin n)), Nat.card Y ≥ m →
      Set.image f (Set.powerset Y) = Set.univ

/--
Let $H(n)$ be the minimum integer $m$ such that there is a function $f: \mathcal{P}(X) \to X$
where $X$ is a finite set of size $n$, such that for every subset $Y \subseteq X$ with $|Y| \ge m$,
the set $\{f(A) : A \subseteq Y\}$ covers $X$.
-/
noncomputable def H (n : ℕ) : ℕ :=
  if 0 < n then
    sInf {m : ℕ | H_property n m}
  else 0

open Asymptotics

/--
Let $X$ be a finite set of size $n$ and $H(n)$ be such that there is a function
$f:\{A : A\subseteq X\}\to X$ so that for every $Y\subseteq X$ with $\lvert Y\rvert \geq H(n)$
we have $\left\{ f(A) : A\subseteq Y\right\}=X$.
Prove that $H(n)-\log_2 n \to \infty$.
-/
@[category research open, AMS 5]
theorem erdos_624 :
    Tendsto (fun n : ℕ => (H n : ℝ) - (Real.log (n : ℝ) / Real.log 2)) atTop atTop := by
  sorry

end Erdos624
