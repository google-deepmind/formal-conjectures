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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 781

*References:*
- [erdosproblems.com/781](https://www.erdosproblems.com/781)
- [BEF90] Brown, T. C. and Erdős, P. and Freedman, A. R., _Quasi-progressions and descending
  waves_. J. Combin. Theory Ser. A (1990), 81-95.
- [AlSp89] Alon, N. and Spencer, Joel, _Ascending waves_. J. Combin. Theory Ser. A (1989),
  275-287.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos781

/-- A $k$-term *descending wave* is a sequence $x_1<\cdots <x_k$ such that, for $1<j<k$,
$x_j \geq \frac{x_{j+1}+x_{j-1}}{2}$. -/
def IsDescendingWave {k : ℕ} (x : Fin k → ℕ) : Prop :=
  StrictMono x ∧
    ∀ i j l : Fin k, (i : ℕ) + 1 = j → (j : ℕ) + 1 = l → x i + x l ≤ 2 * x j

/-- `f k` is the minimal `n` such that any $2$-colouring of $\{1,\ldots,n\}$ (identified with
`Fin n`) contains a monochromatic $k$-term descending wave. -/
noncomputable def f (k : ℕ) : ℕ :=
  sInf {n | ∀ c : Fin n → Fin 2, ∃ x : Fin k → Fin n,
    IsDescendingWave (fun i ↦ (x i : ℕ)) ∧ ∃ γ, ∀ i, c (x i) = γ}

/--
Let $f(k)$ be the minimal $n$ such that any $2$-colouring of $\{1,\ldots,n\}$ contains a
monochromatic $k$-term descending wave: a sequence $x_1<\cdots <x_k$ such that, for $1<j<k$,
$$x_j \geq \frac{x_{j+1}+x_{j-1}}{2}.$$
Estimate $f(k)$.

Brown, Erdős, and Freedman [BEF90] proved $k^2-k+1\leq f(k) \leq \frac{k^3-4k+9}{3}$. Resolved by
Alon and Spencer [AlSp89] who proved that in fact $f(k) \gg k^3$, so that $f(k)\asymp k^3$.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos781.lean#L3202"]
theorem erdos_781.parts.i : (fun k ↦ (f k : ℝ)) =Θ[atTop] fun k ↦ (k : ℝ) ^ 3 := by
  sorry

/--
Is it true that $f(k)=k^2-k+1$ for all $k$?

The answer is no, since $f(k)\gg k^3$ by Alon and Spencer [AlSp89].
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos781.lean#L3202"]
theorem erdos_781.parts.ii : answer(False) ↔ ∀ k ≥ 1, f k = k ^ 2 - k + 1 := by
  sorry

/-- Brown, Erdős, and Freedman [BEF90] proved $k^2-k+1\leq f(k) \leq \frac{k^3-4k+9}{3}$. -/
@[category research solved, AMS 5 11]
theorem erdos_781.variants.brown_erdos_freedman (k : ℕ) (hk : 1 ≤ k) :
    k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3 := by
  sorry

end Erdos781
