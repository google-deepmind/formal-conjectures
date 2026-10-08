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
# Erdős Problem 235

*References:*
- [erdosproblems.com/235](https://www.erdosproblems.com/235)
- [Ho65] Hooley, Christopher, _On the difference between consecutive numbers prime to $n$_. II.
  Publ. Math. Debrecen (1965), 39--49.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Erdos235

/-- The product of the first `k + 1` primes.
On [erdosproblems.com/235](https://www.erdosproblems.com/235) this is $N_{k+1}=2\cdot 3\cdots p_{k+1}$.
The limit as $k\to\infty$ is the same for either indexing. -/
noncomputable def N (k : ℕ) : ℕ :=
  primorial (Nat.nth Nat.Prime k)

/-- The increasing list of integers `< n` that are coprime to `n`. -/
def coprimeList (n : ℕ) : List ℕ :=
  ({a ∈ Finset.range n | n.Coprime a}).sort (· ≤ ·)

/-- The gaps $a_i - a_{i-1}$ between consecutive entries of `coprimeList n`. -/
def gaps (n : ℕ) : List ℕ :=
  (coprimeList n).zipWith (fun a b ↦ b - a) (coprimeList n).tail

/-- The number of gaps of size at most $c \cdot n / \varphi(n)$. -/
noncomputable def countGaps (n : ℕ) (c : ℝ) : ℕ :=
  (gaps n).countP fun g ↦ decide ((g : ℝ) ≤ c * (n : ℝ) / (n.totient : ℝ))

/-- The proportion appearing in `erdos_235`, for the primorial `N k`. -/
noncomputable def proportion (k : ℕ) (c : ℝ) : ℝ :=
  (countGaps (N k) c : ℝ) / ((N k).totient : ℝ)

/-- `N 0` is the primorial of $2$. -/
@[category test, AMS 11]
theorem N_zero : N 0 = 2 := by
  simp [N, Nat.nth_prime_zero_eq_two, primorial_two]

/-- `N 1` is the primorial of $3$. -/
@[category test, AMS 11]
theorem N_one : N 1 = 6 := by
  simp [N, Nat.nth_prime_one_eq_three]
  decide

/-- `coprimeList n` has length $\varphi(n)$. -/
@[category test, AMS 11]
theorem coprimeList_length (n : ℕ) : (coprimeList n).length = n.totient := by
  rw [coprimeList, Finset.length_sort (· ≤ ·), Nat.totient_eq_card_coprime]

/-- $\varphi(N_k)$ is positive, so the proportion is not a division by zero. -/
@[category test, AMS 11]
theorem totient_N_pos (k : ℕ) : 0 < (N k).totient := by
  rw [Nat.totient_pos]
  exact primorial_pos (Nat.nth Nat.Prime k)

/--
Let $N_k=2\cdot 3\cdots p_k$ and $\{a_1<a_2<\cdots <a_{\phi(N_k)}\}$ be the integers $<N_k$ which
are relatively prime to $N_k$. Then, for any $c\geq 0$, the limit
$$\frac{\#\{ a_i-a_{i-1}\leq c \frac{N_k}{\phi(N_k)} : 2\leq i\leq \phi(N_k)\}}{\phi(N_k)}$$
exists and is a continuous function of $c$.

Solved by Hooley [Ho65], who proved that these gaps have an exponential distribution: that is, if
$f(c)$ is the function in question, then
$$f(c)=(1+o(1))(1-e^{-c})$$
(where the $o(1)$ goes to $0$ uniformly as $k\to \infty$).

See also [234](https://www.erdosproblems.com/234) for a more difficult version of this problem using
actual primes.
-/
@[category research solved, AMS 11]
@[formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos235.lean#L4266"]
theorem erdos_235 :
    ∃ f : ℝ → ℝ, ContinuousOn f (Set.Ici (0 : ℝ)) ∧
      ∀ c, 0 ≤ c → Tendsto (fun k ↦ proportion k c) atTop (𝓝 (f c)) := by
  sorry

/--
Hooley [Ho65] proved that the limit in `erdos_235` is $1-e^{-c}$.
For each fixed $c\geq 0$,
$$f(c)=(1+o(1))(1-e^{-c})$$
as $k\to\infty$.
-/
@[category research solved, AMS 11]
@[formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos235.lean#L4266"]
theorem erdos_235.variants.hooley (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c))) := by
  sorry

end Erdos235
