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
# Erdős Problem 866

*References:*
- [erdosproblems.com/866](https://www.erdosproblems.com/866)
- [CES75] S. L. G. Choi, P. Erdős and E. Szemerédi, *Some additive and multiplicative problems
  in number theory*, Acta Arith. 27 (1975), 37–50.
- [vD26] W. van Doorn, Lean formalization of bounds for Erdős Problem 866,
  [erdosproblems.com/forum/thread/866](https://www.erdosproblems.com/forum/thread/866) (2026).
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos866

/-- `A` contains all sums $b_i + b_j$ ($i < j$) of some $k$ distinct integers $b_i$. -/
def HasPairwiseSums (A : Finset ℤ) (k : ℕ) : Prop :=
  ∃ b : Fin k → ℤ, Function.Injective b ∧ ∀ i j : Fin k, i < j → b i + b j ∈ A

/-- `A` contains all sums $b_i + b_j$ ($i < j$) of some $k$ distinct positive integers $b_i$. -/
def HasPosPairwiseSums (A : Finset ℤ) (k : ℕ) : Prop :=
  ∃ b : Fin k → ℤ, Function.Injective b ∧ (∀ i, 0 < b i) ∧ ∀ i j : Fin k, i < j → b i + b j ∈ A

/-- $g_k(N)$ is the least $g$ such that every $A \subseteq \{1, \ldots, 2N\}$ with
$\lvert A\rvert \ge N + g$ contains the pairwise sums of $k$ distinct integers. -/
noncomputable def g (k N : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ A : Finset ℤ, A ⊆ Finset.Icc 1 (2 * (N : ℤ)) → N + m ≤ A.card →
    HasPairwiseSums A k}

/-- $h_k(N)$ is the variant of $g_k(N)$ in which the $b_i$ must be positive. This is the function
studied in [CES75]. -/
noncomputable def h (k N : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ A : Finset ℤ, A ⊆ Finset.Icc 1 (2 * (N : ℤ)) → N + m ≤ A.card →
    HasPosPairwiseSums A k}

/-- The odd numbers in $\{1, \ldots, 2N\}$ contain no three pairwise sums, since
$b_1 + b_2$, $b_1 + b_3$ and $b_2 + b_3$ cannot all be odd. -/
@[category test, AMS 11]
theorem not_hasPairwiseSums_odd (N : ℕ) :
    ¬ HasPairwiseSums ((Finset.Icc 1 (2 * (N : ℤ))).filter Odd) 3 := by
  rintro ⟨b, -, h⟩
  have h01 := (Finset.mem_filter.1 (h 0 1 (by decide))).2
  have h02 := (Finset.mem_filter.1 (h 0 2 (by decide))).2
  have h12 := (Finset.mem_filter.1 (h 1 2 (by decide))).2
  rw [Int.odd_iff] at h01 h02 h12
  omega

def erdos_866.answer : ℕ → ℕ → ℝ := by sorry

/-- Fix $k \ge 3$. Let $g_k(N)$ be minimal such that if $A \subseteq \{1, \ldots, 2N\}$ has
$\lvert A\rvert \ge N + g_k(N)$ then there exist integers $b_1, \ldots, b_k$ such that all
$\binom{k}{2}$ pairwise sums $b_i + b_j$ ($i < j$) are in $A$. Estimate $g_k(N)$. -/
@[category research open, question value, AMS 11]
theorem erdos_866 (k : ℕ) (hk : 3 ≤ k) :
    (fun N : ℕ => (g k N : ℝ)) =Θ[atTop] erdos_866.answer k := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- van Doorn [vD26]: $g_3(N) = 1$ for $N \ge 3$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos866b.lean#L232"]
theorem erdos_866.variants.three (N : ℕ) (hN : 3 ≤ N) : g 3 N = 1 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- [CES75, Theorem 1]: $h_3(N) = 2$. [CES75] assumes $N > 4$. van Doorn [vD26] proves it for
$N \ge 4$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos866b.lean#L633"]
theorem erdos_866.variants.three_pos (N : ℕ) (hN : 4 ≤ N) : h 3 N = 2 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- van Doorn [vD26]: $g_4(N) = 3$ for $N \ge 2$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos866b.lean#L730"]
theorem erdos_866.variants.four (N : ℕ) (hN : 2 ≤ N) : g 4 N = 3 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- [CES75, Theorem 2] shows $h_4(N) \ll 1$. van Doorn [vD26]: $h_4(N) \le 2270$ for $N \ge 1$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos866b.lean#L1624"]
theorem erdos_866.variants.four_pos (N : ℕ) (hN : 1 ≤ N) : h 4 N ≤ 2270 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- van Doorn [vD26]: $g_5(N) < 1.2 \cdot 10^8$ for all $N$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos866b.lean#L3244"]
theorem erdos_866.variants.five (N : ℕ) : g 5 N < 120000000 := by
  sorry

/-- [CES75, Theorem 3]: $h_5(N) \asymp \log N$. The lower bound comes from the odd numbers
together with the powers of $2$. -/
@[category research solved, AMS 11]
theorem erdos_866.variants.five_pos :
    (fun N : ℕ => (h 5 N : ℝ)) =Θ[atTop] fun N : ℕ => Real.log N := by
  sorry

/-- [CES75, Theorem 4]: $h_6(N) \asymp N^{1/2}$. -/
@[category research solved, AMS 11]
theorem erdos_866.variants.six_pos :
    (fun N : ℕ => (h 6 N : ℝ)) =Θ[atTop] fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ) := by
  sorry

/-- [CES75, Theorem 5]: $h_k(N) \ll_k N^{1 - 2^{-k}}$. Since $g_k(N) \le h_k(N)$, the same bound
holds for $g_k(N)$. -/
@[category research solved, AMS 11]
theorem erdos_866.variants.upper (k : ℕ) (hk : 3 ≤ k) :
    (fun N : ℕ => (h k N : ℝ)) ≪ fun N : ℕ => (N : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ k) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- van Doorn [vD26]: $h_k(N) < 4 N^{1 - 2^{-(k-2)}}$ for all large $N$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos866b.lean#L3714"]
theorem erdos_866.variants.upper_explicit (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ N : ℕ in atTop, (h k N : ℝ) < 4 * (N : ℝ) ^ ((1 : ℝ) - 1 / 2 ^ ((k : ℝ) - 2)) := by
  sorry

/-- [CES75, Theorem 6]: for every $\varepsilon > 0$, if $k$ is sufficiently large then
$h_k(N) > N^{1 - \varepsilon}$ for all large $N$. Since $h_{k-1}(N) \le g_k(N)$, the same holds
for $g_k(N)$. -/
@[category research solved, AMS 11]
theorem erdos_866.variants.lower (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (1 - ε) < h k N := by
  sorry

end Erdos866
