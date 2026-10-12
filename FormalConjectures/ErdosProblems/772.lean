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
# Erdős Problem 772

*References:*
- [erdosproblems.com/772](https://www.erdosproblems.com/772)
- [Er80e] Erdős, P., _Some applications of Ramsey's theorem to additive number theory_. European
  J. Combin. (1980), 43-46.
- [Er84d] Erdős, P., _Extremal problems in number theory, combinatorics and geometry_. Proceedings
  of the International Congress of Mathematicians, Vol. 1, 2 (Warsaw, 1983) (1984), 51-70.
- [AlEr85] Alon, Noga and Erdős, P., _An application of graph theory to additive number theory_.
  European J. Combin. (1985), 201-203.
-/

@[expose] public section

open Filter Real AdditiveCombinatorics

namespace Erdos772

/-- $H_k(n)$ is the maximal $r$ such that if $A\subset\mathbb{N}$ has $\lvert A\rvert=n$ and
$\| 1_A\ast 1_A\|_\infty \leq k$ then $A$ contains a Sidon set of size at least $r$.

Here $1_A\ast 1_A(m)$ counts the ordered pairs $(a,b)\in A^2$ with $a+b=m$. (The value is
truncated at $n$, which only matters when no such $A$ exists.) -/
noncomputable def H (k n : ℕ) : ℕ :=
  sSup {r | r ≤ n ∧ ∀ A : Finset ℕ, A.card = n → (∀ m, sumRep A m ≤ k) →
    ∃ S ⊆ A, IsSidon (S : Set ℕ) ∧ r ≤ S.card}

/--
Let $k\geq 1$ and $H_k(n)$ be the maximal $r$ such that if $A\subset\mathbb{N}$ has
$\lvert A\rvert=n$ and $\| 1_A\ast 1_A\|_\infty \leq k$ then $A$ contains a Sidon set of size at
least $r$.

Is it true that $H_k(n)/n^{1/2}\to \infty$?

The answer is yes, and in fact $H_k(n) \gg_k n^{2/3}$, proved by Alon and Erdős [AlEr85].
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos772.lean#L1040"]
theorem erdos_772.parts.i : answer(True) ↔
    ∀ k ≥ 1, Tendsto (fun n : ℕ ↦ (H k n : ℝ) / √n) atTop atTop := by
  sorry

/--
Is it true that $H_k(n) > n^{1/2+c}$ for some constant $c>0$?

The answer is yes, and in fact $H_k(n) \gg_k n^{2/3}$, proved by Alon and Erdős [AlEr85].
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos772.lean#L1040"]
theorem erdos_772.parts.ii : answer(True) ↔
    ∀ k ≥ 1, ∃ c > 0, ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 2 + c : ℝ) < H k n := by
  sorry

/-- Alon and Erdős [AlEr85] proved that $H_k(n) \gg_k n^{2/3}$. -/
@[category research solved, AMS 5 11]
theorem erdos_772.variants.alon_erdos (k : ℕ) (hk : 1 ≤ k) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ (2 / 3 : ℝ) ≤ H k n := by
  sorry

/-- Erdős [Er84d] proved that $H_k(n) \ll n^{2/3}$, where the implied constant is absolute.

Since $1_A\ast 1_A$ counts ordered pairs, the bound needs $k\geq 4$: the construction of
Erdős has at most two unordered representations of each sum, hence at most four ordered ones,
while $k\leq 2$ forces $A$ itself to be Sidon and so $H_k(n)=n$. For $k=3$ the only collisions
are $a+b=2c$, so the Sidon subsets of $A$ are its $3$-term-progression-free subsets, which have
size $n^{1-o(1)}$, and the bound fails there too. -/
@[category research solved, AMS 5 11]
theorem erdos_772.variants.upper_bound :
    ∃ C : ℝ, ∀ k ≥ 4, ∀ᶠ n : ℕ in atTop,
      (H k n : ℝ) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ) := by
  sorry

end Erdos772
