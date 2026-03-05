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
# Erdős Problem 415

*Reference:* [erdosproblems.com/415](https://www.erdosproblems.com/415)

For any $n$ let $F(n)$ be the largest $k$ such that every one of the $k!$ possible
ordering patterns appears in some consecutive sequence $\varphi(m+1), \ldots, \varphi(m+k)$
with $m + k \le n$.

Erdős [Er36b] proved that $F(n) \asymp \log \log \log n$, and similarly for $\sigma$, $\tau$,
$\nu$, or any decent additive or multiplicative function.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in
combinatorial number theory_. Monographies de L'Enseignement Mathematique (1980).
-/

open Filter Classical

namespace Erdos415

/-- A block $\varphi(m+1), \ldots, \varphi(m+k)$ exhibits ordering pattern
$\sigma \in S_k$ if $\sigma$ sorts the totient values into increasing order:
for all $i < j$ in $\operatorname{Fin} k$,
$\varphi(m + 1 + \sigma(i)) < \varphi(m + 1 + \sigma(j))$. -/
def ExhibitsPattern (k m : ℕ) (σ : Equiv.Perm (Fin k)) : Prop :=
  ∀ i j : Fin k, i < j →
    Nat.totient (m + 1 + (σ i).val) < Nat.totient (m + 1 + (σ j).val)

/-- $F(n)$ is the largest $k$ such that every permutation pattern of length $k$ is
realized among consecutive totient values up to $n$. -/
noncomputable def F (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ σ : Equiv.Perm (Fin k),
    ∃ m : ℕ, m + k ≤ n ∧ ExhibitsPattern k m σ}

/-- The descending permutation of $\operatorname{Fin} k$: $i \mapsto k - 1 - i$ (reversal). -/
def descendingPerm (k : ℕ) : Equiv.Perm (Fin k) where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv i := Fin.rev_rev i
  right_inv i := Fin.rev_rev i

/-- Number of starting positions $m$ (with $m + k \le n$) where the block of length $k$
exhibits pattern $\sigma$. -/
noncomputable def patternCount (k n : ℕ) (σ : Equiv.Perm (Fin k)) : ℕ :=
  ((Finset.range n).filter (fun m => m + k ≤ n ∧ ExhibitsPattern k m σ)).card

/--
Erdős Problem 415, Part 1 [ErGr80, p. 82]:

$F(n) / \log(\log(\log(n))) \to c$ as $n \to \infty$ for some positive constant $c$.
-/
@[category research open, AMS 11]
theorem erdos_415 :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun n : ℕ =>
        (F n : ℝ) / Real.log (Real.log (Real.log (n : ℝ))))
        atTop (nhds c) := by
  sorry

/--
Erdős Problem 415, Part 2 [ErGr80, p. 82]:

The first ordering pattern to fail is always the strictly decreasing one.
If the descending pattern of length $k$ appears in totient blocks up to $n$,
then so does every pattern of length $k$.
-/
@[category research open, AMS 11]
theorem erdos_415.variants.descending_pattern :
    ∀ n k : ℕ,
      (∃ m : ℕ, m + k ≤ n ∧ ExhibitsPattern k m (descendingPerm k)) →
        ∀ σ : Equiv.Perm (Fin k),
          ∃ m : ℕ, m + k ≤ n ∧ ExhibitsPattern k m σ := by
  sorry

/--
Erdős Problem 415, Part 3 [ErGr80, p. 82]:

There exists a most common ordering pattern (conjectured to be the "natural" pattern
mimicking $\varphi(1), \ldots, \varphi(k)$). For any pattern $\sigma$, the count of blocks
exhibiting $\sigma$ is eventually at most the count exhibiting this dominant pattern.
-/
@[category research open, AMS 11]
theorem erdos_415.variants.natural_pattern (k : ℕ) (hk : 1 ≤ k) :
    ∃ τ : Equiv.Perm (Fin k), ∀ σ : Equiv.Perm (Fin k),
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        patternCount k n σ ≤ patternCount k n τ := by
  sorry

end Erdos415
