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
# Erdős Problem 895

*References:*
- [erdosproblems.com/895](https://www.erdosproblems.com/895)
- [Er95d] Erdős, Paul, *On some problems in combinatorial set theory*. Publ. Inst. Math.
  (Beograd) (N.S.) (1995), 61-65.
-/

@[expose] public section

open Filter

namespace Erdos895

/--
Is it true that, for all sufficiently large $n$, if $G$ is a triangle-free graph on
$\{1,\ldots,n\}$ then there must exist three independent points $a,b,a+b$?

A problem of Erdős and Hajnal [Er95d]. The stated problem has been resolved by Barber (personal
communication) who verified using a SAT solver that this is true for all $n\geq 18$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos895.lean#L268"]
theorem erdos_895 : answer(True) ↔
    ∀ᶠ n in atTop, ∀ G : SimpleGraph (Set.Icc 1 n), G.CliqueFree 3 →
      ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c} := by
  sorry

/--
Barber's sharp form of [erdős_895](https://www.erdosproblems.com/895): every triangle-free graph on
$\{1,\ldots,n\}$ with $n\geq 18$ contains three independent points $a,b,a+b$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos895.lean#L243"]
theorem erdos_895.variants.eighteen (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n))
    (hG : G.CliqueFree 3) :
    ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c} := by
  sorry

/--
Hajnal thought that there is in fact an independent set which is a Hindman set - that is, an
independent set of the shape
$$\left\{ \sum_{i\in S}a_i : S\subseteq \{1,\ldots,k\}\right\}$$
for some $a_1,\ldots,a_k$ (provided $n$ is sufficiently large depending on $k$).

The general question of an independent Hindman set remains open. Here the $a_i$ are taken to be
distinct positive integers and $S$ ranges over the nonempty subsets of $\{1,\ldots,k\}$.
-/
@[category research open, AMS 5]
theorem erdos_895.variants.hindman : answer(sorry) ↔
    ∀ k : ℕ, ∀ᶠ n in atTop, ∀ G : SimpleGraph (Set.Icc 1 n), G.CliqueFree 3 →
      ∃ a : Fin k → ℕ, StrictMono a ∧ ∃ I : Set (Set.Icc 1 n), G.IsIndepSet I ∧
        Subtype.val '' I = {m | ∃ S : Finset (Fin k), S.Nonempty ∧ m = ∑ i ∈ S, a i} := by
  sorry

end Erdos895
