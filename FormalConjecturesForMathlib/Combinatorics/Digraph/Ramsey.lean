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

public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Nat.Lattice

@[expose] public section

/-!
# Directed Ramsey Numbers

This file defines the directed Ramsey number `k(n, m)` and related concepts on
`Digraph`s: independent sets, transitive tournaments and directed paths. The Ramsey
numbers here quantify over **oriented graphs**, i.e. digraphs that are loopless and
antisymmetric.
-/

namespace Digraph

variable {V : Type*}

/-- An *oriented graph* is a digraph that is loopless and antisymmetric (every pair of
distinct vertices has at most one directed edge between them). -/
def IsOriented (G : Digraph V) : Prop :=
  (∀ v, ¬ G.Adj v v) ∧ (∀ u v, G.Adj u v → ¬ G.Adj v u)

/-- An independent set in a digraph: a set $S$ of vertices with no directed edges
between any two of its members (in either direction). -/
def IsIndepSet (G : Digraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v

/-- A transitive tournament on vertex set $S$ in digraph $G$: there is a bijection
$f : \mathrm{Fin}(|S|) \to S$ such that $G.\mathrm{Adj}(f(i), f(j))$ holds if and only
if $i < j$. This encodes a total ordering of $S$ compatible with the edge relation. -/
def IsTransTournament (G : Digraph V) (S : Finset V) : Prop :=
  ∃ f : Fin S.card → {x : V // x ∈ S}, Function.Bijective f ∧
    ∀ i j : Fin S.card, G.Adj (f i : V) (f j : V) ↔ i < j

/-- A directed path on vertex set $S$ in digraph $G$: there is a bijection
$f : \mathrm{Fin}(|S|) \to S$ such that $G.\mathrm{Adj}(f(i), f(i+1))$ holds for
all consecutive indices. Only consecutive vertices need be connected. -/
def IsDirectedPath (G : Digraph V) (S : Finset V) : Prop :=
  ∃ f : Fin S.card → {x : V // x ∈ S}, Function.Bijective f ∧
    ∀ i : Fin S.card, ∀ h : (i : ℕ) + 1 < S.card,
      G.Adj (f i : V) (f ⟨i + 1, h⟩ : V)

/--
`IsDirRamsey k n m` means: every oriented graph on `k` vertices contains either an
independent set of size `n` or a transitive tournament of size `m`.
-/
def IsDirRamsey (k n m : ℕ) : Prop :=
  ∀ G : Digraph (Fin k), G.IsOriented →
    (∃ S : Finset (Fin k), S.card = n ∧ G.IsIndepSet S) ∨
    (∃ S : Finset (Fin k), S.card = m ∧ G.IsTransTournament S)

/--
The directed Ramsey number `k(n, m)`: the least `k` such that `IsDirRamsey k n m` holds.
-/
noncomputable def dirRamseyNumber (n m : ℕ) : ℕ :=
  sInf {k : ℕ | IsDirRamsey k n m}

/--
`IsDirPathRamsey k n m` means: every oriented graph on `k` vertices contains either an
independent set of size `n` or a directed path of size `m`.
-/
def IsDirPathRamsey (k n m : ℕ) : Prop :=
  ∀ G : Digraph (Fin k), G.IsOriented →
    (∃ S : Finset (Fin k), S.card = n ∧ G.IsIndepSet S) ∨
    (∃ S : Finset (Fin k), S.card = m ∧ G.IsDirectedPath S)

/--
The directed-path Ramsey number: the least `k` such that `IsDirPathRamsey k n m` holds.
-/
noncomputable def dirPathRamseyNumber (n m : ℕ) : ℕ :=
  sInf {k : ℕ | IsDirPathRamsey k n m}

end Digraph
