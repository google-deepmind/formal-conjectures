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
# Erdős Problem 112

*References:*
- [erdosproblems.com/112](https://www.erdosproblems.com/112)
- [ErRa67] Erdős, P. and Rado, R., *Partition relations and transitivity domains of binary
  relations*. J. London Math. Soc. (1967), 624-633.
- [LaMi97] Larson, Jean A. and Mitchell, William J., *On a problem of Erdős and Rado*. Ann.
  Comb. (1997), 245-252.

A directed graph is a `Digraph`. Loops and 2-cycles are allowed. This does not change
$k(n,m)$: deleting one arc of every 2-cycle keeps the independent sets and can only destroy
transitive tournaments.
-/

@[expose] public section

namespace Erdos112

variable {V : Type*}

/-- `s` is an independent set of `G`: there is no arc between two distinct vertices of `s`. -/
def IsIndep (G : Digraph V) (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ G.Adj x y

/-- The list `l` spans a transitive tournament in `G`: its vertices are distinct and every
earlier vertex has an arc to every later vertex. The tournament need not be induced. -/
def IsTransTournament (G : Digraph V) (l : List V) : Prop :=
  l.Nodup ∧ l.Pairwise G.Adj

/-- Every directed graph on `N` vertices contains an independent set of size `n` or a
transitive tournament of size `m`. -/
def ErdosRadoProperty (n m N : ℕ) : Prop :=
  ∀ G : Digraph (Fin N),
    (∃ s : Finset (Fin N), s.card = n ∧ IsIndep G s) ∨
    (∃ l : List (Fin N), l.length = m ∧ IsTransTournament G l)

/-- $k(n,m)$: the least $N$ such that every directed graph on $N$ vertices contains an
independent set of size $n$ or a transitive tournament of size $m$. -/
noncomputable def k (n m : ℕ) : ℕ := sInf {N | ErdosRadoProperty n m N}

/-- `s` is monochromatic of colour `i` for the edge colouring `col`. -/
def IsMono (col : Sym2 V → Fin 3) (i : Fin 3) (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → col s(x, y) = i

/-- The three-colour Ramsey number $R(a,b,c)$. -/
noncomputable def ramsey3 (a b c : ℕ) : ℕ :=
  sInf {N | ∀ col : Sym2 (Fin N) → Fin 3, ∃ s : Finset (Fin N),
    (s.card = a ∧ IsMono col 0 s) ∨ (s.card = b ∧ IsMono col 1 s) ∨
      (s.card = c ∧ IsMono col 2 s)}

/--
Let $k=k(n,m)$ be the minimum number such that any directed graph on $k$ vertices must contain
either an independent set of size $n$ or a transitive tournament of size $m$. Determine
$k(n,m)$.
-/
@[category research open, AMS 5]
theorem erdos_112 : k = answer(sorry) := by
  sorry

/--
Erdős and Rado [ErRa67] proved
$$k(n,m) \leq \frac{2^{m-1}(n-1)^m+n-2}{2n-3}.$$
-/
@[category research solved, AMS 5]
theorem erdos_112.variants.erdos_rado (n m : ℕ) (hn : 2 ≤ n) :
    (k n m : ℝ) ≤ (2 ^ (m - 1) * ((n : ℝ) - 1) ^ m + n - 2) / (2 * n - 3) := by
  sorry

/-- Larson and Mitchell [LaMi97] proved $k(n,3) \leq n^2$. -/
@[category research solved, AMS 5]
theorem erdos_112.variants.larson_mitchell (n : ℕ) : k n 3 ≤ n ^ 2 := by
  sorry

/-- Hunter observed the lower bound $R(n,m) \leq k(n,m)$. -/
@[category research solved, AMS 5]
theorem erdos_112.variants.ramsey_le (n m : ℕ) : SimpleGraph.classicalRamsey n m ≤ k n m := by
  sorry

/-- Hunter observed the upper bound $k(n,m) \leq R(n,m,m)$. -/
@[category research solved, AMS 5]
theorem erdos_112.variants.le_ramsey3 (n m : ℕ) : k n m ≤ ramsey3 n m m := by
  sorry

/-- Hunter's bound $k(n,m) \leq R(n,m,m)$ gives $k(n,m) \leq 3^{n+2m}$. -/
@[category research solved, AMS 5]
theorem erdos_112.variants.le_three_pow (n m : ℕ) : k n m ≤ 3 ^ (n + 2 * m) := by
  sorry

end Erdos112
