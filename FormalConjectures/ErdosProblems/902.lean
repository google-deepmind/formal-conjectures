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

import FormalConjecturesUtil

/-!
# Erdős Problem 902

*References:*
- [erdosproblems.com/902](https://www.erdosproblems.com/902)
- [Er63c] Erdős, P., *On a problem in graph theory*. Math. Gaz. (1963), 220-223.
- [SzSz65] Szekeres, E. and Szekeres, G., *On a problem of Schütte and Erdős*. Math. Gaz.
  (1965), 290-293.
-/

open Asymptotics Filter

namespace Erdos902

/--
A vertex `v` dominates a set `S` in a digraph if `v ∉ S` and `v` has an edge to every vertex
of `S`.
-/
def DominatesSet {V : Type*} (G : Digraph V) (v : V) (S : Set V) : Prop :=
  v ∉ S ∧ ∀ s ∈ S, G.Adj v s

/--
A tournament on `m` vertices has the Schütte–Erdős property of order `n` if every `n`-set is
dominated by some other vertex.
-/
def HasSchutteErdos {m : ℕ} (G : Digraph (Fin m)) (n : ℕ) : Prop :=
  G.IsTournament ∧
    ∀ S : Finset (Fin m), S.card = n → ∃ v, DominatesSet G v S

/--
`f(n)` is minimal such that some tournament on `f(n)` vertices has every `n`-set dominated by
another vertex.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m | ∃ G : Digraph (Fin m), HasSchutteErdos G n}

/--
Let $f(n)$ be minimal such that there is a tournament (a complete directed graph) on $f(n)$
vertices such that every set of $n$ vertices is dominated by at least one other vertex.
Estimate $f(n)$.
-/
@[category research open, AMS 5]
theorem erdos_902 :
    let g : ℕ → ℝ := answer(sorry)
    (fun n => (f n : ℝ)) ~[atTop] g := by
  sorry

/-- It is easy to check that $f(1)=3$ and $f(2)=7$. -/
@[category research solved, AMS 5]
theorem erdos_902.variants.small : f 1 = 3 ∧ f 2 = 7 := by
  sorry

/--
Erdős proved $2^{n+1}-1 \leq f(n) \ll n^2 2^n$.
-/
@[category research solved, AMS 5]
theorem erdos_902.variants.erdos :
    (fun n => (2 : ℝ) ^ (n + 1) - 1) ≪ (fun n => (f n : ℝ)) ∧
      (fun n => (f n : ℝ)) ≪ fun n => (n : ℝ) ^ 2 * (2 : ℝ) ^ n := by
  sorry

/--
Szekeres and Szekeres proved that $f(3)=19$ and $n 2^n \ll f(n)$.
-/
@[category research solved, AMS 5]
theorem erdos_902.variants.szekeres :
    f 3 = 19 ∧ (fun n => (n : ℝ) * (2 : ℝ) ^ n) ≪ fun n => (f n : ℝ) := by
  sorry

end Erdos902
