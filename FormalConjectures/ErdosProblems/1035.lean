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
# Erdős Problem 1035

*Reference:* [erdosproblems.com/1035](https://www.erdosproblems.com/1035)
-/

namespace Erdos1035

/--
The $n$-dimensional hypercube graph $Q_n$ has $2^n$ vertices (corresponding to binary strings
of length $n$) with edges between vertices that differ in exactly one coordinate.
-/
def Hypercube (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj v w := ∃! i, v i ≠ w i
  symm := by
    intros v w h
    obtain ⟨i, hi, hu⟩ := h
    exact ⟨i, hi.symm, fun j hj => (hu j hj).symm⟩
  loopless := by
    intros v
    simp only [not_exists]
    intro i
    push_neg
    intro h
    use i
    constructor
    · exact h
    · simp

/--
A graph $G$ contains (or embeds) a graph $H$ if there exists an injective graph homomorphism
from $H$ to $G$.
-/
def contains {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ∃ f : β → α, Function.Injective f ∧ ∀ {v w : β}, H.Adj v w → G.Adj (f v) (f w)

/--
Is there a constant $c > 0$ such that every graph on $2^n$ vertices with minimum degree
$> (1-c) \cdot 2^n$ contains the $n$-dimensional hypercube $Q_n$?

See also [576] for the extremal number of edges that guarantee a $Q_n$.
-/
@[category research open, AMS 05]
theorem erdos_1035 :
    (∃ c > 0, ∀ n : ℕ, ∀ (G : SimpleGraph (Fin (2^n))),
      (∀ v, (G.degree v : ℝ) > (1 - c) * 2^n) →
      contains G (Hypercube n)) ↔ answer(sorry) := by
  sorry

/--
Erdős [Er93] asks: if the main conjecture is false, determine or estimate the smallest $m > 2^n$
such that every graph on $m$ vertices with minimum degree $> (1-c) \cdot 2^n$ contains a $Q_n$.

[Er93] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős (1993),
467-478.
-/
@[category research open, AMS 05]
theorem erdos_1035.variant_m (c : ℝ) (hc : c > 0) :
    (∀ n : ℕ, ∃ m > 2^n, ∀ (G : SimpleGraph (Fin m)),
      (∀ v, (G.degree v : ℝ) > (1 - c) * 2^n) →
      contains G (Hypercube n)) ↔ answer(sorry) := by
  sorry

/--
Erdős [Er93] asks: for which threshold values $u_n$ is it true that every graph on $2^n$ vertices
with minimum degree $> 2^n - u_n$ contains a $Q_n$.

[Er93] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős (1993),
467-478.
-/
@[category research open, AMS 05]
theorem erdos_1035.variant_u :
    (∃ u : ℕ → ℕ, ∀ n : ℕ, ∀ (G : SimpleGraph (Fin (2^n))),
      (∀ v, G.degree v > 2^n - u n) →
      contains G (Hypercube n)) ↔ answer(sorry) := by
  sorry

end Erdos1035
