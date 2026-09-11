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
# Conjecture 8.8

by R. I. Grigorchuk

Part b) of the problem, due to D. V. Anosov, asks:

Does there exist a non-cyclic finitely presented group $G$ which contains an
element $a$ such that each element of $G$ is conjugate to some power of $a$?

A group is finitely presented if it is isomorphic to a quotient of a free group
on finitely many generators by the normal closure of finitely many relators; see
`Group.IsFinitelyPresented`.

*Reference:* [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v46)
-/

namespace Kourovka.«8.8»

/--
Does there exist a non-cyclic finitely presented group $G$ which contains an
element $a$ such that each element of $G$ is conjugate to some power of $a$?

Here a power of $a$ means $a^n$ for some $n \in \mathbb{Z}$.
-/
@[category research solved, AMS 20]
theorem kourovka.«8.8».parts.b : answer(sorry) ↔
    ∃ (G : Type) (_ : Group G), ¬ IsCyclic G ∧ Group.IsFinitelyPresented G
      ∃ a : G, ∀ g : G, ∃ n : ℤ, IsConj g (a ^ n) := by
  sorry

end Kourovka.«8.8»
