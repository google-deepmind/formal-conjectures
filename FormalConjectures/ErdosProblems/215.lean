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
# Erdős Problem 215

*References:*
- [erdosproblems.com/215](https://www.erdosproblems.com/215)
- [Er83c] Erdős, Paul, *Combinatorial problems in geometry*. Math. Chronicle (1983), 35-54.
- [JaMa02] Jackson, Steve and Mauldin, R. Daniel, *Sets meeting isometric copies of the lattice
  $\mathbb{Z}^2$ in exactly one point*. Proc. Natl. Acad. Sci. USA (2002), 15883-15887.
-/

@[expose] public section

namespace Erdos215

/--
Does there exist $S\subseteq \mathbb{R}^2$ such that every set congruent to $S$ (that is, $S$
after some translation and rotation) contains exactly one point from $\mathbb{Z}^2$?

An old question of Steinhaus. Erdős was 'almost certain that such a set does not exist'.

In fact, such a set does exist, as proved by Jackson and Mauldin [JaMa02]. Their construction
depends on the axiom of choice.

The plane is identified with $\mathbb{C}$: the sets congruent to $S$ are the sets $uS + t$ with
$\lvert u\rvert = 1$ and $t \in \mathbb{C}$, and $\mathbb{Z}^2$ is the set of Gaussian integers.
-/
@[category research solved, AMS 52, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos215.lean#L55"]
theorem erdos_215 : answer(True) ↔ ∃ S : Set ℂ, ∀ u t : ℂ, ‖u‖ = 1 →
    ∃! z : ℂ, z ∈ (fun w => u * w + t) '' S ∧ ∃ a b : ℤ, z = a + b * Complex.I := by
  sorry

end Erdos215
