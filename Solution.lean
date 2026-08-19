/-
Copyright (c) 2025 The Formal Conjectures Authors.

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
import EulerBrick
namespace EulerBrick
section Cuboid

/--
The first Cuboid conjecture

The DeepMind prover agent has found a formal disproof of this statement.

An (independent) informal solution can be found here:
*Reference:* [arxiv/2510.11768](https://arxiv.org/abs/2510.11768) **Irreducibility of the Cuboid Polynomial P_{a,u}(t) via a Rank-Zero Elliptic Curve** by *Valery Asiryan*
-/
theorem cuboid_one : CuboidOne := by
  intro a b hg ha hb hab
  unfold CuboidOneFor
  have h_irr := cuboid_poly_irreducible_Z a b hab ha hb
  exact h_irr

#print axioms cuboid_one
end Cuboid

end EulerBrick
