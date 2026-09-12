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
# Erdős Problem 1046

*Reference:* [erdosproblems.com/1046](https://www.erdosproblems.com/1046)
-/

open Polynomial Metric

namespace Erdos1046

/--
Let $f\in \mathbb{C}[x]$ be a monic polynomial and
$$
E=\{ z: \lvert f(z)\rvert <1\}.
$$
If $E$ is connected then is $E$ contained in a disc of radius $2$?
-/
@[category research open, AMS 30]
theorem erdos_1046 :
    answer(sorry) ↔
      ∀ f : ℂ[X], f.Monic →
        let E := { z : ℂ | ‖f.aeval z‖ < 1 }
        IsConnected E → ∃ c : ℂ, E ⊆ closedBall c 2 := by
  sorry

end Erdos1046
