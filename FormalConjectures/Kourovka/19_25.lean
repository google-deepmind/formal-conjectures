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
# Conjecture 19.25

by B. Curtin, G. R. Pourgholi

*Reference:* [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v40)
-/

open scoped Nat Group

namespace Kourovka.«19.25»

/--
Let $G$ and $H$ be finite groups of the same order with
$\sum_{g \in G} \phi(|g|) = \sum_{h \in H} \phi(|h|)$,
where $\phi$ is the Euler totient function. Suppose that $G$ is simple. Is
$H$ necessarily simple?
-/
@[category research open, AMS 20]
theorem kourovka.«19.25» : answer(sorry) ↔
    ∀ (G H : Type) [Group G] [Group H] [Fintype G] [Fintype H],
       ∑ g : G, φ (orderOf g) = ∑ h : H, φ (orderOf h) →
       IsSimpleGroup G → IsSimpleGroup H := by
  sorry

end Kourovka.«19.25»
