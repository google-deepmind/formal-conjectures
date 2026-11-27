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
# Erdős Problem 738

*References:*
- [erdosproblems.com/738](https://www.erdosproblems.com/738)
- [Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*.
  Combinatorica (1981), 25-42.
-/

@[expose] public section

namespace Erdos738

/--
If $G$ has infinite chromatic number and is triangle-free (contains no $K_3$) then must $G$
contain every tree as an induced subgraph?

A conjecture of Gyárfás. The graph $G$ may be infinite; infinite chromatic number means that $G$
has no proper colouring with finitely many colours. By the de Bruijn–Erdős theorem this would
follow from the triangle-free case of the Gyárfás–Sumner conjecture
(see `GyarfasSumnerConjecture.gyarfas_sumner_conjecture`).
-/
@[category research open, question, AMS 5]
theorem erdos_738 : ∀ {V : Type} (G : SimpleGraph V), G.chromaticNumber = ⊤ → G.CliqueFree 3 →
    ∀ {W : Type} [Fintype W] (T : SimpleGraph W), T.IsTree → T.IsIndContained G := by
  sorry

end Erdos738
