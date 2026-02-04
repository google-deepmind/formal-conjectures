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

import FormalConjectures.ErdosProblems.«274»

/-!
# Herzog–Schönheim conjecture

The actual formalization is in `FormalConjectures.ErdosProblems.«274»`.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Herzog%E2%80%93Sch%C3%B6nheim_conjecture)
-/

namespace HerzogSchonheimConjecture

@[category API, AMS 20]
theorem herzog_schonheim_conjecture {G : Type*} [Group G] (hG : 1 < ENat.card G) {ι : Type*}
        [Fintype ι] (hι : 1 < Fintype.card ι) (P : Erdos274.Group.ExactCovering G ι) :
        type_of% (Erdos274.herzog_schonheim (G := G) (hG := hG) (ι := ι) (hι := hι) (P := P)) := by
    simpa using
        (Erdos274.herzog_schonheim (G := G) (hG := hG) (ι := ι) (hι := hι) (P := P))

end HerzogSchonheimConjecture
