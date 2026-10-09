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

import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Tactic

/-!
AEGIS Ω — meromorphic continuation identity helper V11.

If two meromorphic functions on a preconnected domain agree in a full
neighborhood of one point, then they agree in a punctured neighborhood of
every point of the domain.

The proof uses the clopen/infinite-order mechanism already provided by
Mathlib's meromorphic-order API:
* f-g has order top at the seed point;
* if it had finite order anywhere else, preconnectedness would propagate that
  finite order back to the seed point;
* hence f-g has order top everywhere, i.e. it vanishes in every punctured
  neighborhood.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology

set_option autoImplicit false
noncomputable section

namespace AEGIS.MeromorphicIdentityPreconnectedV11

theorem eventuallyEq_nhdsNE_of_meromorphicOn_of_seed
    {U : Set ℂ} {f g : ℂ → ℂ}
    (hf : MeromorphicOn f U)
    (hg : MeromorphicOn g U)
    (hU : IsPreconnected U)
    {x y : ℂ}
    (hx : x ∈ U) (hy : y ∈ U)
    (hseed : f =ᶠ[𝓝 x] g) :
    f =ᶠ[𝓝[≠] y] g := by
  let h : ℂ → ℂ := fun z => f z - g z
  have hh : MeromorphicOn h U := by
    dsimp [h]
    exact hf.sub hg

  have hseed0 : h =ᶠ[𝓝 x] 0 := by
    filter_upwards [hseed] with z hz
    simp [h, hz]

  have hseed0NE : h =ᶠ[𝓝[≠] x] 0 :=
    hseed0.filter_mono inf_le_left

  have htopx : meromorphicOrderAt h x = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr hseed0NE

  have htopy : meromorphicOrderAt h y = ⊤ := by
    by_contra hne
    have hxFinite :
        meromorphicOrderAt h x ≠ ⊤ :=
      hh.meromorphicOrderAt_ne_top_of_isPreconnected
        (x := y) (y := x) hU hy hx hne
    exact hxFinite htopx

  have hy0 : h =ᶠ[𝓝[≠] y] 0 :=
    meromorphicOrderAt_eq_top_iff.mp htopy

  filter_upwards [hy0] with z hz
  simpa [h, sub_eq_zero] using hz

end AEGIS.MeromorphicIdentityPreconnectedV11

#print axioms AEGIS.MeromorphicIdentityPreconnectedV11.eventuallyEq_nhdsNE_of_meromorphicOn_of_seed
