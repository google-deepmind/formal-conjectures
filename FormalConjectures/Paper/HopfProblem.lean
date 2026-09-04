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
# The Hopf problem

Does the $6$-sphere admit a complex structure?

Posed by Heinz Hopf ([Ho48]), this is one of the oldest open problems of complex
geometry. The spheres admitting almost complex structures are exactly $S^2$ and
$S^6$ (Borel–Serre); on $S^2$ the structure is integrable, while on $S^6$ neither
the integrability of some almost complex structure nor its impossibility has been
established. LeBrun ([LB87]) showed that no complex structure on $S^6$ can be
orthogonal with respect to the round metric. Claimed resolutions in both
directions have so far not achieved community acceptance.

We formalise "complex structure" as a holomorphic atlas on the topological
$6$-sphere: a `ChartedSpace` structure modeled on $ℂ^3$ making the sphere an
analytic (`ω`) manifold over $ℂ$. This is equivalent to the classical statement
that the smooth $S^6$ carries an integrable almost complex structure: every
smooth homotopy $6$-sphere is diffeomorphic to the standard $S^6$ (Smale's
h-cobordism theorem together with $Θ_6 = 0$, Kervaire–Milnor), and integrable
almost complex structures correspond to holomorphic atlases by the
Newlander–Nirenberg theorem.

## References

* [Ho48] Hopf, H., *Zur Topologie der komplexen Mannigfaltigkeiten*,
  Studies and Essays Presented to R. Courant, Interscience, New York, 1948.
* [ABGKR18] Agricola, I., Bazzoni, G., Goertsches, O., Konstantis, P., Rollenske, S.,
  [*On the history of the Hopf problem*](https://arxiv.org/abs/1708.01068),
  Differ. Geom. Appl. 57 (2018).
* [An18] Angella, D.,
  [*Hodge numbers of a hypothetical complex structure on the six sphere*](https://arxiv.org/abs/1705.10518),
  Differ. Geom. Appl. 57 (2018), 105–120.
* [LB87] LeBrun, C., *Orthogonal complex structures on $S^6$*,
  Proc. Amer. Math. Soc. 101 (1987), 136–138.
-/

open scoped Manifold ContDiff

namespace HopfProblem

/--
**The Hopf problem.** Does the $6$-sphere admit a complex structure?

Formally: does the unit sphere in $ℝ^7$, with its subspace topology, carry a
charted-space structure modeled on $ℂ^3$ all of whose transition functions are
$ℂ$-analytic?
-/
@[category research open, AMS 32 53]
theorem hopf_problem :
    answer(sorry) ↔
      ∃ cs : ChartedSpace (EuclideanSpace ℂ (Fin 3))
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1),
        letI := cs
        IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) ω
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1) := by
  sorry

end HopfProblem
