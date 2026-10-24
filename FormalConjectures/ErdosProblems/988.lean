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
# Erdős Problem 988

*References:*
- [erdosproblems.com/988](https://www.erdosproblems.com/988)
- [Er64b] Erdős, P., _Problems and results on diophantine approximations_. Compositio Math.
  (1964), 52-65.
- [Ro54] Roth, K. F., _On irregularities of distribution_. Mathematika (1954), 73--79.
- [Sc69b] Schmidt, Wolfgang M., _Irregularities of distribution. IV_. Invent. Math. (1969),
  55--82.
-/

@[expose] public section

open Filter MeasureTheory

namespace Erdos988

/-- The unit sphere $S^2\subseteq\mathbb{R}^3$. -/
abbrev Sphere : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The spherical cap $\{x\in S^2 : \langle x,u\rangle\geq t\}$ with centre `u` and inner-product
threshold `t ∈ [-1, 1]`. -/
def cap (u : Sphere) (t : ℝ) : Set Sphere :=
  {x | t ≤ inner ℝ (x : EuclideanSpace ℝ (Fin 3)) (u : EuclideanSpace ℝ (Fin 3))}

/-- The surface measure on the unit sphere, induced by Lebesgue measure on $\mathbb{R}^3$. -/
noncomputable def surface : Measure Sphere :=
  (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere

/-- The normalised surface measure $\alpha_C$ of a subset `C` of the sphere, so that the entire
sphere has measure $1$. -/
noncomputable def normalizedArea (C : Set Sphere) : ℝ :=
  (surface C).toReal / (surface Set.univ).toReal

open scoped Classical in
/-- The spherical cap discrepancy
$$D(P) = \max_C \lvert \lvert C\cap P\rvert - \alpha_C \lvert P\rvert \rvert$$
of a finite set `P ⊆ S²`, where the maximum is taken over all spherical caps $C$ and
$\alpha_C$ is the normalised surface measure of $C$. -/
noncomputable def discrepancy (P : Finset Sphere) : ℝ :=
  sSup {r | ∃ (u : Sphere) (t : ℝ), t ∈ Set.Icc (-1 : ℝ) 1 ∧
    r = |((P.filter (· ∈ cap u t)).card : ℝ) - normalizedArea (cap u t) * P.card|}

/-- The minimal spherical cap discrepancy $\min_{\lvert P\rvert=n}D(P)$ of an `n`-point subset
of the sphere. -/
noncomputable def minDiscrepancy (n : ℕ) : ℝ :=
  sInf {d | ∃ P : Finset Sphere, P.card = n ∧ d = discrepancy P}

/--
If $P\subseteq S^2$ is a subset of the unit sphere then define the discrepancy
$$D(P) = \max_C \lvert \lvert C\cap P\rvert - \alpha_C \lvert P\rvert \rvert,$$
where the maximum is taken over all spherical caps $C$, and $\alpha_C$ is the appropriately
normalised measure of $C$.

Is it true that
$$\min_{\lvert P\rvert=n}D(P)\to \infty$$
as $n\to \infty$?

This is true, and was proved (in any number of dimensions) by Schmidt [Sc69b]. Roth [Ro54]
proved that the answer is yes if we replace the sphere by a square.
-/
@[category research solved, AMS 11 52, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos988.lean#L2225"]
theorem erdos_988 : answer(True) ↔ Tendsto minDiscrepancy atTop atTop := by
  sorry

end Erdos988
