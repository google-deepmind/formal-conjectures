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
public import FormalConjectures.ErdosProblems.«988»

/-!
# Erdős Problem 991

*References:*
- [erdosproblems.com/991](https://www.erdosproblems.com/991)
- [Er64b] Erdős, P., _Problems and results on diophantine approximations_. Compositio Math.
  (1964), 52-65.
- [Br08] Brauchart, J. S., _Optimal logarithmic energy points on the unit sphere_. Math. Comp.
  (2008), 1599--1613.
- [MaMa21] Marzo, Jordi and Mas, Albert, _Discrepancy of minimal Riesz energy points_. Constr.
  Approx. (2021), 473--506.
-/

@[expose] public section

open Filter Asymptotics Erdos988

namespace Erdos991

open scoped Classical in
/-- The product $\prod_{i<j}\lvert w_i-w_j\rvert$ of the distances between the points of `A`. -/
noncomputable def distanceProduct (A : Finset Sphere) : ℝ :=
  ∏ e ∈ A.sym2.filter (fun e ↦ ¬ e.IsDiag), Sym2.lift ⟨dist, dist_comm⟩ e

/-- `A` maximises $\prod_{i<j}\lvert w_i-w_j\rvert$ over all subsets of the sphere of the same
size (a set of *Fekete points*). -/
def IsDistanceProductMaximizer (A : Finset Sphere) : Prop :=
  ∀ B : Finset Sphere, B.card = A.card → distanceProduct B ≤ distanceProduct A

/--
Suppose $A=\{w_1,\ldots,w_n\}\subset S^2$ maximises
$$\prod_{i<j}\lvert w_i-w_j\rvert$$
over all possible sets of size $n$. Is it true that
$$\max_C\lvert \lvert A\cap C\rvert - \alpha_C n\rvert =o(n),$$
where the maximum is taken over all spherical caps $C$ and $\alpha_C$ is the area of $C$
(normalised so that the entire sphere has area $1$)?

This is certainly solved, although it is unclear exactly who to attribute this to. Brauchart
[Br08] says that this qualitative result follows from 'classical potential theory', and proves
a quantitative decay rate of $\ll n^{3/4}$. Marzo and Mas [MaMa21] give a proof of
$\ll n^{2/3}$ (as a special case of a more general result).

See also [988](https://www.erdosproblems.com/988).
-/
@[category research solved, AMS 11 31 52, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos991.lean#L187"]
theorem erdos_991 : answer(True) ↔
    ∀ A : ℕ → Finset Sphere, (∀ n, (A n).card = n) →
      (∀ n, IsDistanceProductMaximizer (A n)) →
        (fun n : ℕ ↦ discrepancy (A n)) =o[atTop] fun n : ℕ ↦ (n : ℝ) := by
  sorry

/-- Brauchart [Br08] proves a quantitative decay rate of $\ll n^{3/4}$; Marzo and Mas [MaMa21]
give a proof of $\ll n^{2/3}$. -/
@[category research solved, AMS 11 31 52]
theorem erdos_991.variants.marzo_mas :
    ∃ C : ℝ, ∀ A : Finset Sphere, IsDistanceProductMaximizer A →
      discrepancy A ≤ C * (A.card : ℝ) ^ (2 / 3 : ℝ) := by
  sorry

end Erdos991
