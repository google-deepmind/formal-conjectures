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
# The Birch and Swinnerton-Dyer (BSD) Conjecture

*References:*
- [The Clay Institute](https://www.claymath.org/millennium/birch-and-swinnerton-dyer-conjecture/),
  official problem description by Andrew Wiles:
  [PDF](https://www.claymath.org/wp-content/uploads/2022/05/birchswin.pdf)
- [BSD1965] B. J. Birch and H. P. F. Swinnerton-Dyer. "Notes on elliptic curves. II."
  Journal fur die reine und angewandte Mathematik 218 (1965), 79-108,
  [doi](https://doi.org/10.1515/crll.1965.218.79)
- [Tate1966] John Tate. "On the conjectures of Birch and Swinnerton-Dyer and a geometric analog."
  Seminaire Bourbaki, Vol. 9, Exp. No. 306 (1966), 415-440,
  [numdam](https://www.numdam.org/item/SB_1964-1966__9__415_0/)
- [Gross2011] Benedict H. Gross. "Lectures on the conjecture of Birch and Swinnerton-Dyer."
  Arithmetic of L-functions, IAS/Park City Math. Ser. 18, AMS (2011), 169-209,
  [PDF](https://people.math.harvard.edu/~gross/preprints/lectures-pcmi.pdf)
- [Ang2025] David Kurniadi Angdinata. "L-functions of Dirichlet twists of elliptic curves:
  computations and congruences." PhD thesis, University College London (2025),
  [PDF](https://discovery.ucl.ac.uk/10223687/1/main-pages.pdf)
- [Ada] Tom Adamczewski. "Autoformalized conjectures",
  [Birch and Swinnerton-Dyer](https://tadamcz.com/autoformalization-results/#/p/wp-birch-and-swinnerton-dyer-conjecture)
-/

namespace BirchSwinnertonDyer

variable {K : Type*} [Field K] [NumberField K] {E : WeierstrassCurve K}

def IsLFunction (E : WeierstrassCurve K) (L : ℂ → ℂ) : Prop :=
  Differentiable ℂ L ∧ ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s

/-- The $L$-function of `E` is unique: two entire functions agreeing with
`WeierstrassCurve.LSeries` on $\operatorname{Re}(s) > 3/2$ agree everywhere. -/
@[category API, AMS 11 14]
theorem IsLFunction.unique {L L' : ℂ → ℂ} (hL : IsLFunction E L) (hL' : IsLFunction E L') :
    L = L' := by
  refine AnalyticOnNhd.eq_of_eventuallyEq (Complex.analyticOnNhd_univ_iff_differentiable.2 hL.1)
    (Complex.analyticOnNhd_univ_iff_differentiable.2 hL'.1) (z₀ := 2) ?_
  have hopen : IsOpen {s : ℂ | 3 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
  rw [hL.2 s hs, hL'.2 s hs]

/-- Every special value $L(E, s)$ is well defined, in particular the central value $L(E, 1)$
and the order of vanishing $\operatorname{ord}_{s = 1} L(E, s)$ appearing in the conjecture. -/
@[category API, AMS 11 14]
theorem IsLFunction.apply_eq {L L' : ℂ → ℂ} (hL : IsLFunction E L) (hL' : IsLFunction E L')
    (s : ℂ) : L s = L' s :=
  congrFun (hL.unique hL') s

/-- **Hasse--Weil conjecture** for elliptic curves over $\mathbb{Q}$, a consequence of the modularity
theorem: the $L$-function of an elliptic curve over $\mathbb{Q}$ extends to an entire function.
Over a general number field this is open. -/
@[category research solved, AMS 11 14]
theorem exists_isLFunction (E : WeierstrassCurve ℚ) [E.IsElliptic] : ∃ L, IsLFunction E L := by
  sorry

end BirchSwinnertonDyer
