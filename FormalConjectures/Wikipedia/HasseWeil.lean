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
# The Hasse--Weil conjecture for elliptic curves

The $L$-series $L(E, s)$ of an elliptic curve $E$ over a number field converges absolutely on
$\operatorname{Re} s > 3/2$ ([Tate1966], p. 416; [Gross2011], Lecture 2, §1). The **Hasse--Weil
conjecture** predicts that it has an analytic continuation to the whole complex plane and satisfies
a functional equation ([Tate1966], p. 416; [Gross2011], Conjecture 2.7, stated there for the
completed $L$-function). Only the continuation is stated here. Over $\mathbb{Q}$ it follows from
the modularity theorem.

[Wikipedia] states the conjecture for the Hasse--Weil zeta function and asks only for a
meromorphic continuation, which is equivalent to a meromorphic continuation of $L(E, s)$. That
weaker form is the one the Birch and Swinnerton-Dyer conjecture rests on, so it is recorded here as
well. [Gross2011], Conjecture 2.10 takes it as a hypothesis; a statement of that conjecture which
instead asserts the continuation implies `exists_hasMeromorphicContinuation` below.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Hasse%E2%80%93Weil_zeta_function#Hasse%E2%80%93Weil_conjecture)
- [Tate1966] John Tate. "On the conjectures of Birch and Swinnerton-Dyer and a geometric analog."
  Seminaire Bourbaki, Vol. 9, Exp. No. 306 (1966), 415-440,
  [numdam](https://www.numdam.org/item/SB_1964-1966__9__415_0/)
- [Gross2011] Benedict H. Gross. "Lectures on the conjecture of Birch and Swinnerton-Dyer."
  Arithmetic of L-functions, IAS/Park City Math. Ser. 18, AMS (2011), 169-209,
  [math.harvard.edu](https://people.math.harvard.edu/~gross/preprints/lectures-pcmi.pdf)
-/

namespace HasseWeil

section NumberField

variable {K : Type*} [Field K] [NumberField K] {E : WeierstrassCurve K}

/-- The $L$-series of `E` has the meromorphic continuation `L`: `L` is meromorphic on
$\mathbb{C}$ and agrees with `E.LSeries` on $\operatorname{Re} s > 3/2$, where the series
converges absolutely. -/
def HasMeromorphicContinuation (E : WeierstrassCurve K) (L : ℂ → ℂ) : Prop :=
  Meromorphic L ∧ ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s

/-- The $L$-series of `E` has the analytic continuation `L`: `L` is analytic on
$\mathbb{C}$ and agrees with `E.LSeries` on $\operatorname{Re} s > 3/2$, where the series
converges absolutely. -/
def HasAnalyticContinuation (E : WeierstrassCurve K) (L : ℂ → ℂ) : Prop :=
  (∀ z, AnalyticAt ℂ L z) ∧ ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s

/-- An analytic continuation is a meromorphic continuation. -/
@[category API, AMS 11 14]
theorem HasAnalyticContinuation.hasMeromorphicContinuation {L : ℂ → ℂ}
    (hL : HasAnalyticContinuation E L) : HasMeromorphicContinuation E L :=
  ⟨fun z ↦ (hL.1 z).meromorphicAt, hL.2⟩

open scoped Topology in
/-- A meromorphic continuation is unique away from isolated points: two meromorphic
continuations of the $L$-series of `E` agree on a punctured neighbourhood of every point. They may
differ at isolated points, since `Meromorphic` does not constrain the value of a function at any
single point. -/
@[category API, AMS 11 14]
theorem HasMeromorphicContinuation.unique {L L' : ℂ → ℂ}
    (hL : HasMeromorphicContinuation E L) (hL' : HasMeromorphicContinuation E L') (x : ℂ) :
    L =ᶠ[𝓝[≠] x] L' := by
  have h2 : meromorphicOrderAt (L - L') 2 = ⊤ := meromorphicOrderAt_eq_top_iff.2 <|
    Filter.eventually_of_mem (nhdsWithin_le_nhds <| (Complex.isOpen_re_gt (3 / 2)).mem_nhds
      (by norm_num)) fun s hs ↦ sub_eq_zero.2 ((hL.2 s hs).trans (hL'.2 s hs).symm)
  have key : meromorphicOrderAt (L - L') x = ⊤ := not_not.1 fun hx ↦
    (hL.1.sub hL'.1).exists_meromorphicOrderAt_ne_top_iff_forall.1 ⟨x, hx⟩ 2 h2
  exact (meromorphicOrderAt_eq_top_iff.1 key).mono fun s hs ↦ sub_eq_zero.1 hs

/-- The $L$-series of an elliptic curve over a number field has a meromorphic continuation to
$\mathbb{C}$. This is the **Hasse--Weil conjecture** in the form stated in [Wikipedia], and a weak
form of [Gross2011], Conjecture 2.7. It is also what the Birch and Swinnerton-Dyer conjecture rests
on, as the hypothesis of [Gross2011], Conjecture 2.10. -/
@[category research open, AMS 11 14]
theorem exists_hasMeromorphicContinuation (E : WeierstrassCurve K) [E.IsElliptic] :
    ∃ L, HasMeromorphicContinuation E L := by
  sorry

/-- The **Hasse--Weil conjecture** ([Tate1966], p. 416; [Gross2011], Conjecture 2.7): the
$L$-series of an elliptic curve over a number field has an analytic continuation to $\mathbb{C}$.
-/
@[category research open, AMS 11 14]
theorem exists_hasAnalyticContinuation (E : WeierstrassCurve K) [E.IsElliptic] :
    ∃ L, HasAnalyticContinuation E L := by
  sorry

end NumberField

/-- The **Hasse--Weil conjecture** over $\mathbb{Q}$: the $L$-series of an elliptic curve over
$\mathbb{Q}$ has an analytic continuation to $\mathbb{C}$. This follows from the modularity
theorem, see [Wikipedia]. -/
@[category research solved, AMS 11 14]
theorem exists_hasAnalyticContinuation_rat (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ L, HasAnalyticContinuation E L := by
  sorry

end HasseWeil
