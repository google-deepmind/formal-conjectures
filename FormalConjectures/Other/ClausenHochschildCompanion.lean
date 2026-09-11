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
# Clausen's Hochschild companion conjecture

Clausen's modified Hodge conjecture predicts that a natural regulator comparison is an
equivalence. In the lecture below he states a *companion conjecture* about Hochschild homology,
observes that it "unwinds to something that looks completely unbelievable", and invites attempts
at it: proving positive-degree acyclicity would be "halfway to proving our conjecture". This file
states that companion conjecture. The modified Hodge conjecture itself is not formalized here.

Let `H = ℓ²(ℕ, ℂ)`, let `B(H)` be its algebra of bounded operators, and let `J∞` be the ideal of
operators whose approximation numbers decay faster than every inverse power. Approximation
numbers measure distance to operators factoring through `ℂⁿ`; on Hilbert space they are the
singular values, up to a shift in indexing. `RapidDecayOperator.mem_ideal_iff` proves that the
two-sided ideal used below is exactly this set of operators.

The ring `J∞` has no unit. The conjecture concerns its ordinary algebraic Hochschild complex
over `ℚ`, with `Chains ℚ J∞ n = J∞ ⊗_ℚ ⋯ ⊗_ℚ J∞` on `n + 1` factors and the usual alternating
boundary — not a unitalization, and not a completed tensor product. This is what distinguishes
the statement from the literature on entire and local cyclic homology of Schatten ideals, which
is topological. It predicts `ℂ` in degree zero and zero in every positive degree.

In the lecture the degree-zero value is stated for the category whose invariants `J∞` computes,
and positive-degree acyclicity for the Hochschild complex of `J∞` itself; the recording speaks of
a shift between the two without pinning it down. The normalization used here — the base field in
degree zero, zero above — is the one stated outright for the non-archimedean analogue, and is the
only one available to a complex concentrated in nonnegative degrees.

The map from `ℂ` is the explicit rank-one corner `z ↦ z P₀`, followed by passage to homology,
where `P₀` projects onto the coordinate-zero line. The ordinary operator trace is normalized on
this corner, so the corner specifies the inverse of the expected trace isomorphism.
`Hochschild.section_bijective_iff_trace_bijective` proves the corner and trace formulations
equivalent for any cyclic trace that the corner normalizes; the operator trace on `J∞` is not
itself constructed here, which is why the statement below is phrased with the corner.

`Hochschild.boundary_comp_boundary` proves that the boundary squares to zero in every degree, so
the second clause below is genuinely the vanishing of the homology of a complex; the same chain
complex is assembled as `Hochschild.chainComplex`.

The degree-zero clause is expected to be classical rather than open. Degree-zero homology is
`J∞ / [J∞, J∞]`, which coincides with `J∞ / [J∞, B(H)]` because every element of `J∞` is a
product of two, so `[a * b, c] = [a, b * c] + [b, c * a]` rewrites a commutator with a bounded
operator inside the ideal. That quotient is one dimensional, spanned by the trace: the tail sums
of a rapidly decaying sequence again decay rapidly, so `J∞` is stable under the arithmetic mean
at infinity, and for such ideals the commutator description of Dykema–Figiel–Weiss–Wodzicki
leaves a unique trace up to scalars. What Clausen asks for is the positive-degree clause.

Clausen notes that the non-archimedean analogue, with `ℚ_p` in degree zero, was proved by his
student Adriano Córdova by methods that do not proceed by analyzing the Hochschild complex.

## References

- [D. Clausen, *What is the K-theory of the Complex Numbers?*](https://www.ias.edu/video/what-k-theory-complex-numbers),
  Joint PU/IAS Arithmetic Geometry Seminar, 6 November 2023. The companion conjecture is stated
  at 1:05:01–1:06:55 of the [recording](https://www.youtube.com/watch?v=5QE__xdYtA0).
- [D. Clausen, *Three Perspectives on Deligne Cohomology*](https://www.math.ku.dk/english/calendar/events/masterclass-continuous-k-theory/Clausen1.pdf),
  whose Main Conjecture 4.5 is the modified Hodge conjecture; Remark 4.13 gives related
  categorical Hochschild background, not the statement formalized here.
- [D. Clausen's answer on the modified Hodge conjecture](https://mathoverflow.net/questions/446978/clausens-modified-hodge-conjecture).
- [K. Dykema, T. Figiel, G. Weiss, M. Wodzicki, *Commutator structure of operator
  ideals*](https://math.berkeley.edu/~wodzicki/prace/Advances-185.pdf), Adv. Math. 185 (2004)
  1–79, doi:10.1016/S0001-8708(03)00141-5; Theorem 5.6 describes the commutator space of an
  operator ideal.
- [V. Kaftal, G. Weiss, *Traces on operator ideals and arithmetic
  means*](https://arxiv.org/abs/0707.3169), arXiv:0707.3169; Theorem 6.6 identifies the ideals of
  trace class operators carrying a unique trace as the arithmetic-mean-at-infinity stable ones.
-/

namespace ClausenHochschildCompanion

open RapidDecayOperator

/-- The concrete rank-one comparison from `ℂ` to degree-zero algebraic Hochschild homology
of the rapid-decay operator ideal, with tensor products over `ℚ`. -/
noncomputable def hochschildCorner : ℂ →ₗ[ℚ] Hochschild.HomologyZero ℚ ideal :=
  Hochschild.algebraClassZero ℚ ideal ∘ₗ rankOne.restrictScalars ℚ

/--
Clausen's Hochschild companion conjecture over the complex numbers.

For the nonunital algebra $J_\infty$, the map $z \mapsto [zP_0]$ identifies
$\mathbb C$ with $HH_0(J_\infty/\mathbb Q)$, and $HH_n(J_\infty/\mathbb Q)=0$
for every $n>0$. Tensor products are algebraic. The second clause expresses exactness
in each positive degree: `boundary n` maps degree `n + 1` to degree `n`, so the equality
holds in `Chains ℚ J∞ (n + 1)` and covers every degree from one upwards.

See [D. Clausen, *What is the K-theory of the Complex Numbers?*](https://www.ias.edu/video/what-k-theory-complex-numbers),
1:05:01–1:06:55 of the [recording](https://www.youtube.com/watch?v=5QE__xdYtA0).
-/
@[category research open, AMS 16 19 46]
theorem hochschild_companion_conjecture :
    Function.Bijective hochschildCorner ∧
      ∀ n : ℕ,
        LinearMap.range (Hochschild.boundary ℚ ideal (n + 1)) =
          LinearMap.ker (Hochschild.boundary ℚ ideal n) := by
  sorry

end ClausenHochschildCompanion
