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
# Rokhlin's multiple-mixing problem

An invertible measure-preserving transformation $T$ of a probability space is *mixing* if
$\mu(A \cap T^{-n} B) \to \mu(A)\mu(B)$ as $|n| \to \infty$, and *mixing of order $k$* if
$$\mu\bigl(A_1 \cap T^{-t_2} A_2 \cap \cdots \cap T^{-t_k} A_k\bigr) \to
  \mu(A_1) \cdots \mu(A_k)$$
as $0 = t_1 < t_2 < \cdots < t_k$ and the gaps $t_{i+1} - t_i$ all tend to infinity.
Rokhlin [Ro49] asked whether mixing implies mixing of order $3$, and more generally of every
order. Here the order is the number of sets, as in [dlR06].

*References:*
- [Ro49] V. A. Rokhlin, *On endomorphisms of compact commutative groups*,
  Izv. Akad. Nauk SSSR Ser. Mat. 13 (1949), 329–340.
- [Ka84] S. A. Kalikow, *Twofold mixing implies threefold mixing for rank one
  transformations*, Ergodic Theory Dynam. Systems 4 (1984), 237–259.
- [Ho91] B. Host, *Mixing of all orders and pairwise independent joinings of systems with
  singular spectrum*, Israel J. Math. 76 (1991), 289–298.
- [dlR06] T. de la Rue, *2-fold and 3-fold mixing: why 3-dot-type counterexamples are
  impossible in one dimension*, Bull. Braz. Math. Soc. (N.S.) 37 (2006), 503–521.
- [OAI26] OpenAI, *Rokhlin's multiple-mixing problem for one transformation*. OpenAI Math
  Release preprint (2026).
  https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace RokhlinMultipleMixing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The iterate $T^n$ for $n \in \mathbb{Z}$. -/
def timeMap (T : Ω ≃ᵐ Ω) (n : ℤ) : Ω → Ω :=
  ⇑((T.toEquiv : Equiv.Perm Ω) ^ n)

/-- $T$ is *mixing*: $\mu(A \cap T^{-n} B) \to \mu(A)\mu(B)$ as $|n| \to \infty$. -/
def IsMixing (μ : Measure Ω) (T : Ω ≃ᵐ Ω) : Prop :=
  ∀ A B : Set Ω, MeasurableSet A → MeasurableSet B →
    Tendsto (fun n : ℤ => μ (A ∩ timeMap T n ⁻¹' B))
      (comap Int.natAbs atTop) (𝓝 (μ A * μ B))

/-- The times $t_i = g_1 + \cdots + g_{i-1}$ given by the positive gaps $g_j$. -/
def layoutTime {k : ℕ} (gaps : Fin (k - 1) → ℕ+) (i : Fin k) : ℕ :=
  ∑ j : Fin (k - 1), if j.val < i.val then (gaps j : ℕ) else 0

/-- $T$ is *mixing of order $k$*: the measure of $\bigcap_i T^{-t_i} A_i$ tends to
$\prod_i \mu(A_i)$ as all gaps between consecutive times tend to infinity. -/
def MixingOfOrder (μ : Measure Ω) (T : Ω ≃ᵐ Ω) (k : ℕ) : Prop :=
  ∀ A : Fin k → Set Ω, (∀ i, MeasurableSet (A i)) →
    Tendsto
      (fun gaps : Fin (k - 1) → ℕ+ =>
        μ (⋂ i : Fin k, timeMap T (layoutTime gaps i : ℤ) ⁻¹' A i))
      atTop (𝓝 (∏ i : Fin k, μ (A i)))

/--
**Rokhlin's multiple-mixing problem.** Every invertible mixing measure-preserving transformation
of a probability space is mixing of every order $k \ge 3$.

Kalikow proved this for rank-one transformations [Ka84] and Host for transformations with
singular spectrum [Ho91]. An internal OpenAI model proved it in general in September
2026 [OAI26]. Rokhlin's original question is the case $k = 3$.
-/
@[category research solved, AMS 28 37]
theorem rokhlin_multiple_mixing (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω ≃ᵐ Ω)
    (hT : MeasurePreserving T μ μ) (hmix : IsMixing μ T) :
    ∀ k : ℕ, 3 ≤ k → MixingOfOrder μ T k := by
  sorry

end RokhlinMultipleMixing
