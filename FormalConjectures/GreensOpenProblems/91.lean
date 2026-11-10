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
# Ben Green's Open Problem 91

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.91)
- [FKNSS22] Ferber, A., Kwan, M., Narayanan, B., Sah, A. and Sawhney, M., *Friendly bisections of
  random graphs*. Comm. Amer. Math. Soc. 2 (2022), 380--416.
  [arXiv:2105.13337](https://arxiv.org/abs/2105.13337)
- [MSS24] Minzer, D., Sah, A. and Sawhney, M., *On perfectly friendly bisections of random
  graphs*. Ann. Probab. 52 (2024), 2281--2341.
  [arXiv:2305.03543](https://arxiv.org/abs/2305.03543)
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace Green91

/--
`prob n P` is the probability that the random graph $G(n, 1/2)$ on the vertex set `Fin n` has the
property `P`. Each edge is present independently with probability $1/2$, so every graph has the
same probability $2^{-\binom{n}{2}}$.
-/
noncomputable def prob (n : ℕ) (P : SimpleGraph (Fin n) → Prop) : ENNReal :=
  SimpleGraph.binomialRandom (Fin n) ⟨1 / 2, by norm_num⟩ {G | P G}

open scoped Classical in
/--
`friendliness G s v` is the number of neighbours of `v` on its own side minus the number of
neighbours of `v` on the other side, for the partition of the vertices into `s` and its
complement. This is the quantity $\Delta(v)$ of [FKNSS22, Section 2].
-/
noncomputable def friendliness {n : ℕ} (G : SimpleGraph (Fin n)) (s : Finset (Fin n))
    (v : Fin n) : ℤ :=
  ((Finset.univ.filter fun w ↦ G.Adj v w ∧ (w ∈ s ↔ v ∈ s)).card : ℤ) -
    (Finset.univ.filter fun w ↦ G.Adj v w ∧ ¬ (w ∈ s ↔ v ∈ s)).card

open scoped Classical in
/--
`numFriendly G s` is the number of vertices that have more neighbours on their own side than on
the other side (*friendly* vertices in [FKNSS22]), for the partition of the vertices into `s` and
its complement. A vertex with equally many neighbours on both sides is not friendly.
-/
noncomputable def numFriendly {n : ℕ} (G : SimpleGraph (Fin n)) (s : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter fun v ↦ 0 < friendliness G s v).card

/--
Take a random graph $G(n, \frac{1}{2})$. Is there almost surely a bipartition of $G$ into two sets
of $n/2$ vertices with the property that $99\%$ of vertices have more neighbours on their own side
than on the other?

We read "almost surely" as "with probability tending to $1$ as $n \to \infty$", and "$99\%$ of
vertices" as at least $\frac{99}{100} n$ vertices. A bisection is the partition into a set `s` with
$\lfloor n/2 \rfloor$ elements and its complement; for odd $n$ the parts have sizes differing by
one, as in [FKNSS22]. [Gr24] writes that the question "was apparently asked by Füredi in 1988".
The answer is yes
[FKNSS22, Theorem 1.1], see `green_91.variants.fknss`.
-/
@[category research solved, question, AMS 5 60]
theorem green_91 :
    Tendsto (fun n : ℕ ↦ prob n fun G ↦
      ∃ s : Finset (Fin n), s.card = n / 2 ∧ (99 / 100 : ℝ) * n ≤ numFriendly G s)
      atTop (𝓝 1) := by
  sorry

/--
**Ferber, Kwan, Narayanan, Sah and Sawhney.** With high probability, $G(n, \frac{1}{2})$ admits a
bisection in which $n - o(n)$ vertices are friendly [FKNSS22, Theorem 1.1]. A vertex is friendly
if it has more neighbours in its own part than across, and a bisection is a partition into two
parts whose sizes differ by at most one. This implies `green_91`.
-/
@[category research solved, AMS 5 60]
theorem green_91.variants.fknss :
    ∃ f : ℕ → ℝ, f =o[atTop] (fun n : ℕ ↦ (n : ℝ)) ∧
      Tendsto (fun n : ℕ ↦ prob n fun G ↦
        ∃ s : Finset (Fin n), s.card = n / 2 ∧ (n : ℝ) - f n ≤ numFriendly G s)
        atTop (𝓝 1) := by
  sorry

/--
Is there almost surely a bipartition of $G(n, \frac{1}{2})$ into two sets of $n/2$ vertices with
the property that all vertices have more neighbours on their own side than on the other?

[Gr24] reports that the authors of [FKNSS22] believe this may be true. Minzer, Sah and Sawhney
[MSS24, Theorem 1.3] prove it, conditional on a numerical hypothesis [MSS24, Assumption 1.5] that
they check by computer, partly with interval arithmetic and partly in floating point only. Under
the same hypothesis they find the critical margin: for every $\varepsilon > 0$, with high
probability there is a bisection in which every vertex has at least
$(\gamma - \varepsilon)\sqrt{n}$ more neighbours in its own part than in the other, but none with
$(\gamma + \varepsilon)\sqrt{n}$. Here $\gamma = \gamma_{\mathrm{crit}} / \sqrt{2} \approx 0.17566$,
and $\gamma_{\mathrm{crit}}$ is defined by an optimisation problem for Gaussian tail
probabilities [MSS24, Definition 1.2].
-/
@[category research solved, question, AMS 5 60]
theorem green_91.variants.all_friendly :
    Tendsto (fun n : ℕ ↦ prob n fun G ↦
      ∃ s : Finset (Fin n), s.card = n / 2 ∧ ∀ v, 0 < friendliness G s v)
      atTop (𝓝 1) := by
  sorry

end Green91
