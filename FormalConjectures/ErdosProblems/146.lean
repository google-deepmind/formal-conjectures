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
# Erdős Problem 146

*References:*
- [erdosproblems.com/146](https://www.erdosproblems.com/146)
- [ErSi84] Erdős, P. and Simonovits, M., *Cube-supersaturated graphs and related problems*.
  Progress in graph theory (1984), 203-218.
- [AKS03] Alon, Noga and Krivelevich, Michael and Sudakov, Benny, *Turán numbers of bipartite
  graphs and related Ramsey-type questions*. Combin. Probab. Comput. **12** (2003), 477-494.
- [OpenAI26] OpenAI, *Ten advances in mathematics and theoretical computer science*, Ch. 10 (2026).
  <https://cdn.openai.com/pdf/ten-proofs-oai.pdf>, Lean development at
  <https://github.com/openai/ten-proofs>. Chapter 10 refutes the conjecture, at $r=2$.
- [FGLO26] Claude Fable 5, Sai Gajjala, Christian Lewis, and Claude Opus 5, *The Erdős–Simonovits
  degeneracy conjecture is false for all $r \geq 2$*, draft (2026).
  <https://github.com/EvolvingPrograms/erdos-simonovits-degeneracy>. Generalises the construction
  of [OpenAI26, Ch. 10] to every $r$, and builds on its Lean development.

Here $r$-degeneracy is `SimpleGraph.IsDegenerate` and $\mathrm{ex}(n;H)$ is Mathlib's
`SimpleGraph.extremalNumber`.
-/

open Filter SimpleGraph

namespace Erdos146

/--
If $H$ is bipartite and is $r$-degenerate, that is, every induced subgraph of $H$ has minimum
degree $\leq r$, then
$$\mathrm{ex}(n;H) \ll n^{2-1/r}.$$

The answer is no. OpenAI [OpenAI26] give a connected bipartite `2`-degenerate `H` and constants
`c, ε > 0` with $\mathrm{ex}(n;H)\geq cn^{3/2+\epsilon}$ for all large `n`, which exceeds the
conjectured $n^{2-1/2}=n^{3/2}$. See `erdos_146.variants.two_degenerate_counterexample`.
-/
@[category research solved, AMS 5]
theorem erdos_146 : answer(False) ↔
    ∀ (r q : ℕ) (H : SimpleGraph (Fin q)),
      0 < r → H.IsBipartite → H.IsDegenerate r →
        Asymptotics.IsBigO atTop
          (fun n : ℕ => (extremalNumber n H : ℝ))
          (fun n : ℕ => (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ))) := by
  sorry

/--
The counterexample: a connected bipartite `2`-degenerate `H` whose extremal number exceeds
$n^{3/2+\epsilon}$ infinitely often, so the `r = 2` case of `erdos_146` fails.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean"]
theorem erdos_146.variants.two_degenerate_counterexample :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧ H.IsBipartite ∧ H.IsDegenerate 2 ∧
      ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((3 : ℝ) / 2 + ε) ≤ (extremalNumber n H : ℝ) := by
  sorry

/-- Sanity check for `SimpleGraph.IsDegenerate`: a triangle has degeneracy exactly $2$, since every
nonempty subset of its vertices contains a vertex with at most $2$ neighbours inside it, but the
whole vertex set contains none with at most $1$. -/
@[category test, AMS 5]
theorem isDegenerate_top_fin_three :
    (⊤ : SimpleGraph (Fin 3)).IsDegenerate 2 ∧ ¬ (⊤ : SimpleGraph (Fin 3)).IsDegenerate 1 := by
  rw [isDegenerate_iff_of_decidableRel, isDegenerate_iff_of_decidableRel]
  constructor <;> decide

/-- A single bipartite $r$-degenerate graph whose extremal number is eventually at least
$c\,n^{2-1/r+\varepsilon}$, for some $c, \varepsilon > 0$, refutes the conjectured bound: the
polynomial gain $n^\varepsilon$ outgrows any constant. -/
@[category API, AMS 5]
theorem not_bigO_of_lower_bound {q r : ℕ} {H : SimpleGraph (Fin q)} {c ε : ℝ}
    (hr : 0 < r) (hbip : H.IsBipartite) (hdeg : H.IsDegenerate r) (hc : 0 < c) (hε : 0 < ε)
    (hlow : ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + ε) ≤ (extremalNumber n H : ℝ)) :
    ¬ ∀ (r q : ℕ) (H : SimpleGraph (Fin q)),
        0 < r → H.IsBipartite → H.IsDegenerate r →
          Asymptotics.IsBigO atTop
            (fun n : ℕ => (extremalNumber n H : ℝ))
            (fun n : ℕ => (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ))) := by
  intro hconj
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp (hconj r q H hr hbip hdeg)
  -- `c * n ^ ε` eventually exceeds the `O`-constant `C`.
  have hgrow : ∀ᶠ n : ℕ in atTop, C < c * (n : ℝ) ^ ε := by
    have : Tendsto (fun n : ℕ => c * (n : ℝ) ^ ε) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hc
        ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop)
    exact this.eventually_gt_atTop C
  have : ∀ᶠ _ : ℕ in atTop, False := by
    filter_upwards [hlow, hC, hgrow, eventually_gt_atTop 0] with n hlow hC hgrow hn
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hpow : (0 : ℝ) < (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) := Real.rpow_pos_of_pos hn' _
    rw [Real.norm_natCast, Real.norm_of_nonneg hpow.le] at hC
    rw [Real.rpow_add hn'] at hlow
    nlinarith [mul_le_mul_of_nonneg_right hgrow.le hpow.le]
  exact this.exists.elim fun _ h => h

/--
A counterexample at every level $r \geq 2$: for every $r \geq 2$ there is a connected bipartite
graph $H_r$ of degeneracy exactly $r$ — that is, $H_r$ is $r$-degenerate but not
$(r-1)$-degenerate — and a constant $c > 0$ with
$$\mathrm{ex}(n;H_r) \geq c\,n^{2-\frac{1}{r}+\frac{1}{28r^2}}$$
for all sufficiently large $n$. The exponent exceeds $2-1/r$ by a polynomial margin (see
`not_bigO_of_lower_bound`).

Due to [FGLO26], which strengthens the solution of [OpenAI26, Ch. 10] to every $r$ by leaving free
the Gibbs weight [OpenAI26] fixed numerically, and which imports the [OpenAI26] Lean development.
It does not subsume the $r=2$ case: the [OpenAI26] bound optimises the Hamming radius freely, and
the bound below does not imply it.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/EvolvingPrograms/erdos-simonovits-degeneracy/blob/87510f34a7ffc521f7dd6d9b3978ba0b560a92d3/Theorem2.lean"]
theorem erdos_146.variants.counterexample (r : ℕ) (hr : 2 ≤ r) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧ H.IsBipartite ∧ H.IsDegenerate r ∧ ¬ H.IsDegenerate (r - 1) ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + 1 / (28 * (r : ℝ) ^ 2)) ≤
            (extremalNumber n H : ℝ) := by
  sorry

/--
At $r=3$ the exponent of `erdos_146.variants.counterexample` improves from
$\frac{5}{3}+\frac{1}{252}$ to $\frac{5}{3}+\frac{1}{160}$: there is a connected bipartite
graph $H$ of degeneracy exactly $3$ and a constant $c>0$ with
$$\mathrm{ex}(n;H) \geq c\,n^{\frac{5}{3}+\frac{1}{160}}$$
for all sufficiently large $n$. Due to [FGLO26]; as with
`erdos_146.variants.counterexample`, this strengthens the solution of [OpenAI26, Ch. 10] and builds
on its Lean development.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/EvolvingPrograms/erdos-simonovits-degeneracy/blob/87510f34a7ffc521f7dd6d9b3978ba0b560a92d3/Theorem1.lean"]
theorem erdos_146.variants.counterexample_three :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧ H.IsBipartite ∧ H.IsDegenerate 3 ∧ ¬ H.IsDegenerate 2 ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((5 : ℝ) / 3 + 1 / 160) ≤ (extremalNumber n H : ℝ) := by
  sorry

end Erdos146
