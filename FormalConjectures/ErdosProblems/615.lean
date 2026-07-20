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
# Erdős Problem 615

A Ramsey–Turán problem of Erdős, Hajnal, Simonovits, Sós, and Szemerédi [EHSSS93]: does there
exist a constant $c > 0$ such that every graph on $n$ vertices with at least $(1/8 - c)n^2$
edges contains either a $K_4$ or an independent set on at least $n/\log n$ vertices? In the
notation of Ramsey–Turán theory this asks whether
$$\mathrm{rt}(n; 4, n/\log n) < (1/8 - c)n^2.$$

This was disproved by Fox, Loh, and Zhao [FLZ15], who showed that
$\mathrm{rt}(n; 4, ne^{-f(n)}) \geq (1/8 - o(1))n^2$ whenever
$f(n) = o(\sqrt{\log n/\log\log n})$. In the other direction Sudakov [Su03] had shown that
$\mathrm{rt}(n; 4, ne^{-f(n)}) = o(n^2)$ whenever $f(n)/\sqrt{\log n} \to \infty$.

*References:*
* [erdosproblems.com/615](https://www.erdosproblems.com/615)
* [EHSSS93] Erdős, P., Hajnal, A., Simonovits, M., Sós, V. T., and Szemerédi, E.,
  *Turán-Ramsey theorems and simple asymptotically extremal structures*. Combinatorica 13
  (1993), 31--56.
* [Su03] Sudakov, B., *A few remarks on Ramsey-Turán-type problems*. J. Combin. Theory Ser. B
  88 (2003), 99--106.
* [FLZ15] Fox, J., Loh, P.-S., and Zhao, Y., *The critical window for the classical
  Ramsey-Turán problem*. Combinatorica 35 (2015), 435--476.
-/

open Classical Filter SimpleGraph

namespace Erdos615

/--
Does there exist some constant $c > 0$ such that for all sufficiently large $n$, if $G$ is a
graph with $n$ vertices and at least $(1/8 - c)n^2$ edges then $G$ must contain either a $K_4$
or an independent set on at least $n/\log n$ vertices?

The answer is no, as shown by Fox, Loh, and Zhao [FLZ15].
-/
@[category research solved, AMS 5]
theorem erdos_615 : answer(False) ↔
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ (n : ℕ) in atTop,
      ∀ G : SimpleGraph (Fin n), (1 / 8 - c) * n ^ 2 ≤ G.edgeFinset.card →
        ¬ G.CliqueFree 4 ∨ (n : ℝ) / Real.log n ≤ G.indepNum := by
  sorry

/--
The result of Fox, Loh, and Zhao [FLZ15] disproving the problem: if $f(n) \geq 0$ satisfies
$f(n) = o(\sqrt{\log n/\log\log n})$, then for every $\epsilon > 0$ and all sufficiently
large $n$ there is a $K_4$-free graph on $n$ vertices with independence number at most
$ne^{-f(n)}$ and at least $(1/8 - \epsilon)n^2$ edges; that is,
$\mathrm{rt}(n; 4, ne^{-f(n)}) \geq (1/8 - o(1))n^2$. Applied with
$f(n) = \log\log n$, this disproves the headline problem, since
$ne^{-f(n)} = n/\log n = o(n)$.
-/
@[category research solved, AMS 5]
theorem erdos_615.variants.fox_loh_zhao (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (hfo : Tendsto (fun n : ℕ => f n / Real.sqrt (Real.log n / Real.log (Real.log n)))
      atTop (nhds 0)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ (n : ℕ) in atTop,
      ∃ G : SimpleGraph (Fin n), G.CliqueFree 4 ∧
        (G.indepNum : ℝ) ≤ n * Real.exp (-f n) ∧
        (1 / 8 - ε) * n ^ 2 ≤ G.edgeFinset.card := by
  sorry

/--
The complementary result of Sudakov [Su03]: if $f(n)/\sqrt{\log n} \to \infty$ then
$\mathrm{rt}(n; 4, ne^{-f(n)}) = o(n^2)$; that is, for every $\epsilon > 0$ and all
sufficiently large $n$, every $K_4$-free graph on $n$ vertices with independence number at
most $ne^{-f(n)}$ has at most $\epsilon n^2$ edges.
-/
@[category research solved, AMS 5]
theorem erdos_615.variants.sudakov (f : ℕ → ℝ)
    (hf : Tendsto (fun n : ℕ => f n / Real.sqrt (Real.log n)) atTop atTop)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ (n : ℕ) in atTop,
      ∀ G : SimpleGraph (Fin n), G.CliqueFree 4 →
        (G.indepNum : ℝ) ≤ n * Real.exp (-f n) →
        (G.edgeFinset.card : ℝ) ≤ ε * n ^ 2 := by
  sorry

/--
A sanity check for `erdos_615`: the empty graph on $n \geq 3$ vertices contains an independent
set on at least $n/\log n$ vertices (namely the whole vertex set), so it satisfies the
conclusion of the implication in the problem statement.
-/
@[category test, AMS 5]
theorem erdos_615.variants.test_bot (n : ℕ) (hn : 3 ≤ n) :
    (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    calc Real.exp 1 ≤ 3 := by
          have := Real.exp_one_lt_d9
          linarith
      _ ≤ n := hn'
  have h2 : (n : ℝ) / Real.log n ≤ n := div_le_self (by positivity) h1
  have h3 : (Finset.univ : Finset (Fin n)).card ≤ (⊥ : SimpleGraph (Fin n)).indepNum :=
    SimpleGraph.IsIndepSet.card_le_indepNum (by simp [SimpleGraph.isIndepSet_iff, Set.Pairwise])
  have h4 : (n : ℝ) ≤ (⊥ : SimpleGraph (Fin n)).indepNum := by exact_mod_cast by simpa using h3
  exact h2.trans h4

end Erdos615
