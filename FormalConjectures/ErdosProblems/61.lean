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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 61 -- Erdős–Hajnal Conjecture

*Reference:* [erdosproblems.com/61](https://www.erdosproblems.com/61)
-/

open Filter
open SimpleGraph
open Real

namespace Erdos61

/-
For a graph $H$, consider all graphs $G$ that do not contain $H$ as an induced subgraph.
We would like to find a lower bound $f(n)$ such that every such $G$ on $n$ vertices
has a clique or independent set of size $\ge f(n)$ for sufficiently large $n$.
-/
def IsErdosHajnalLowerBound {α : Type*} [Fintype α] [DecidableEq α]
  (H : SimpleGraph α) (f : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
    (¬∃ g : α ↪ Fin n, H = G.comap g) → G.indepNum ≥ f n ∨ G.cliqueNum ≥ f n

/--
The Erdős–Hajnal Conjecture states that there is a constant $c(H) > 0$ for each
$H$ such that we can take $f(n) = n^{c(H)}$ in the above formulation.
-/
@[category research open, AMS 5]
theorem erdos_61 :
    answer(sorry) ↔ ∀ {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
      ∃ c > (0 : ℝ), IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c) := by
  sorry

/--
Erdős and Hajnal [ErHa89] proved that we can take $f(n) = \exp(c_H \sqrt{\log n})$
for some constant $c_H > 0$ dependending on $H$.

[ErHa89] Erdős, P. and Hajnal, A., Ramsey-type theorems. Discrete Appl. Math. (1989), 37-52.
-/
@[category research solved, AMS 5]
theorem erdos_61.variants.erha89 :
    ∀ {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
      ∃ c > (0 : ℝ), IsErdosHajnalLowerBound H (fun n : ℕ => exp (c * sqrt (log n))) := by
  sorry

/--
Bucić, Nguyen, Scott, and Seymour [BNSS23] improved this to
$f(n) = \exp(c_H \sqrt{\log n \log \log n})$ for some constant $c_H > 0$ dependending on $H$.

[BNSS23] Bucić, M. and Nguyen, T. and Scott, A. and Seymour, P., A loglog step towards Erdos-Hajnal
-/
@[category research solved, AMS 5]
theorem erdos_61.variants.bnss23 :
    ∀ {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
      ∃ c > (0 : ℝ), IsErdosHajnalLowerBound H (fun n : ℕ => exp (c * sqrt (log n * log (log n)))) := by
  sorry

/--
Nguyen, Scott, and Seymour [NSS23] proved the conjecture for $H = P_5$, the path on five
vertices: every $P_5$-free graph on $n$ vertices has a clique or independent set of
polynomial size.

[NSS23] Nguyen, T., Scott, A. and Seymour, P., Induced subgraph density. VII. The
five-vertex path. [arXiv:2312.15333](https://arxiv.org/abs/2312.15333)
-/
@[category research solved, AMS 5]
theorem erdos_61.variants.p5 :
    ∃ c > (0 : ℝ), IsErdosHajnalLowerBound (pathGraph 5) (fun n : ℕ => (n : ℝ) ^ c) := by
  sorry

/--
Chudnovsky, Scott, Seymour, and Spirkl [CSSS23] proved the conjecture for $H = C_5$, the
cycle on five vertices: every graph with no induced five-cycle has a clique or independent
set of polynomial size.

[CSSS23] Chudnovsky, M., Scott, A., Seymour, P. and Spirkl, S., Erdős–Hajnal for graphs with
no 5-hole. Proc. Lond. Math. Soc. (3) 126 (2023), 997–1014.
-/
@[category research solved, AMS 5]
theorem erdos_61.variants.c5 :
    ∃ c > (0 : ℝ), IsErdosHajnalLowerBound (cycleGraph 5) (fun n : ℕ => (n : ℝ) ^ c) := by
  sorry

end Erdos61
