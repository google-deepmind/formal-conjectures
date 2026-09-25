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
# Erdős Problem 746

*References:*
- [erdosproblems.com/746](https://www.erdosproblems.com/746)
- [Er71] Erdős, P., Some unsolved problems in graph theory and combinatorial analysis.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Er81] Erdős, P., On the combinatorial problems which I would most like to see solved.
  Combinatorica (1981), 25-42.
- [Er82e] Erdős, Paul, Some of my favourite problems which recently have been solved. (1982),
  59--79.
- [ErRe66] Erdős, P. and Rényi, A., On the existence of a factor of degree one of a connected
  random graph. Acta Math. Acad. Sci. Hungar. (1966), 359-368.
- [Po76] Pósa, L., Hamiltonian circuits in random graphs. Discrete Math. (1976), 359-364.
- [Ko77] Koršunov, A. D., Solution of a problem of P. Erdős and A. Rényi on Hamiltonian cycles
  in nonoriented graphs. Diskret. Analiz (1977), 17--56, 90.
- [KoSz83] Komlós, János and Szemerédi, Endre, Limit distribution for the existence of
  Hamiltonian cycles in a random graph. Discrete Math. (1983), 55-63.
-/

@[expose] public section

open Filter Real Topology SimpleGraph

namespace Erdos746

open scoped Classical in
/-- The probability that the random graph `G(n, m)`, chosen uniformly among the labelled graphs
on `n` vertices with exactly `m` edges, satisfies `P`. -/
noncomputable def probability (n m : ℕ) (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  ((Finset.univ.filter fun G : SimpleGraph (Fin n) ↦ G.edgeFinset.card = m ∧ P G).card : ℝ) /
    (Finset.univ.filter fun G : SimpleGraph (Fin n) ↦ G.edgeFinset.card = m).card

/--
Is it true that, almost surely, a random graph on $n$ vertices with $\geq (\tfrac{1}{2}+\epsilon)n\log n$
edges is Hamiltonian?

A conjecture of Erdős and Rényi [ErRe66], who proved that almost surely such a graph has a perfect
matching (when $n$ is even).

This is true. Pósa [Po76] proved that almost surely a random graph with $\geq Cn\log n$ edges is
Hamiltonian for some large constant $C$, and Korshunov [Ko77] proved that
$\geq \frac{1}{2}n\log n+\frac{1}{2}n\log\log n+w(n)n$ edges suffices, for any function $w$ which
$\to \infty$ as $n\to \infty$. Komlós and Szemerédi [KoSz83] proved the stronger result that with
$\frac{1}{2}n\log n+\frac{1}{2}n\log\log n+cn$ edges the probability that the graph is Hamiltonian
tends to $e^{-e^{-2c}}$ as $n\to \infty$.

This was formalized in Lean by Codex and GPT-5.6 Sol.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos746.lean#L34"]
theorem erdos_746 : answer(True) ↔ ∀ ε : ℝ, 0 < ε → ∀ m : ℕ → ℕ,
    (∀ᶠ n : ℕ in atTop, (1 / 2 + ε) * n * log n ≤ m n) → (∀ᶠ n : ℕ in atTop, m n ≤ n.choose 2) →
      Tendsto (fun n ↦ probability n (m n) IsHamiltonian) atTop (𝓝 1) := by
  sorry

/--
Komlós and Szemerédi [KoSz83] proved that with $\frac{1}{2}n\log n+\frac{1}{2}n\log\log n+cn$
edges the probability that the graph is Hamiltonian tends to $e^{-e^{-2c}}$ as $n\to \infty$.
-/
@[category research solved, AMS 5]
theorem erdos_746.variants.komlos_szemeredi (c : ℝ) (m : ℕ → ℕ)
    (hm : (fun n : ℕ ↦ (m n : ℝ) - (1 / 2 * n * log n + 1 / 2 * n * log (log n) + c * n)) =o[atTop]
      fun n : ℕ ↦ (n : ℝ)) :
    Tendsto (fun n ↦ probability n (m n) IsHamiltonian) atTop (𝓝 (exp (-exp (-2 * c)))) := by
  sorry

end Erdos746
