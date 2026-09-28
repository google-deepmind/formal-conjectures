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
# Erdős Problem 511

*References:*
- [erdosproblems.com/511](https://www.erdosproblems.com/511)
- [EHP58] Erdős, P. and Herzog, F. and Piranian, G., _Metric properties of polynomials_.
  J. Analyse Math. (1958), 125-148.
- [Er61] Erdős, Paul, _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221-254.
- [Ha74] Hayman, W. K., _Research problems in function theory: new problems_. (1974), 155--180.
- [Po61] Pommerenke, Ch., _On metric properties of complex polynomials_. Michigan Math. J. (1961),
  97-115.
- [Hu25] L. Huang, _Many leminscates with large diameter_. arXiv:2509.11597 (2025).
- [Po28] G. Pólya, _Beitrag zue Verallgemeinerung des Verzerrungssatzes auf mehrfach
  zusammenhängende Gebiete_. S-B. Akad. Wiss. (1928), 228-232 and 280-282.
-/

@[expose] public section

open Polynomial Metric

namespace Erdos511

/-- The connected components of a set `s ⊆ ℂ`, as subsets of `ℂ`. -/
def components (s : Set ℂ) : Set (Set ℂ) := {C | ∃ x ∈ s, C = connectedComponentIn s x}

/--
Let $f(z)\in \mathbb{C}[z]$ be a monic polynomial of degree $n$. Is it true that, for every $c>1$,
the set
$$\{ z\in \mathbb{C} : \lvert f(z)\rvert< 1\}$$
has at most $O_c(1)$ many connected components of diameter $>c$ (where the implied constant is in
particular independent of $n$)?

The answer is no: Pommerenke [Po61] proved that, for any $0<d<4$ and $k\geq 1$ there exist monic
polynomials $f\in \mathbb{C}[x]$ such that $\{z: \lvert f(z)\rvert\leq 1\}$ has at least $k$
connected components of diameter $\geq d$. This was independently proved by Huang [Hu25].
-/
@[category research solved, AMS 30, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos511.lean#L924"]
theorem erdos_511 : answer(False) ↔
    ∀ c : ℝ, 1 < c → ∃ B : ℕ, ∀ f : ℂ[X], f.Monic →
      {C ∈ components {z : ℂ | ‖f.eval z‖ < 1} | c < diam C}.encard ≤ B := by
  sorry

/--
Pommerenke [Po61] proved that, for any $0<d<4$ and $k\geq 1$ there exist monic polynomials
$f\in \mathbb{C}[x]$ such that $\{z: \lvert f(z)\rvert\leq 1\}$ has at least $k$ connected
components of diameter $\geq d$. This was independently proved by Huang [Hu25].
-/
@[category research solved, AMS 30]
theorem erdos_511.variants.pommerenke (d : ℝ) (hd₀ : 0 < d) (hd₄ : d < 4) (k : ℕ) :
    ∃ f : ℂ[X], f.Monic ∧
      k ≤ {C ∈ components {z : ℂ | ‖f.eval z‖ ≤ 1} | d ≤ diam C}.encard := by
  sorry

/--
Pólya [Po28] showed that $4$ is the best possible here, in that no connected component of
$\{z: \lvert f(z)\rvert\leq 1\}$ can have diameter $>4$.
-/
@[category research solved, AMS 30]
theorem erdos_511.variants.polya (f : ℂ[X]) (hf : f.Monic)
    (C : Set ℂ) (hC : C ∈ components {z : ℂ | ‖f.eval z‖ ≤ 1}) : diam C ≤ 4 := by
  sorry

end Erdos511
