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
# Erdős Problem 580

*References:*
- [erdosproblems.com/580](https://www.erdosproblems.com/580)
- [AKS95] Ajtai, Miklós, Komlós, János, and Szemerédi, Endre, *On a conjecture of Loebl*.
  Graph theory, combinatorics, and algorithms, Vol. 1, 2 (1995), 1135-1146.
- [Zh11] Zhao, Yi, *Proof of the $(n/2-n/2-n/2)$ conjecture for large $n$*.
  Electron. J. Combin. (2011), Paper 27, 61.
-/

@[expose] public section

namespace Erdos580

open Filter SimpleGraph

open scoped Classical in
/--
Let $G$ be a graph on $n$ vertices such that at least $n/2$ vertices have degree at least
$n/2$. Must $G$ contain every tree on at most $n/2$ vertices?
-/
@[category research open, AMS 5]
theorem erdos_580 : answer(sorry) ↔
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      n ≤ 2 * (Finset.univ.filter (fun v => n ≤ 2 * G.degree v)).card →
        ∀ m : ℕ, 2 * m ≤ n → ∀ T : SimpleGraph (Fin m), T.IsTree → T.IsContained G := by
  sorry

open scoped Classical in
/--
Ajtai, Komlós, and Szemerédi [AKS95] proved an asymptotic version, where at least
$(1+\epsilon)n/2$ vertices have degree at least $(1+\epsilon)n/2$ (and $n$ is sufficiently
large depending on $\epsilon$).
-/
@[category research solved, AMS 5]
theorem erdos_580.variants.ajtai_komlos_szemeredi :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (1 + ε) * (n : ℝ) / 2 ≤
        ((Finset.univ.filter (fun v =>
          (1 + ε) * (n : ℝ) / 2 ≤ (G.degree v : ℝ))).card : ℝ) →
        ∀ m : ℕ, 2 * m ≤ n → ∀ T : SimpleGraph (Fin m), T.IsTree → T.IsContained G := by
  sorry

open scoped Classical in
/--
Zhao [Zh11] has proved this conjecture holds for all sufficiently large $n$.
-/
@[category research solved, AMS 5]
theorem erdos_580.variants.zhao :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      n ≤ 2 * (Finset.univ.filter (fun v => n ≤ 2 * G.degree v)).card →
        ∀ m : ℕ, 2 * m ≤ n → ∀ T : SimpleGraph (Fin m), T.IsTree → T.IsContained G := by
  sorry

open scoped Classical in
/--
Komlós and Sós conjectured the generalisation that if at least $n/2$ vertices have
degree at least $k$ then $G$ contains any tree with $k$ vertices.

The host graph is nonempty to exclude the vacuous degree condition on an empty graph.
-/
@[category research open, AMS 5]
theorem erdos_580.variants.komlos_sos : answer(sorry) ↔
    ∀ n : ℕ, 0 < n → ∀ (k : ℕ) (G : SimpleGraph (Fin n)),
      n ≤ 2 * (Finset.univ.filter (fun v => k ≤ G.degree v)).card →
        ∀ T : SimpleGraph (Fin k), T.IsTree → T.IsContained G := by
  sorry

end Erdos580
