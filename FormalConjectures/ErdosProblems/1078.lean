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
# Erdős Problem 1078

*References:*
- [erdosproblems.com/1078](https://www.erdosproblems.com/1078)
- [BES75b] Bollobás, B. and Erdős, P. and Szemerédi, E., *On complete subgraphs of $r$-chromatic
  graphs*. Discrete Math. (1975), 97-107.
- [Er75] Erdős, P., *Some recent progress on extremal problems in graph theory*. Congr. Numer.
  (1975), 3-14.
- [Ha01] Haxell, P. E., *A note on vertex list colouring*. Combin. Probab. Comput. (2001),
  345-347.
- [HaSz06] Haxell, Penny and Szabó, Tibor, *Odd independent transversals are odd*. Combin. Probab.
  Comput. (2006), 193-211.
-/

@[expose] public section

open Filter SimpleGraph

namespace Erdos1078

/--
A graph on `Fin r × Fin n` is `r`-partite with parts `{i} × Fin n` (each of size `n`) if
there are no edges inside a part.
-/
def IsPartite {r n : ℕ} (G : SimpleGraph (Fin r × Fin n)) : Prop :=
  ∀ ⦃x y⦄, G.Adj x y → x.1 ≠ y.1

open scoped Classical in
/--
Let $G$ be an $r$-partite graph with $n$ vertices in each part. If $G$ has minimum degree
$\geq (r-\frac{3}{2}-o(1))n$ then $G$ must contain a $K_r$.

A conjecture of Bollobás, Erdős, and Szemerédi [BES75b], who proved that $r-\frac{3}{2}$ would be
the best possible here. This is true, and was proved by Haxell [Ha01]. The sharp threshold of
$$(r-1)n-\left\lceil \frac{sn}{2s-1}\right\rceil$$
where $s=\lfloor r/2\rfloor$ was proved by Haxell and Szabó [HaSz06].

Here the $o(1)$ term tends to zero as $r\to\infty$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1078.lean#L905"]
theorem erdos_1078 : answer(True) ↔ ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
    ∀ r n : ℕ, 2 ≤ r → 0 < n → ∀ G : SimpleGraph (Fin r × Fin n), IsPartite G →
      (∀ x, (r - 3 / 2 - ε r) * n ≤ G.degree x) → ¬ G.CliqueFree r := by
  sorry

open scoped Classical in
/--
Haxell [Ha01] proved that an $r$-partite graph with $n$ vertices in each part and minimum degree
$\geq (r-\frac{3}{2})n$ contains a $K_r$.
-/
@[category research solved, AMS 5]
theorem erdos_1078.variants.haxell : ∀ r n : ℕ, 2 ≤ r → 0 < n →
    ∀ G : SimpleGraph (Fin r × Fin n), IsPartite G →
      (∀ x, (r - 3 / 2 : ℝ) * n ≤ G.degree x) → ¬ G.CliqueFree r := by
  sorry

open scoped Classical in
/--
Haxell and Szabó [HaSz06] proved that an $r$-partite graph with $n$ vertices in each part and
minimum degree $> (r-1)n-\lceil \frac{sn}{2s-1}\rceil$, where $s=\lfloor r/2\rfloor$, contains a
$K_r$.
-/
@[category research solved, AMS 5]
theorem erdos_1078.variants.haxell_szabo : ∀ r n : ℕ, 2 ≤ r → 0 < n →
    ∀ G : SimpleGraph (Fin r × Fin n), IsPartite G →
      (∀ x, (r - 1) * n - (r / 2 * n) ⌈/⌉ (2 * (r / 2) - 1) < G.degree x) → ¬ G.CliqueFree r := by
  sorry

open scoped Classical in
/--
The threshold of Haxell and Szabó [HaSz06] is sharp: for all $r\geq 2$ and $n\geq 1$ there is an
$r$-partite graph with $n$ vertices in each part, minimum degree
$(r-1)n-\lceil \frac{sn}{2s-1}\rceil$ (where $s=\lfloor r/2\rfloor$), and no $K_r$.
-/
@[category research solved, AMS 5]
theorem erdos_1078.variants.haxell_szabo_sharp : ∀ r n : ℕ, 2 ≤ r → 0 < n →
    ∃ G : SimpleGraph (Fin r × Fin n), IsPartite G ∧
      (∀ x, (r - 1) * n - (r / 2 * n) ⌈/⌉ (2 * (r / 2) - 1) ≤ G.degree x) ∧ G.CliqueFree r := by
  sorry

end Erdos1078
