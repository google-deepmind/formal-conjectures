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
# Erdős Problem 565

*References:*
- [erdosproblems.com/565](https://www.erdosproblems.com/565)
- [Er75d] Erdős, Paul, Problems and results on finite and infinite graphs. Recent advances in graph
  theory (Proc. Second Czechoslovak Sympos., Prague, 1974) (1975), 183-192.
- [De75] Deuber, W., Generalizations of Ramsey's theorem. Infinite and finite sets (Colloq.,
  Keszthely, 1973; dedicated to P. Erdős on his 60th birthday), Vols. I, II, III (1975), 323-332.
- [EHP75] Erdős, P. and Hajnal, A. and Pósa, L., Strong embeddings of graphs into colored graphs.
  Infinite and finite sets (Colloq., Keszthely, 1973; dedicated to P. Erdős on his 60th birthday),
  Vols. I, II, III (1975), 585-595.
- [Ro73] Rödl, V., The dimension of a graph and generalized Ramsey theorems. thesis (1973).
- [KPR98] Kohayakawa, Y. and Prömel, H. J. and Rödl, V., Induced Ramsey numbers. Combinatorica
  (1998), 373-404.
- [FoSu08] Fox, Jacob and Sudakov, Benny, Induced Ramsey-type theorems. Adv. Math. (2008),
  1771-1800.
- [CFS12] Conlon, David and Fox, Jacob and Sudakov, Benny, On two problems in graph Ramsey theory.
  Combinatorica (2012), 513-535.
- [ACDFM25] L. Aragao, M. Campos, G. Dahia, R. Filipe, and J. P. Marciano, An exponential upper
  bound for induced Ramsey numbers. arXiv:2509.22629 (2025).
-/

@[expose] public section

open SimpleGraph

namespace Erdos565

/-- `H` is an *induced Ramsey host* for `G` if every $2$-colouring of the edges of `H` contains an
induced monochromatic copy of `G`, i.e. a graph embedding `G ↪g H` (which preserves and reflects
adjacency) all of whose edges receive the same colour. -/
def IsInducedRamseyHost {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∀ c : H.EdgeLabeling (Fin 2), ∃ (i : Fin 2) (f : G ↪g H), ∀ e : G.edgeSet, c (f.mapEdgeSet e) = i

/-- The induced Ramsey number `R*(G)`: the minimal `m` such that there is a graph `H` on `m`
vertices such that any $2$-colouring of the edges of `H` contains an induced monochromatic copy
of `G`. -/
noncomputable def inducedRamseyNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {m | ∃ H : SimpleGraph (Fin m), IsInducedRamseyHost G H}

/--
Let $R^*(G)$ be the induced Ramsey number: the minimal $m$ such that there is a graph $H$ on $m$
vertices such that any $2$-colouring of the edges of $H$ contains an induced monochromatic copy of
$G$.

Is it true that
$$R^*(G) \leq 2^{O(n)}$$
for any graph $G$ on $n$ vertices?

This is true, and an upper bound of $R^*(G) < 2^{O(n)}$ was proved by Aragão, Campos, Dahia,
Filipe, and Marciano [ACDFM25].

This was formalized in Lean by Codex and GPT-5.6 Sol.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos565.lean#L52"]
theorem erdos_565 : answer(True) ↔
    ∃ C : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), inducedRamseyNumber G ≤ 2 ^ (C * n) := by
  sorry

/--
Even the existence of $R^*(G)$ is not obvious, but was proved independently by Deuber [De75],
Erdős, Hajnal, and Pósa [EHP75], and Rödl [Ro73].

This was formalized in Lean by Codex and GPT-5.6 Sol.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos565.lean#L42"]
theorem erdos_565.variants.exists (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ (m : ℕ) (H : SimpleGraph (Fin m)), IsInducedRamseyHost G H := by
  sorry

/--
Kohayakawa, Prömel, and Rödl [KPR98] have proved that $R^*(G) < 2^{O(n(\log n)^2)}$. An
alternative (and more explicit) proof was given by Fox and Sudakov [FoSu08]. Conlon, Fox, and
Sudakov [CFS12] have improved this to
$$R^*(G) < 2^{O(n\log n)}.$$
-/
@[category research solved, AMS 5]
theorem erdos_565.variants.conlon_fox_sudakov : ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (inducedRamseyNumber G : ℝ) ≤ 2 ^ (C * n * Real.log n) := by
  sorry

end Erdos565
