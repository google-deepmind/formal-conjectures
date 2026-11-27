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
# Erdős Problem 811

*References:*
- [erdosproblems.com/811](https://www.erdosproblems.com/811)
- [ErTu93] P. Erdős and Zs. Tuza, *Rainbow subgraphs in edge-colorings of complete graphs*,
  Ann. Discrete Math. 55 (1993), 81–88.
- [AxCl24] M. Axenovich and F. C. Clemen, *Rainbow subgraphs in edge-colored complete graphs:
  answering two questions by Erdős and Tuza*, J. Graph Theory (2024),
  [arXiv:2209.13867](https://arxiv.org/abs/2209.13867).
- [ClWa23] F. C. Clemen and A. Z. Wagner, *Balanced edge-colorings avoiding rainbow cliques of
  size four*, Electron. J. Combin. 30 (2023), P3.17,
  [arXiv:2303.15476](https://arxiv.org/abs/2303.15476).
-/

@[expose] public section

open Filter SimpleGraph

namespace Erdos811

/-- An edge colouring of $K_n$ with $m$ colours is balanced if every vertex is incident to exactly
$(n - 1)/m$ edges of each colour. For $m \ge 2$ and $n \equiv 1 \pmod m$ this is
$\lfloor n/m \rfloor$, as on the problem page. -/
def IsBalanced {n m : ℕ} (C : TopEdgeLabeling (Fin n) (Fin m)) : Prop :=
  ∀ (i : Fin m) (v : Fin n), ((C.labelGraph i).neighborSet v).ncard = (n - 1) / m

/-- `H` has the rainbow property if, with $m = e(H)$, for all large $n \equiv 1 \pmod m$ every
balanced $m$-colouring of $K_n$ contains a rainbow copy of `H`. -/
def HasRainbowProperty {α : Type*} [Fintype α] (H : SimpleGraph α) : Prop :=
  ∀ᶠ n in atTop, n ≡ 1 [MOD H.edgeSet.ncard] →
    ∀ C : TopEdgeLabeling (Fin n) (Fin H.edgeSet.ncard), IsBalanced C →
      ∃ f : H.Copy ⊤, IsRainbow f.toHom C

/-- The set of graphs on `Fin k` with the rainbow property. -/
def erdos_811.answer (k : ℕ) : Set (SimpleGraph (Fin k)) := by sorry

/--
Let $n \equiv 1 \pmod m$. An edge colouring of $K_n$ with $m$ colours is balanced if every vertex
sees exactly $\lfloor n/m \rfloor$ edges of each colour. For which graphs $G$ is it true that,
with $m = e(G)$, for all large $n \equiv 1 \pmod m$, every balanced $m$-colouring of $K_n$ contains
a rainbow copy of $G$?
-/
@[category research open, question value, AMS 5]
theorem erdos_811 (k : ℕ) (H : SimpleGraph (Fin k)) :
    HasRainbowProperty H ↔ H ∈ erdos_811.answer k := by
  sorry

/--
Clemen and Wagner [ClWa23]: for every $k \ge 1$ there is a balanced $6$-colouring of $K_{13^k}$
with no rainbow $K_4$.
-/
@[category research solved, AMS 5]
theorem erdos_811.variants.clemen_wagner (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : TopEdgeLabeling (Fin (13 ^ k)) (Fin 6), IsBalanced C ∧
      ∀ f : (⊤ : SimpleGraph (Fin 4)).Copy ⊤, ¬ IsRainbow f.toHom C := by
  sorry

/-- Erdős suggested that every graph might have the rainbow property. This is false: by
[ClWa23], $K_4$ does not have it. -/
@[category research solved, AMS 5]
theorem erdos_811.variants.k4 : ¬ HasRainbowProperty (⊤ : SimpleGraph (Fin 4)) := by
  sorry

/--
Axenovich and Clemen [AxCl24, Theorem 3.3]: let $\ell \ge 3$ be odd and
$m = \lfloor \sqrt{\ell} + 7/2 \rfloor$. For every $k \ge 1$ there is a balanced $\ell$-colouring of
$K_{(\ell + 1)^k}$ with no rainbow $K_m$.
-/
@[category research solved, AMS 5]
theorem erdos_811.variants.axenovich_clemen (ℓ k : ℕ) (hℓ : 3 ≤ ℓ) (hodd : Odd ℓ) (hk : 1 ≤ k) :
    ∃ C : TopEdgeLabeling (Fin ((ℓ + 1) ^ k)) (Fin ℓ), IsBalanced C ∧
      ∀ f : (⊤ : SimpleGraph (Fin ⌊Real.sqrt ℓ + 7 / 2⌋₊)).Copy ⊤, ¬ IsRainbow f.toHom C := by
  sorry

/--
Axenovich and Clemen [AxCl24, Theorem 1.4]: if $q \ge 10$ and $q \equiv 2$ or $3 \pmod 4$, then
$K_q$ does not have the rainbow property.
-/
@[category research solved, AMS 5]
theorem erdos_811.variants.cliques (q : ℕ) (hq : 10 ≤ q) (hq4 : q % 4 = 2 ∨ q % 4 = 3) :
    ¬ HasRainbowProperty (⊤ : SimpleGraph (Fin q)) := by
  sorry

/-- Axenovich and Clemen [AxCl24] conjecture that no complete graph $K_q$ with $q \ge 4$ has the
rainbow property. -/
@[category research open, AMS 5]
theorem erdos_811.variants.cliques_conjecture (q : ℕ) (hq : 4 ≤ q) :
    ¬ HasRainbowProperty (⊤ : SimpleGraph (Fin q)) := by
  sorry

end Erdos811
