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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 570

*Reference:* [erdosproblems.com/570](https://www.erdosproblems.com/570)

For any integer $k \geq 3$, is it true that for all sufficiently large $m$, every graph $H$ with
$m$ edges and no isolated vertices satisfies $R(C_k, H) \leq 2m + \lfloor(k-1)/2\rfloor$, where
$R$ denotes the two-colour Ramsey number and $C_k$ the cycle on $k$ vertices?

[EFRS93] Erdős, P., Faudree, R., Rousseau, C., and Schelp, R., _Multipartite graph—sparse
graph Ramsey numbers_ (1993).
-/

open SimpleGraph

namespace Erdos570

/-- A graph $G$ embeds into a graph $H$: there is an injective map from
vertices of $G$ to vertices of $H$ preserving adjacency. -/
def Embeds {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧ ∀ u v, G.Adj u v → H.Adj (f u) (f v)

/-- The Ramsey number $R(G, H)$: the minimum $N$ such that for any graph $F$
on $\operatorname{Fin} N$, either $G$ embeds in $F$ or $H$ embeds in the complement of $F$. -/
noncomputable def ramseyNum {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) : ℕ :=
  sInf {N : ℕ | ∀ (F : SimpleGraph (Fin N)),
    Embeds G F ∨ Embeds H Fᶜ}

/-- The cycle graph $C_m$ on $m$ vertices ($m \geq 3$). Vertex $i$ is adjacent to vertex
$i + 1 \pmod{m}$ and vertex $i - 1 \pmod{m}$. -/
def cycleGraph (m : ℕ) (_ : m ≥ 3) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ (j.val = (i.val + 1) % m ∨ i.val = (j.val + 1) % m)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := fun _ ⟨h, _⟩ => h rfl

/--
Erdős Problem 570 [EFRS93]:

Let $k \geq 3$. Is it true that, for sufficiently large $m$, for any graph $H$ with $m$ edges and
no isolated vertices, $R(C_k, H) \leq 2m + \lfloor(k - 1) / 2\rfloor$?

Here $C_k$ is the cycle on $k$ vertices and $R(G, H)$ is the two-colour
Ramsey number.
-/
@[category research solved, AMS 5]
theorem erdos_570 : answer(True) ↔ ∀ (k : ℕ) (hk : k ≥ 3),
    ∃ M₀ : ℕ, ∀ (n : ℕ) (H : SimpleGraph (Fin n)),
      (∀ v : Fin n, ∃ w, H.Adj v w) →
      H.edgeSet.ncard ≥ M₀ →
      ramseyNum (cycleGraph k hk) H ≤ 2 * H.edgeSet.ncard + (k - 1) / 2 := by
  sorry

end Erdos570
