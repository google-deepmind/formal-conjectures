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
# Erdős Problem 569

Is it true that for every $k \geq 1$, there exists a constant $c_k$ such that for any graph $H$
with $m$ edges and no isolated vertices, $R(C_{2k+1}, H) \leq c_k \cdot m$?

*Reference:* [erdosproblems.com/569](https://www.erdosproblems.com/569)

[EFRS93] Erdős, P., Faudree, R., Rousseau, C., and Schelp, R.
-/

open SimpleGraph

namespace Erdos569

/-- A graph $G$ embeds into a graph $H$: there is an injective map from
vertices of $G$ to vertices of $H$ preserving adjacency. -/
def Embeds {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧ ∀ u v, G.Adj u v → H.Adj (f u) (f v)

/-- The Ramsey number $R(G, H)$: the minimum $N$ such that for any graph $F$
on $\operatorname{Fin} N$, either $G$ embeds in $F$ or $H$ embeds in the complement
of $F$. -/
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
Erdős Problem 569 [EFRS93]:

For every $k \geq 1$, there exists a constant $c_k$ such that for any graph $H$
with $m$ edges and no isolated vertices, $R(C_{2k+1}, H) \leq c_k \cdot m$.

Here $C_{2k+1}$ is the odd cycle on $2k+1$ vertices.
-/
@[category research open, AMS 5]
theorem erdos_569 (k : ℕ) (hk : k ≥ 1) :
    ∃ c : ℕ, ∀ (n : ℕ) (H : SimpleGraph (Fin n)),
      (∀ v : Fin n, ∃ w, H.Adj v w) →
      ramseyNum (cycleGraph (2 * k + 1) (by omega)) H ≤ c * H.edgeSet.ncard := by
  sorry

end Erdos569
