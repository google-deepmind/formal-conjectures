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
# Erdős Problem 37

*References:*
- [erdosproblems.com/37](https://www.erdosproblems.com/37)
- [Er56] Erdős, P., *Problems and results in additive number theory*. Colloque sur la Théorie des
  Nombres, Bruxelles, 1955 (1956), 127-137.
- [Er61] Erdős, Paul, *Some unsolved problems*. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221-254.
- [Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971)
  (1973), 117-138.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Ru87] Ruzsa, I., *Essential Components*. Proc. London Math. Soc. (1987), 38-56.
-/

@[expose] public section

open Filter
open scoped Pointwise

namespace Erdos37

open scoped Classical in
/-- A set $A\subset \mathbb{N}$ is an essential component if $d_s(A+B)>d_s(B)$ for every
$B\subset \mathbb{N}$ with $0<d_s(B)<1$, where $d_s$ is the Schnirelmann density. -/
def IsEssentialComponent (A : Set ℕ) : Prop :=
  ∀ B : Set ℕ, 0 < schnirelmannDensity B → schnirelmannDensity B < 1 →
    schnirelmannDensity B < schnirelmannDensity (A + B)

/-- A set $A = \{a_1 < a_2 < \cdots\} \subset \mathbb{N}$ is lacunary if it is infinite and
$a_{k+1} \geq q a_k$ for all $k$, for some fixed $q > 1$. -/
def IsLacunarySet (A : Set ℕ) : Prop :=
  A.Infinite ∧ ∃ q : ℝ, 1 < q ∧ ∀ x ∈ A, ∀ y ∈ A, x < y → q * x ≤ y

/--
We say that $A\subset \mathbb{N}$ is an essential component if $d_s(A+B)>d_s(B)$ for every
$B\subset \mathbb{N}$ with $0<d_s(B)<1$ where $d_s$ is the Schnirelmann density.

Can a lacunary set $A\subset\mathbb{N}$ be an essential component?

The answer is no by Ruzsa [Ru87], who proved that if $A$ is an essential component then there
exists some constant $c>0$ such that $\lvert A\cap \{1,\ldots,N\}\rvert \geq (\log N)^{1+c}$
for all large $N$. Furthermore, Ruzsa proves that this is best possible, in that for any $c>0$
there exists an essential component $A$ for which $\lvert A\cap \{1,\ldots,N\}\rvert \leq
(\log N)^{1+c}$ for all large $N$.

See also [1146](https://www.erdosproblems.com/1146) for whether $\{2^m3^n\}$ is an essential
component.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos37.lean#L6737"]
theorem erdos_37 : answer(False) ↔ ∃ A : Set ℕ, IsLacunarySet A ∧ IsEssentialComponent A := by
  sorry

/--
Ruzsa [Ru87] proved that if $A$ is an essential component then there exists some constant $c>0$
such that $\lvert A\cap \{1,\ldots,N\}\rvert \geq (\log N)^{1+c}$ for all large $N$.
-/
@[category research solved, AMS 11]
theorem erdos_37.variants.ruzsa_lower (A : Set ℕ) (hA : IsEssentialComponent A) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      Real.log N ^ (1 + c) ≤ ((A ∩ Set.Icc 1 N).ncard : ℝ) := by
  sorry

/--
Ruzsa [Ru87] proved that for any $c>0$ there exists an essential component $A$ for which
$\lvert A\cap \{1,\ldots,N\}\rvert \leq (\log N)^{1+c}$ for all large $N$.
-/
@[category research solved, AMS 11]
theorem erdos_37.variants.ruzsa_sharp (c : ℝ) (hc : 0 < c) :
    ∃ A : Set ℕ, IsEssentialComponent A ∧ ∀ᶠ N : ℕ in atTop,
      ((A ∩ Set.Icc 1 N).ncard : ℝ) ≤ Real.log N ^ (1 + c) := by
  sorry

end Erdos37
