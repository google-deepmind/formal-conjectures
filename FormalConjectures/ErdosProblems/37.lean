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
# Erdős Problem 37

*Reference:* [erdosproblems.com/37](https://www.erdosproblems.com/37)

A lacunary set cannot be an essential component (a set that strictly increases the
Schnirelmann density of every set it is added to). Proved by Ruzsa [Ru87].

[Ru87] Ruzsa, I.Z., _Essential components_. Proc. London Math. Soc. (3) **54** (1987), 38–56.
-/

open Classical

namespace Erdos37

/--
The Schnirelmann density of a set $A \subseteq \mathbb{N}$, defined as
$$d_s(A) = \inf_{n \geq 1} \frac{|A \cap \{1,\ldots,n\}|}{n}$$
-/
noncomputable def schnirelmannDensity (A : Set ℕ) : ℝ :=
  ⨅ n : ℕ+, (((Finset.Icc 1 (n : ℕ)).filter (· ∈ A)).card : ℝ) / ((n : ℕ) : ℝ)

/--
The sumset $A + B = \{a + b \mid a \in A, b \in B\}$ for sets of natural numbers.
-/
def sumset (A B : Set ℕ) : Set ℕ :=
  {n | ∃ a ∈ A, ∃ b ∈ B, n = a + b}

/--
A set $A \subseteq \mathbb{N}$ is an *essential component* if $d_s(A + B) > d_s(B)$ for every
$B \subseteq \mathbb{N}$ with $0 < d_s(B) < 1$, where $d_s$ is the Schnirelmann density.
-/
def IsEssentialComponent (A : Set ℕ) : Prop :=
  ∀ (B : Set ℕ), 0 < schnirelmannDensity B → schnirelmannDensity B < 1 →
    schnirelmannDensity (sumset A B) > schnirelmannDensity B

/--
A set $A \subseteq \mathbb{N}$ is *lacunary* if there exists $q > 1$ such that for any two
consecutive elements $a < b$ of $A$ (with no element of $A$ strictly between them),
we have $b \geq q \cdot a$.
-/
def IsLacunary (A : Set ℕ) : Prop :=
  ∃ (q : ℝ), q > 1 ∧ ∀ (a b : ℕ), a ∈ A → b ∈ A → a < b →
    (∀ c ∈ A, ¬(a < c ∧ c < b)) → (b : ℝ) ≥ q * (a : ℝ)

/--
Erdős Problem 37, proved by Ruzsa [Ru87].
A lacunary set cannot be an essential component.
Ruzsa proved that if $A$ is an essential component then there exists some constant
$c > 0$ such that $|A \cap \{1,\ldots,N\}| \geq (\log N)^{1+c}$ for all large $N$, which rules
out lacunary sets (which satisfy $|A \cap \{1,\ldots,N\}| = O(\log N)$).
-/
@[category research solved, AMS 11]
theorem erdos_37 :
    ∀ (A : Set ℕ), IsLacunary A → ¬IsEssentialComponent A := by
  sorry

end Erdos37
