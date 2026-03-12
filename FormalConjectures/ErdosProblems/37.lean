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

See also Problem 1146 (whether $\{2^m \cdot 3^n\}$ is an essential component).

[Er56] Erdős, P., _Problems and results in additive number theory_. Colloque sur la Théorie
des Nombres, Bruxelles, 1955 (1956), 127-137.

[Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl.
**6** (1961), 221–254.

[Er73] Erdős, P., _Problems and results on combinatorial number theory_. In: A Survey of
Combinatorial Theory (1973), 117–138.

[ErGr80] Erdős, P. and Graham, R.L., _Old and new problems and results in combinatorial
number theory_. Monographies de L'Enseignement Mathématique **28** (1980).

[Ru87] Ruzsa, I.Z., _Essential components_. Proc. London Math. Soc. (3) **54** (1987), 38–56.
-/

open Classical Finset Pointwise

namespace Erdos37

/--
A set $A \subseteq \mathbb{N}$ is an *essential component* if $d_s(A + B) > d_s(B)$ for every
$B \subseteq \mathbb{N}$ with $0 < d_s(B) < 1$, where $d_s$ is the Schnirelmann density.
-/
def IsEssentialComponent (A : Set ℕ) : Prop :=
  ∀ (B : Set ℕ), 0 < schnirelmannDensity B → schnirelmannDensity B < 1 →
    schnirelmannDensity (A + B) > schnirelmannDensity B

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

/--
Ruzsa's density lower bound for essential components [Ru87]:
if $A$ is an essential component, then there exists $c > 0$ such that
$|A \cap \{1,\ldots,N\}| \geq (\log N)^{1+c}$ for all sufficiently large $N$.
-/
@[category research solved, AMS 11]
theorem erdos_37_essential_component_lower_bound :
    ∀ (A : Set ℕ), IsEssentialComponent A →
      ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in Filter.atTop,
        ((Icc 1 N).filter (· ∈ A)).card ≥ (Real.log N) ^ (1 + c) := by
  sorry

/--
Optimality of the density lower bound [Ru87]:
for any $c > 0$, there exists an essential component $A$ with
$|A \cap \{1,\ldots,N\}| \leq (\log N)^{1+c}$ for all sufficiently large $N$.
-/
@[category research solved, AMS 11]
theorem erdos_37_essential_component_upper_bound :
    ∀ c : ℝ, c > 0 →
      ∃ (A : Set ℕ), IsEssentialComponent A ∧
        ∀ᶠ N in Filter.atTop,
          ((Icc 1 N).filter (· ∈ A)).card ≤ (Real.log N) ^ (1 + c) := by
  sorry

end Erdos37
