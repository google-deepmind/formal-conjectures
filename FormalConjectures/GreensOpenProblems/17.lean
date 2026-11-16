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
# Ben Green's Open Problem 17

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.17)
- [Hą20] Hązła, J., *On arithmetic progressions in symmetric sets in finite field model*.
  Electron. J. Combin. 27 (2020), no. 3, Paper No. 3.61.
  [arXiv:1811.09947](https://arxiv.org/abs/1811.09947)
- [BKLM24] Bhangale, A., Khot, S., Liu, Y. P. and Minzer, D., *On approximability of satisfiable
  $k$-CSPs: VI*. [arXiv:2411.15133](https://arxiv.org/abs/2411.15133) (2024).
-/

@[expose] public section

open Filter Asymptotics

namespace Green17

/--
`IsRestrictedAP A x d` says that $x, x + d, x + 2d$ all lie in `A`, where the common difference
$d$ is a nonzero vector in $\{0, 1\}^n \subset \mathbb{F}_3^n$. Since $d \ne 0$, the three points
are distinct.
-/
def IsRestrictedAP {n : ℕ} (A : Finset (𝔽₃ n)) (x d : 𝔽₃ n) : Prop :=
  d ≠ 0 ∧ (∀ i, d i = 0 ∨ d i = 1) ∧ x ∈ A ∧ x + d ∈ A ∧ x + 2 • d ∈ A

/--
`HasRestrictedAP A` says that `A` contains a 3-term progression whose common difference is a
nonzero vector in $\{0, 1\}^n$.
-/
def HasRestrictedAP {n : ℕ} (A : Finset (𝔽₃ n)) : Prop :=
  ∃ x d, IsRestrictedAP A x d

/--
`numRestrictedAPs A` is the number of pairs $(x, d)$ with $x \in \mathbb{F}_3^n$ and
$d \in \{0, 1\}^n \setminus \{0\}$ such that $x, x + d, x + 2d \in A$. There are
$3^n (2^n - 1)$ such pairs in all, which is about $6^n$.
-/
noncomputable def numRestrictedAPs {n : ℕ} (A : Finset (𝔽₃ n)) : ℕ :=
  Nat.card {p : 𝔽₃ n × 𝔽₃ n // IsRestrictedAP A p.1 p.2}

/--
`maxFree n` is the largest size of a set $A \subseteq \mathbb{F}_3^n$ with no 3-term progression
whose common difference is a nonzero vector in $\{0, 1\}^n$. The set of possible sizes is
nonempty (it contains $0$) and bounded by $3^n$, so the supremum is the maximum.
-/
noncomputable def maxFree (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset (𝔽₃ n), A.card = k ∧ ¬ HasRestrictedAP A}

/--
`IsSymmetric A` says that `A` is invariant under the action of the symmetric group $S_n$ on
$\mathbb{F}_3^n$ by permutation of the coordinates. Equivalently, whether $x \in A$ depends only
on the numbers of coordinates of $x$ equal to $0$, $1$ and $2$; this is the definition of a
symmetric set in [Hą20].
-/
def IsSymmetric {n : ℕ} (A : Finset (𝔽₃ n)) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), ∀ x ∈ A, (fun i ↦ x (σ i)) ∈ A

/--
In $\mathbb{F}_3^0$ there is no nonzero difference, so no set contains a progression of the
required kind. This is why `green_17.parts.ii` is stated for large $n$ only.
-/
@[category test, AMS 5 11]
theorem not_hasRestrictedAP_zero (A : Finset (𝔽₃ 0)) : ¬ HasRestrictedAP A := by
  rintro ⟨_, d, hd, -⟩
  exact hd (Subsingleton.elim _ _)

def green_17.parts.i.answer : ℕ → ℝ := sorry

/--
Suppose that $A \subset \mathbb{F}_3^n$ is a set of density $\alpha$. Under what conditions on
$\alpha$ is $A$ guaranteed to contain a 3-term progression with nonzero common difference in
$\{0, 1\}^n$?

We read the question as asking for the order of magnitude of the threshold density
$\alpha(n) = r(n) / 3^n$, where $r(n)$ is `maxFree n`: every set of density greater than
$\alpha(n)$ contains such a progression, and some set of density $\alpha(n)$ does not. [Gr24]
notes that $\alpha(n) \to 0$ by the density Hales-Jewett theorem; for the best known bound see
`green_17.variants.bklm`.
-/
@[category research open, question value, AMS 5 11]
theorem green_17.parts.i :
    (fun n : ℕ ↦ (maxFree n : ℝ) / 3 ^ n) =Θ[atTop] green_17.parts.i.answer := by
  sorry

/--
Suppose that $A \subset \mathbb{F}_3^n$ is a set of density $\alpha$. For fixed $\alpha$, must
$A$ contain $\gg_\alpha 6^n$ 3-term progressions with nonzero common difference in
$\{0, 1\}^n$?

A progression is counted as a pair $(x, d)$, see `numRestrictedAPs`. We read $\gg_\alpha 6^n$ as
at least $c(\alpha) 6^n$ for all $n \ge n_0(\alpha)$. A bound for all $n$ is false: for $n = 1$
the set $\{0, 1\}$ has density $2/3$ and contains no such progression.
-/
@[category research open, question, AMS 5 11]
theorem green_17.parts.ii :
    ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ A : Finset (𝔽₃ n),
      α * 3 ^ n ≤ (A.card : ℝ) → c * 6 ^ n ≤ (numRestrictedAPs A : ℝ) := by
  sorry

/--
Is there a constant $c \in (0, 1)$ such that, for all large $n$, every set
$A \subseteq \mathbb{F}_3^n$ of density at least $(1 - c)^n$ contains a 3-term progression with
nonzero common difference in $\{0, 1\}^n$?

[Gr24] notes that a density $\alpha \to 0$ slowly enough forces such a progression, and that
this may even hold with $\alpha = (1-c)^n$ for some $c > 0$. We require $c < 1$, so that
$(1 - c)^n > 0$.
-/
@[category research open, question, AMS 5 11]
theorem green_17.variants.exponential :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ᶠ n : ℕ in atTop, ∀ A : Finset (𝔽₃ n),
      (1 - c) ^ n * 3 ^ n ≤ (A.card : ℝ) → HasRestrictedAP A := by
  sorry

/--
**Bhangale, Khot, Liu and Minzer.** There are constants $c, C > 0$ such that every set
$A \subseteq \mathbb{F}_3^n$ of density at least $C (\log \log \log n)^{-c}$ contains a 3-term
progression with nonzero common difference in $\{0, 1\}^n$.

This is [BKLM24, Theorem 3] for $\Sigma = \mathbb{F}_3$ and
$S = \{(x, x + a, x + 2a) : x \in \mathbb{F}_3, a \in \{0, 1\}\}$, as in [BKLM24, Section 1.2.1]:
three points of $A$, not all equal, with $(x_i, y_i, z_i) \in S$ for all $i$ form such a
progression. We state it for large $n$, where $\log \log \log n > 0$.
-/
@[category research solved, AMS 5 11]
theorem green_17.variants.bklm :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ A : Finset (𝔽₃ n),
      C / Real.log (Real.log (Real.log n)) ^ c * 3 ^ n ≤ (A.card : ℝ) → HasRestrictedAP A := by
  sorry

/--
**Hązła.** For every $\mu > 0$ there is $\delta > 0$ such that every symmetric set
$A \subseteq \mathbb{F}_3^n$ of density at least $\mu$ contains at least $\delta 6^n$
progressions $x, x + d, x + 2d$ with $d \in \{0, 1\}^n$ [Hą20, abstract and Theorem 2, case
$q = 3$].

[Hą20] counts all pairs $(x, d)$ with $d \in \{0, 1\}^n$, including the $|A|$ pairs with
$d = 0$; this is why `A.card` is added to `numRestrictedAPs A`. For large $n$ the $d = 0$ pairs
are negligible, so `green_17.parts.ii` holds for symmetric sets. [Hą20, abstract] states the
result for sets of density exactly $\mu$. The form with density at least $\mu$ follows from the
removal statement [Hą20, Theorem 2] with $\mu/2$ in place of $\mu$: it removes a single symmetric
set of density at most $\mu/2$ and leaves a set with no progressions, but the remaining set is
nonempty and contains the progressions with $d = 0$.
-/
@[category research solved, AMS 5 11]
theorem green_17.variants.symmetric :
    ∀ μ : ℝ, 0 < μ → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ A : Finset (𝔽₃ n), IsSymmetric A →
      μ * 3 ^ n ≤ (A.card : ℝ) → δ * 6 ^ n ≤ (numRestrictedAPs A + A.card : ℝ) := by
  sorry

end Green17
