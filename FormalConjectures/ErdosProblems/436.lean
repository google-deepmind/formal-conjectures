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
# Erdős Problem 436

*References:*
- [erdosproblems.com/436](https://www.erdosproblems.com/436)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
  number theory*. Monographies de L'Enseignement Mathematique (1980).
- [LeLe62] Lehmer, D. H. and Lehmer, Emma, *On runs of residues*.
  Proc. Amer. Math. Soc. (1962), 102-106.
- [Hi91] Hildebrand, Adolf, *On consecutive $k$th power residues. II*.
  Michigan Math. J. (1991), 241-253.
-/

@[expose] public section

namespace Erdos436

open Filter

/-- A nonzero $k$th power residue modulo $p$. -/
def IsPowerResidue (k p n : ℕ) : Prop :=
  (n : ZMod p) ≠ 0 ∧ ∃ x : ZMod p, x ^ k = (n : ZMod p)

/-- The least positive start of a run of $m$ consecutive nonzero $k$th power residues
modulo $p$, or $\infty$ if there is no such run. -/
noncomputable def r (k m p : ℕ) : ℕ∞ :=
  sInf ((fun a : ℕ ↦ (a : ℕ∞)) ''
    {a | 0 < a ∧ ∀ i < m, IsPowerResidue k p (a + i)})

/-- The limit superior of $r(k,m,p)$ as $p$ tends to infinity through the primes. -/
noncomputable def Lambda (k m : ℕ) : ℕ∞ :=
  limsup (fun p : ℕ ↦ r k m p) (atTop ⊓ principal {p | p.Prime})

/-- The integer $p$ is not a nonzero power residue modulo $p$. -/
@[category test, AMS 11]
theorem not_isPowerResidue_self (k p : ℕ) : ¬ IsPowerResidue k p p := by
  rintro ⟨h, -⟩
  exact h (ZMod.natCast_self p)

/-- Modulo one there is no nonempty run of nonzero power residues. -/
@[category test, AMS 11]
theorem r_modulus_one (k m : ℕ) (hm : 0 < m) : r k m 1 = ⊤ := by
  apply top_unique
  apply le_sInf
  rintro x ⟨a, ⟨_, hRun⟩, rfl⟩
  have h := (hRun 0 hm).1
  exact False.elim (h (Subsingleton.elim _ _))

/--
If $p$ is a prime and $k,m\geq 2$ then let $r(k,m,p)$ be the minimal $r$ such that
$r,r+1,\ldots,r+m-1$ are all $k$th power residues modulo $p$. Let
$$\Lambda(k,m)=\limsup_{p\to \infty} r(k,m,p).$$
Is it true that $\Lambda(k,2)$ is finite for all $k$?

Hildebrand [Hi91] resolved the first question, proving that $\Lambda(k,2)$ is finite for
all $k$: in other words, for any $k\geq 2$, if $p$ is sufficiently large then there exists
a pair of consecutive $k$th power residues modulo $p$ in $[1,O_k(1)]$.
-/
@[category research solved, AMS 11]
theorem erdos_436.parts.i : answer(True) ↔
    ∀ k : ℕ, 2 ≤ k → Lambda k 2 < ⊤ := by
  sorry

/--
Is $\Lambda(k,3)$ finite for all odd $k$?
Here $k\geq 2$, as in the definition of the problem.
-/
@[category research open, AMS 11]
theorem erdos_436.parts.ii : answer(sorry) ↔
    ∀ k : ℕ, 2 ≤ k → Odd k → Lambda k 3 < ⊤ := by
  sorry

/--
How large are they? Determine the growth rate of $\Lambda(k,2)$ and $\Lambda(k,3)$ as
functions of $k$.

Here growth is specified up to positive constant factors, with the second function
restricted to odd $k$. The comparison takes place in $\mathbb{N}\cup\{\infty\}$, so it
also records infinite values without assuming an answer to the finiteness question.
-/
@[category research open, AMS 11]
theorem erdos_436.parts.iii :
    let f : (ℕ → ℕ∞) × (ℕ → ℕ∞) := answer(sorry)
    ∃ C D : ℕ, 0 < C ∧ 0 < D ∧ ∀ᶠ k : ℕ in atTop,
      Lambda k 2 ≤ C * f.1 k ∧ f.1 k ≤ D * Lambda k 2 ∧
        (Odd k → Lambda k 3 ≤ C * f.2 k ∧ f.2 k ≤ D * Lambda k 3) := by
  sorry

end Erdos436
