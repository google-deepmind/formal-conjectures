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
# Erdős Problem 202

*References:*
- [erdosproblems.com/202](https://www.erdosproblems.com/202)
- [BFV13] de la Bretèche, Régis and Ford, Kevin and Vandehey, Joseph, *On non-intersecting
  arithmetic progressions*. Acta Arith. (2013), 381--392.
- [Ch05] Chen, Yong-Gao, *On disjoint arithmetic progressions*. Acta Arith. (2005), 143--148.
- [Cr03b] Croot, III, Ernest S., *On non-intersecting arithmetic progressions*. Acta Arith.
  (2003), 233--238.
- [ErSz68] Erdős, P. and Szemerédi, E., *On a problem of P. Erdős and S. Stein*. Acta Arith.
  (1968), 85-90.
- [PaPh24] Park, Jinyoung and Pham, Huy Tuan, *A proof of the Kahn-Kalai conjecture*.
  J. Amer. Math. Soc. (2024), 235--243.
-/

namespace Erdos202

open Filter

/-- The integer residue class $a \pmod q$. -/
def residueClass (q : ℕ) (a : ℤ) : Set ℤ :=
  {n : ℤ | n ≡ a [ZMOD (q : ℤ)]}

/-- A choice of one residue representative for each modulus in a finite set. -/
abbrev ResidueAssignment (Q : Finset ℕ) : Type :=
  {q : ℕ // q ∈ Q} → ℤ

/-- The selected residue classes are pairwise disjoint. -/
def PairwiseDisjointResidues (Q : Finset ℕ) (a : ResidueAssignment Q) : Prop :=
  ∀ i j : {q : ℕ // q ∈ Q}, i ≠ j →
    Disjoint (residueClass i.1 (a i)) (residueClass j.1 (a j))

/-- A finite family of moduli up to $N$ admitting disjoint residue classes. -/
def Admissible (N : ℕ) (Q : Finset ℕ) : Prop :=
  (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) ∧
    ∃ a : ResidueAssignment Q, PairwiseDisjointResidues Q a

/-- The maximal size of a family of disjoint residue classes with moduli at most $N$. -/
noncomputable def f (N : ℕ) : ℕ :=
  sSup {r : ℕ | ∃ Q : Finset ℕ, Admissible N Q ∧ Q.card = r}

/-- The standard Erdős 202 scale $L_\alpha(N)=\exp(\alpha\sqrt{\log N\log\log N})$. -/
noncomputable def Lscale (α : ℝ) (N : ℕ) : ℝ :=
  Real.exp (α * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))))

/--
Let $n_1<\cdots < n_r\leq N$ with associated $a_i\pmod{n_i}$ such that the congruence classes are disjoint (that is, every integer is $\equiv a_i\pmod{n_i}$ for at most one $1\leq i\leq r$). How large can $r$ be in terms of $N$?

The sharp asymptotic is $f(N)=N\exp(-(1+o(1))\sqrt{\log N\log\log N})$.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos202.lean"]
theorem erdos_202 :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) ∧
      (f N : ℝ) ≤ (N : ℝ) * Lscale (-(1 - ε)) N := by
  sorry

end Erdos202
