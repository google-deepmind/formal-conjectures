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
# Erdős Problem 179

*References:*
- [erdosproblems.com/179](https://www.erdosproblems.com/179)
- [Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971)
  (1973), 117-138.
- [Er75b] Erdős, Paul, *Problems and results in combinatorial number theory*. Journées
  Arithmétiques de Bordeaux (Conf., Univ. Bordeaux, Bordeaux, 1974) (1975), 295-310.
- [ErGr79] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics*. Enseign. Math. (1979), 325-344.
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [FoPo20] Fox, J. and Pohoata, C., *Sets without $k$-term progressions can have many shorter
  progressions*. arXiv:1908.09905 (2020).
- [LSS24] Leng, J., Sah, A. and Sawhney, M., *Improved bounds for Szemerédi's theorem*.
  arXiv:2402.17995 (2024).
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos179

/--
The number of nontrivial `k`-term arithmetic progressions in a finite set `A`, each progression
`a, a + d, …, a + (k - 1) d` (with `d > 0`) counted once via its first two terms.
-/
noncomputable def apCount (k : ℕ) (A : Finset ℕ) : ℕ :=
  ((A ×ˢ A).filter fun p : ℕ × ℕ ↦
    p.1 < p.2 ∧ ∀ i < k, p.1 + i * (p.2 - p.1) ∈ A).card

/-- `A` contains a nontrivial `ℓ`-term arithmetic progression. -/
def HasAP (ℓ : ℕ) (A : Finset ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < ℓ, a + i * d ∈ A

/--
`F k N ℓ` is minimal such that every set `A ⊆ ℕ` of size `N` which contains at least `F k N ℓ`
many `k`-term arithmetic progressions must contain an `ℓ`-term arithmetic progression.
-/
noncomputable def F (k N ℓ : ℕ) : ℕ :=
  sInf {m | ∀ A : Finset ℕ, A.card = N → m ≤ apCount k A → HasAP ℓ A}

/--
Let $1\leq k<\ell$ be integers and define $F_k(N,\ell)$ to be minimal such that every set
$A\subset \mathbb{N}$ of size $N$ which contains at least $F_k(N,\ell)$ many $k$-term arithmetic
progressions must contain an $\ell$-term arithmetic progression. Find good upper bounds for
$F_k(N,\ell)$. Is it true that
$$F_3(N,4)=o(N^2)?$$

Erdős remarks the upper bound $o(N^2)$ is certainly false for $\ell >\epsilon \log N$. The answer
is yes: Fox and Pohoata [FoPo20] have shown that, for all fixed $1\leq k<\ell$,
$F_k(N,\ell)=N^{2-o(1)}$ and in fact $F_{k}(N,\ell) \leq \frac{N^2}{(\log\log N)^{C_\ell}}$ where
$C_\ell>0$ is some constant.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos179.lean#L1373"]
theorem erdos_179.parts.i : answer(True) ↔
    (fun N : ℕ ↦ (F 3 N 4 : ℝ)) =o[atTop] fun N ↦ (N : ℝ) ^ 2 := by
  sorry

/--
Is it true that for every $\ell>3$
$$\lim_{N\to \infty}\frac{\log F_3(N,\ell)}{\log N}=2?$$

Yes, by the result of Fox and Pohoata [FoPo20].
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos179.lean#L1373"]
theorem erdos_179.parts.ii : answer(True) ↔ ∀ ℓ : ℕ, 3 < ℓ →
    Tendsto (fun N : ℕ ↦ Real.log (F 3 N ℓ) / Real.log N) atTop (nhds 2) := by
  sorry

/--
Fox and Pohoata [FoPo20] proved that, for all fixed $1\leq k<\ell$,
$F_{k}(N,\ell) \leq \frac{N^2}{(\log\log N)^{C_\ell}}$ where $C_\ell>0$ is some constant.
-/
@[category research solved, AMS 5 11]
theorem erdos_179.variants.fox_pohoata : ∀ k ℓ : ℕ, 1 ≤ k → k < ℓ →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      (F k N ℓ : ℝ) ≤ (N : ℝ) ^ 2 / Real.log (Real.log N) ^ C := by
  sorry

end Erdos179
