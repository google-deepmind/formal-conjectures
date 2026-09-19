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
# Erdős Problem 1179

*References:*
- [erdosproblems.com/1179](https://www.erdosproblems.com/1179)
- [Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971)
  (1973), 117-138.
- [ErRe65] Erdős, P. and Rényi, A., *Probabilistic methods in group theory*. J. Analyse Math.
  (1965), 127-138.
- [ErHa76] Erdős, P. and Hall, R. R., *Probabilistic methods in group theory. II*. Houston J.
  Math. (1976), 173-180.
-/

@[expose] public section

open Filter Finset

namespace Erdos1179

variable {G : Type*} [AddCommGroup G] [Fintype G]

open scoped Classical in
/-- $F_A(g) = \#\{ S\subseteq A : g = \sum_{x\in S}x\}$. -/
noncomputable def repCount (A : Finset G) (g : G) : ℕ :=
  (A.powerset.filter fun S ↦ ∑ x ∈ S, x = g).card

/-- `A` is `ε`-balanced: $\lvert F_A(g)-2^{|A|}/N\rvert \leq \epsilon 2^{|A|}/N$ for all `g`. -/
def IsBalanced (ε : ℝ) (A : Finset G) : Prop :=
  ∀ g : G, |(repCount A g : ℝ) - 2 ^ A.card / Fintype.card G| ≤
    ε * (2 ^ A.card / Fintype.card G)

open scoped Classical in
/-- The probability that a uniformly random `k`-element subset of `G` is `ε`-balanced. -/
noncomputable def successProbability (G : Type*) [AddCommGroup G] [Fintype G] (ε : ℝ) (k : ℕ) :
    ℝ :=
  (((univ : Finset G).powersetCard k).filter (IsBalanced ε)).card /
    ((univ : Finset G).powersetCard k).card

/--
Let $0<\epsilon<1$ and let $g_\epsilon(N)$ be the minimal $k$ such that if $G$ is an abelian
group of size $N$ and $A\subseteq G$ is a uniformly random subset of size $k$, and
$$F_A(g) = \#\left\{ S\subseteq A : g = \sum_{x\in S}x\right\},$$
then, with probability $\to 1$ as $N\to \infty$,
$$\left\lvert F_A(g)-\frac{2^k}{N}\right\rvert \leq \epsilon \frac{2^k}{N}$$
for all $g\in G$.

Estimate $g_\epsilon(N)$ - in particular, is it true that for all $\epsilon>0$
$$g_\epsilon(N)=(1+o_\epsilon(1))\log_2N?$$

It is trivial that $g_\epsilon(N)\geq \log_2N$ for all $0<\epsilon<1$. Erdős and Rényi [ErRe65]
proved that for all $0<\epsilon<1$, $g_\epsilon(N) \leq (2+o(1))\log_2N+O_\epsilon(1)$. Erdős and
Hall [ErHa76] proved that, for all $0<\epsilon<1$,
$$g_\epsilon(N)\leq \left(1+O_\epsilon\left(\frac{\log\log\log N}{\log\log N}\right)\right)
\log_2N.$$

The upper bound $g_\epsilon(N)\leq (1+o(1))\log_2 N$ is formalised as: there is a choice of sizes
$k(N) = (1+o(1))\log_2 N$ such that, along any sequence of abelian groups with $|G|\to\infty$,
the probability that a random $k(|G|)$-subset is $\epsilon$-balanced tends to $1$. The matching
lower bound is `erdos_1179.variants.lower_bound`.

See also [543](https://www.erdosproblems.com/543).
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1179.lean#L3564"]
theorem erdos_1179 : answer(True) ↔ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ k : ℕ → ℕ,
    Tendsto (fun N : ℕ ↦ (k N : ℝ) / Real.logb 2 N) atTop (nhds 1) ∧
      ∀ (G : ℕ → Type) [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)],
        Tendsto (fun i ↦ Fintype.card (G i)) atTop atTop →
          Tendsto (fun i ↦ successProbability (G i) ε (k (Fintype.card (G i)))) atTop
            (nhds 1) := by
  sorry

/-- It is trivial that $g_\epsilon(N)\geq \log_2N$: an $\epsilon$-balanced set $A$ with
$\epsilon < 1$ must satisfy $|G| \leq 2^{|A|}$, since every $g$ has a representation. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1179.lean#L3564"]
theorem erdos_1179.variants.lower_bound : ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∀ A : Finset G, IsBalanced ε A → Fintype.card G ≤ 2 ^ A.card := by
  sorry

end Erdos1179
