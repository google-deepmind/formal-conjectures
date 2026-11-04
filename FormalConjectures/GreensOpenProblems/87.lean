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
# Green's Open Problem 87

References:
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.87)
- [BW15] Britnell, John R., and Mark Wildon. "Computing derangement probabilities of the symmetric
  group acting on k-sets." arXiv preprint arXiv:1511.04106 (2015).
- [EFG16] Eberhard, Sean, Kevin Ford, and Ben Green. "Permutations fixing a k-set." International
  Mathematics Research Notices 2016.21 (2016): 6713-6731. arXiv:1507.04465.
- [GS26] Green, Ben, and Mehtaab Sawhney. "The proportion of permutations fixing a k-set."
  arXiv preprint arXiv:2604.28116 (2026).
- [Ve26] Veljjanoski, Daniel. "p(k) for permutations fixing a k-set: values and checks for
  k ≤ 121." https://github.com/veljjanoski/green87-fixing-k-set (2026).
-/

@[expose] public section

open Filter Asymptotics Topology

namespace Green87

/-- A permutation $\sigma$ of $[n]$ *fixes a set of size $k$* (Green: "preserves some set of
size $k$") if some $k$-element subset of $[n]$ is mapped to itself by $\sigma$. -/
def FixesSet {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) : Prop :=
  ∃ s : Finset (Fin n), s.card = k ∧ s.image σ = s

/-- `i n k` is the proportion of permutations of $[n]$ that fix a set of size $k$, denoted
$i(n, k)$ in [BW15] and [EFG16]. -/
noncomputable def i (n k : ℕ) : ℝ :=
  (Nat.card {σ : Equiv.Perm (Fin n) // FixesSet σ k} : ℝ) / (Nat.card (Equiv.Perm (Fin n)) : ℝ)

/-- For every $k$, $i(n, k)$ converges as $n \to \infty$ [BW15, Section 2]; the limit is
$p(k)$ in Green's notation. It is the probability that the random multiset with
$\mathrm{Pois}(1/j)$ parts of size $j$ ($1 \le j \le k$, independent) has a sub-multiset
of total size $k$. -/
@[category research solved, AMS 5 60]
theorem exists_tendsto (k : ℕ) : ∃ L : ℝ, Tendsto (fun n ↦ i n k) atTop (𝓝 L) := by
  sorry

/-- The Erdős–Ford–Tenenbaum constant $\delta = 1 - \frac{1 + \log \log 2}{\log 2} \approx 0.086$,
called $\alpha$ in [Gr24]. -/
noncomputable def δ : ℝ := 1 - (1 + Real.log (Real.log 2)) / Real.log 2

/-- Let $p(k)$ be the limit, as $n \to \infty$, of the probability that a random permutation of
$[n]$ preserves some set of size $k$. Is $p(k)$ a decreasing function of $k$?

This is a conjecture of Peter Cameron (2010), see [BW15]. The statement is taken in the strict
sense, as in [BW15]: they verified $p(k) > p(k + 1)$ for $k < 30$, and this has been extended to
$k < 121$ in [Ve26]. Note $p(0) = 1$, since the empty set is always fixed, and $p(1) = 1 - 1/e$. -/
@[category research open, question, AMS 5 60]
theorem green_87.decreasing (p : ℕ → ℝ) (hp : ∀ k, Tendsto (fun n ↦ i n k) atTop (𝓝 (p k))) :
    StrictAnti p := by
  sorry

/-- $p(k)$ is bounded above and below by constant multiples of $k^{-\delta} (\log k)^{-3/2}$
[EFG16, Theorem 1.1]. -/
@[category research solved, AMS 5 60]
theorem green_87.order (p : ℕ → ℝ) (hp : ∀ k, Tendsto (fun n ↦ i n k) atTop (𝓝 (p k))) :
    p =Θ[atTop] fun k : ℕ ↦ (k : ℝ) ^ (-δ) * (Real.log k) ^ (-(3 / 2 : ℝ)) := by
  sorry

/-- Is $p(k) = (C + o(1)) k^{-\delta} (\log k)^{-3/2}$ for some absolute constant $C$?

Green and Sawhney [GS26] proved $p(k) = (1 + o(1)) f(\{\log_2 k\}) k^{-\delta} (\log k)^{-3/2}$
for an explicit smooth, positive $f$ on $\mathbb{R} / \mathbb{Z}$ with
$\max f / \min f < 1 + 2 \cdot 10^{-7}$. The question is therefore equivalent to whether $f$ is
constant; they conjecture that it is not, so the expected answer is no, but this has not been
proved. -/
@[category research open, question, AMS 5 60]
theorem green_87.asymptotic (p : ℕ → ℝ)
    (hp : ∀ k, Tendsto (fun n ↦ i n k) atTop (𝓝 (p k))) :
    ∃ C : ℝ, 0 < C ∧ p ~[atTop] fun k : ℕ ↦ C * (k : ℝ) ^ (-δ) * (Real.log k) ^ (-(3 / 2 : ℝ)) := by
  sorry

end Green87
