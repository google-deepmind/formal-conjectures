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
import FormalConjectures.Wikipedia.RamseyNumbers

/-!
# Erdős Problem 165

Give an asymptotic formula for the off-diagonal Ramsey number $R(3,k)$.

It is known that
$$(c + o(1)) \frac{k^2}{\log k} \leq R(3,k) \leq (1 + o(1)) \frac{k^2}{\log k}$$
for some constant $c > 0$. The upper bound is due to Shearer [Sh83], improving an earlier
bound of Ajtai, Komlós and Szemerédi [AKS80]; the lower bound (with $c = 1/162$) is due to
Kim [Ki95], which settled the order of magnitude. The bound $c \geq 1/4$ was proved
independently by Bohman–Keevash [BoKe21] and Fiz Pontiveros–Griffiths–Morris [PGM20] via the
triangle-free process; the latter authors conjectured that $1/4$ is the correct constant.
This was disproved by Campos–Jenssen–Michelen–Sahasrabudhe [CJMS25], who proved
$c \geq 1/3$, and improved further by Hefty–Horn–King–Pfender [HHKP25] to $c \geq 1/2$.
Both of the latter papers conjecture that $c = 1/2$ is the correct asymptotic.

We express the asymptotics in terms of the normalised quotient
$k \mapsto R(3,k) \log k / k^2$. Note that the set defining `graphRamseyNumber` is nonempty
by Ramsey's theorem, so the `sInf` is a genuine minimum, and the junk values of the quotient
at $k = 0, 1$ (where $\log k \leq 0$) do not affect any of the limit statements below.

*References:*
- [erdosproblems.com/165](https://www.erdosproblems.com/165)
- [Sh83] J. Shearer, *A note on the independence number of triangle-free graphs*,
  Discrete Math. 46 (1983), 83–87.
- [AKS80] M. Ajtai, J. Komlós and E. Szemerédi, *A note on Ramsey numbers*,
  J. Combin. Theory Ser. A 29 (1980), 354–360.
- [Ki95] J. H. Kim, *The Ramsey number $R(3,t)$ has order of magnitude $t^2/\log t$*,
  Random Structures Algorithms 7 (1995), 173–207.
- [BoKe21] T. Bohman and P. Keevash, *Dynamic concentration of the triangle-free process*,
  Random Structures Algorithms 58 (2021), 221–293.
- [PGM20] G. Fiz Pontiveros, S. Griffiths and R. Morris, *The triangle-free process and the
  Ramsey number $R(3,k)$*, Mem. Amer. Math. Soc. 263 (2020), no. 1274, v+125.
- [CJMS25] M. Campos, M. Jenssen, M. Michelen and J. Sahasrabudhe, *A new lower bound for
  the Ramsey numbers $R(3,k)$*, arXiv:2505.13371 (2025).
- [HHKP25] Z. Hefty, P. Horn, D. King and F. Pfender, *Improving $R(3,k)$ in just two bites*,
  arXiv:2510.19718 (2025).
-/

namespace Erdos165

open Filter Real RamseyNumbers Topology

/--
Give an asymptotic formula for $R(3,k)$: does
$$\lim_{k \to \infty} \frac{R(3,k) \log k}{k^2}$$
exist as a positive constant $c$?

Here $R(3,k)$ is the off-diagonal Ramsey number: the least $N$ such that every simple graph
on $N$ vertices contains a triangle or an independent set of size $k$.
-/
@[category research open, AMS 5]
theorem erdos_165 : answer(sorry) ↔ ∃ c : ℝ, 0 < c ∧
    Tendsto (fun k : ℕ ↦ (R(3, k) : ℝ) * log k / k ^ 2) atTop (𝓝 c) := by
  sorry

/--
Shearer's upper bound [Sh83]: $R(3,k) \leq (1 + o(1)) k^2 / \log k$, i.e.
$$\limsup_{k \to \infty} \frac{R(3,k) \log k}{k^2} \leq 1.$$
This improved an earlier bound of Ajtai, Komlós and Szemerédi [AKS80].
-/
@[category research solved, AMS 5]
theorem erdos_165.variants.shearer_upper :
    limsup (fun k : ℕ ↦ (R(3, k) : ℝ) * log k / k ^ 2) atTop ≤ 1 := by
  sorry

/--
Kim's lower bound [Ki95]: $R(3,k) \geq (c + o(1)) k^2 / \log k$ for some constant $c > 0$
(Kim's original proof gave $c = 1/162$). Together with Shearer's upper bound this settled
the order of magnitude of $R(3,k)$.
-/
@[category research solved, AMS 5]
theorem erdos_165.variants.kim_lower :
    ∃ c : ℝ, 0 < c ∧
      c ≤ liminf (fun k : ℕ ↦ (R(3, k) : ℝ) * log k / k ^ 2) atTop := by
  sorry

/--
The triangle-free process lower bound, proved independently by Bohman–Keevash [BoKe21] and
Fiz Pontiveros–Griffiths–Morris [PGM20]:
$$\liminf_{k \to \infty} \frac{R(3,k) \log k}{k^2} \geq \frac{1}{4}.$$
-/
@[category research solved, AMS 5]
theorem erdos_165.variants.lower_bound_quarter :
    (1 : ℝ) / 4 ≤ liminf (fun k : ℕ ↦ (R(3, k) : ℝ) * log k / k ^ 2) atTop := by
  sorry

/--
The Campos–Jenssen–Michelen–Sahasrabudhe lower bound [CJMS25]:
$$\liminf_{k \to \infty} \frac{R(3,k) \log k}{k^2} \geq \frac{1}{3}.$$
-/
@[category research solved, AMS 5]
theorem erdos_165.variants.lower_bound_third :
    (1 : ℝ) / 3 ≤ liminf (fun k : ℕ ↦ (R(3, k) : ℝ) * log k / k ^ 2) atTop := by
  sorry

/--
The Hefty–Horn–King–Pfender lower bound [HHKP25], the current record:
$$\liminf_{k \to \infty} \frac{R(3,k) \log k}{k^2} \geq \frac{1}{2}.$$
-/
@[category research solved, AMS 5]
theorem erdos_165.variants.lower_bound_half :
    (1 : ℝ) / 2 ≤ liminf (fun k : ℕ ↦ (R(3, k) : ℝ) * log k / k ^ 2) atTop := by
  sorry

/--
Fiz Pontiveros–Griffiths–Morris [PGM20] conjectured that the triangle-free process lower
bound $1/4$ gives the correct constant, i.e. that $R(3,k) \log k / k^2 \to 1/4$. This was
disproved by the lower bound $\liminf \geq 1/3$ of [CJMS25] (and a fortiori by
$\liminf \geq 1/2$ of [HHKP25]).
-/
@[category research solved, AMS 5]
theorem erdos_165.variants.limit_not_quarter :
    ¬ Tendsto (fun k : ℕ ↦ (R(3, k) : ℝ) * log k / k ^ 2) atTop (𝓝 (1 / 4)) := by
  sorry

/--
Is $c = 1/2$ the correct asymptotic, i.e. does
$$\lim_{k \to \infty} \frac{R(3,k) \log k}{k^2} = \frac{1}{2}?$$
This is conjectured in both [CJMS25] and [HHKP25].
-/
@[category research open, AMS 5]
theorem erdos_165.variants.limit_eq_half : answer(sorry) ↔
    Tendsto (fun k : ℕ ↦ (R(3, k) : ℝ) * log k / k ^ 2) atTop (𝓝 (1 / 2)) := by
  sorry

/--
Degenerate case as a sanity check: $R(3,0) = 0$, since no graph has a $0$-independent set
to avoid (`CliqueFree 0` is false), so every $N$ works and the infimum is $0$.
-/
@[category test, AMS 5]
theorem graphRamseyNumber_three_zero : R(3, 0) = 0 :=
  Nat.sInf_eq_zero.mpr <| Or.inl fun _ h ↦ SimpleGraph.not_cliqueFree_zero h.2

/--
Sanity check: $R(3,1) \leq 1$, since any graph on one vertex contains an independent set of
size one.
-/
@[category test, AMS 5]
theorem graphRamseyNumber_three_one_le : R(3, 1) ≤ 1 :=
  Nat.sInf_le fun _ h ↦ (SimpleGraph.cliqueFree_one.mp h.2).elim ⟨0, Nat.zero_lt_one⟩

end Erdos165
