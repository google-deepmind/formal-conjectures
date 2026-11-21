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
# Erdős Problem 917

*References:*
- [erdosproblems.com/917](https://www.erdosproblems.com/917)
- [Er69b] Erdős, P., *Problems and results in chromatic graph theory*. Proof Techniques in Graph
  Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
  [PDF](https://www.renyi.hu/~p_erdos/1969-13.pdf)
- [Er93] Erdős, P., *Some of my favorite solved and unsolved problems in graph theory*.
  Quaestiones Math. 16 (1993), 333-350.
- [Di52] Dirac, G. A., *A property of $4$-chromatic graphs and some remarks on critical graphs*.
  J. London Math. Soc. 27 (1952), 85-92.
- [To70] Toft, B., *On the maximal number of edges of critical $k$-chromatic graphs*. Studia Sci.
  Math. Hungar. 5 (1970), 461-470.
- [St87] Stiebitz, M., *Subgraphs of colour-critical graphs*. Combinatorica 7 (1987), 303-312.
- [LMY23] Luo, C., Ma, J. and Yang, T., *On the maximum number of edges in $k$-critical graphs*.
  Combin. Probab. Comput. 32 (2023), 900-911.
  [arXiv:2301.01656](https://arxiv.org/abs/2301.01656)

The question is due to Erdős [Er69b, p. 28]; see also [Er93, p. 341]. See also
[erdosproblems.com/944](https://www.erdosproblems.com/944) and
[erdosproblems.com/1032](https://www.erdosproblems.com/1032).
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos917

/-- A graph `G` is `k`-critical if it has chromatic number `k` and every proper subgraph has
chromatic number less than `k`. For a finite graph a proper subgraph misses a vertex or an edge, so
this holds iff `G.IsCritical k` (deleting any vertex lowers the chromatic number) and deleting any
edge lowers the chromatic number.

The definition of Dirac quoted in [Er69b] uses only the edge condition. That would allow isolated
vertices, and then $f_k(n)$ below would be a running maximum. We use the standard notion, which is
also the one in [LMY23]. -/
def IsKCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.IsCritical k ∧ ∀ e ∈ G.edgeSet, G.IsCriticalEdge e

/-- $f_k(n)$ is the largest number of edges of a `k`-critical graph on `n` vertices. A graph on `n`
vertices has at most $\binom{n}{2}$ edges, so the `sSup` is a maximum whenever such a graph exists.
If there is none (for example if $n < k$), the value is `0`. -/
noncomputable def f (k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), IsKCritical G k ∧ G.edgeSet.ncard = m}

/-- A `k`-critical graph on `n` vertices has at most `f k n` edges. -/
@[category API, AMS 5]
theorem edgeSet_ncard_le_f {k n : ℕ} {G : SimpleGraph (Fin n)} (hG : IsKCritical G k) :
    G.edgeSet.ncard ≤ f k n := by
  unfold f
  refine le_csSup ⟨Nat.card (Sym2 (Fin n)), ?_⟩ ⟨G, hG, rfl⟩
  rintro m ⟨H, -, rfl⟩
  exact Set.ncard_le_card _

/-- The conjectured value $\frac{1}{2}\left(1-\frac{1}{\lfloor k/3\rfloor}\right)n^2$ of $f_k(n)$
for $k \geq 6$. It is also used for $k = 3$ in `erdos_917.variants.erdos_three_dvd`, where it is
$0$. -/
noncomputable def conjecturedValue (k n : ℕ) : ℝ :=
  1 / 2 * (1 - 1 / ((k / 3 : ℕ) : ℝ)) * (n : ℝ) ^ 2

/-- For $k = 6$ the conjectured value is $n^2/4$. -/
@[category test, AMS 5]
theorem conjecturedValue_six (n : ℕ) : conjecturedValue 6 n = (n : ℝ) ^ 2 / 4 := by
  have h : ((6 / 3 : ℕ) : ℝ) = 2 := by norm_num
  rw [conjecturedValue, h]
  ring

/-- The constant $\delta_k$ of the constructions below: $\delta_k = 0$ if $k \equiv 0 \pmod 3$,
$\delta_k = 1/7$ if $k \equiv 1 \pmod 3$ and $\delta_k = 24/69$ if $k \equiv 2 \pmod 3$. -/
noncomputable def delta (k : ℕ) : ℝ :=
  if k % 3 = 0 then 0 else if k % 3 = 1 then 1 / 7 else 24 / 69

/--
Let $k\geq 4$ and $f_k(n)$ be the largest number of edges in a graph on $n$ vertices which has
chromatic number $k$ and is critical (i.e. deleting any edge reduces the chromatic number).

Is it true that
$$f_k(n) \gg_k n^2?$$

This is the first part. It was proved by Toft [To70]. We read $\gg_k$ as: for each $k$ there is
$c > 0$ with $f_k(n) \geq cn^2$ for all large $n$.
-/
@[category research solved, question, AMS 5]
theorem erdos_917.parts.i :
    ∀ k : ℕ, 4 ≤ k → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ 2 ≤ (f k n : ℝ) := by
  sorry

/--
Let $k\geq 4$ and $f_k(n)$ be the largest number of edges in a graph on $n$ vertices which has
chromatic number $k$ and is critical (i.e. deleting any edge reduces the chromatic number).

Is it true that
$$f_6(n)\sim n^2/4?$$

This is the second part.
-/
@[category research open, question, AMS 5]
theorem erdos_917.parts.ii :
    (fun n : ℕ ↦ (f 6 n : ℝ)) ~[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 2 / 4) := by
  sorry

/--
Let $k\geq 4$ and $f_k(n)$ be the largest number of edges in a graph on $n$ vertices which has
chromatic number $k$ and is critical (i.e. deleting any edge reduces the chromatic number).

More generally, is it true that, for $k\geq 6$,
$$f_k(n) \sim \frac{1}{2}\left(1-\frac{1}{\lfloor k/3\rfloor}\right)n^2?$$

This is the third part. It has a negative answer: the constructions in
`erdos_917.variants.lower_construction` disprove it for $k \not\equiv 0 \pmod 3$
(see `erdos_917.variants.not_asymptotic`).
-/
@[category research solved, question, AMS 5]
theorem erdos_917.parts.iii :
    ¬ ∀ k : ℕ, 6 ≤ k → (fun n : ℕ ↦ (f k n : ℝ)) ~[atTop] conjecturedValue k := by
  sorry

/--
Constructions of Stiebitz [St87] show that, for $k\geq 6$, there exist infinitely many values of
$n$ such that
$$f_k(n) \geq \frac{1}{2}\left(1-\frac{1}{\lfloor k/3\rfloor+\delta_k}\right)n^2$$
where $\delta_k=0$ if $k\equiv 0\pmod{3}$, $\delta_k=1/7$ if $k\equiv 1\pmod{3}$, and
$\delta_k = 24/69$ if $k\equiv 2\pmod{3}$.

[LMY23] state the same bound in the form $(\frac12-\frac{3}{2k-\delta_k'})n^2$ with
$\delta_k'=0,8/7,44/23$, and credit the constructions to Toft [To70].
-/
@[category research solved, AMS 5]
theorem erdos_917.variants.lower_construction (k : ℕ) (hk : 6 ≤ k) :
    ∃ᶠ n : ℕ in atTop,
      1 / 2 * (1 - 1 / (((k / 3 : ℕ) : ℝ) + delta k)) * (n : ℝ) ^ 2 ≤ (f k n : ℝ) := by
  sorry

/--
The constructions in `erdos_917.variants.lower_construction` disprove Erdős' conjectured asymptotic
$f_k(n) \sim \frac{1}{2}\left(1-\frac{1}{\lfloor k/3\rfloor}\right)n^2$ for $k\not\equiv 0\pmod{3}$,
$k \geq 6$.
-/
@[category research solved, AMS 5]
theorem erdos_917.variants.not_asymptotic (k : ℕ) (hk : 6 ≤ k) (h3 : ¬ 3 ∣ k) :
    ¬ (fun n : ℕ ↦ (f k n : ℝ)) ~[atTop] conjecturedValue k := by
  sorry

/--
The remaining case of the third question: is it true that, for $k\geq 6$ with $3 \mid k$,
$$f_k(n) \sim \frac{1}{2}\left(1-\frac{1}{\lfloor k/3\rfloor}\right)n^2?$$
For $k = 6$ this is `erdos_917.parts.ii`.
-/
@[category research open, question, AMS 5]
theorem erdos_917.variants.three_dvd :
    ∀ k : ℕ, 6 ≤ k → 3 ∣ k → (fun n : ℕ ↦ (f k n : ℝ)) ~[atTop] conjecturedValue k := by
  sorry

/--
In fact Dirac [Di52] proved
$$f_6(4n+2) \geq 4n^2+8n+3,$$
as witnessed by taking two disjoint copies of $C_{2n+1}$ and adding all edges between them.

We take $n \geq 1$, so that $C_{2n+1}$ is a cycle.
-/
@[category research solved, AMS 5]
theorem erdos_917.variants.dirac (n : ℕ) (hn : 1 ≤ n) :
    4 * n ^ 2 + 8 * n + 3 ≤ f 6 (4 * n + 2) := by
  sorry

/--
Erdős [Er69b] observed that Dirac's construction generalises to show that, if $3\mid k$, there are
infinitely many values of $n$ (those of the shape $mk/3$ where $m$ is odd) such that
$$f_k(n) \geq \frac{1}{2}\left(1-\frac{1}{k/3}\right)n^2 + n.$$

We take $m \geq 3$, so that the cycle $C_m$ exists.
-/
@[category research solved, AMS 5]
theorem erdos_917.variants.erdos_three_dvd (k : ℕ) (hk : 3 ≤ k) (h3 : 3 ∣ k) (m : ℕ)
    (hm : Odd m) (hm3 : 3 ≤ m) :
    conjecturedValue k (m * (k / 3)) + ((m * (k / 3) : ℕ) : ℝ) ≤ (f k (m * (k / 3)) : ℝ) := by
  sorry

/--
Stiebitz also proved the general upper bound
$$f_k(n) < \mathrm{ex}(n;K_{k-1})\sim \frac{1}{2}\left(1-\frac{1}{k-2}\right)n^2$$
for large $n$.

Here $k \geq 4$, as in [LMY23].
-/
@[category research solved, AMS 5]
theorem erdos_917.variants.stiebitz_upper (k : ℕ) (hk : 4 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      f k n < SimpleGraph.extremalNumber n (SimpleGraph.completeGraph (Fin (k - 1))) := by
  sorry

/--
Luo, Ma, and Yang [LMY23] have improved this upper bound to
$$f_k(n) \leq \frac{1}{2}\left(1-\frac{1}{k-2}-\frac{1}{36(k-1)^2}+o(1)\right)n^2.$$

[LMY23, Theorem 1.1] proves the stronger bound
$f_k(n) \leq \mathrm{ex}(n;K_{k-1}) - \frac{n^2}{36(k-1)^2}$ for $k \geq 4$ and all large $n$, where
$\mathrm{ex}(n;K_{k-1})$ is the number of edges of the Turán graph $T_{k-2}(n)$. We state this form.
-/
@[category research solved, AMS 5]
theorem erdos_917.variants.luo_ma_yang (k : ℕ) (hk : 4 ≤ k) :
    ∀ᶠ n : ℕ in atTop, (f k n : ℝ) ≤
      (SimpleGraph.extremalNumber n (SimpleGraph.completeGraph (Fin (k - 1))) : ℝ) -
        (n : ℝ) ^ 2 / (36 * ((k : ℝ) - 1) ^ 2) := by
  sorry

end Erdos917
