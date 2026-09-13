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

import FormalConjecturesUtil

/-!
# Erdős Problem 1012

*References:*
- [erdosproblems.com/1012](https://www.erdosproblems.com/1012)
- [Bo71b] Bondy, J. A., *Large cycles in graphs*. Discrete Math. (1971/72), 121--132.
- [Er62e] Erdős, P., *Remarks on a paper of Pósa*. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1962),
  227--229.
- [Or61] Ore, Oystein, *Arc coverings of graphs*. Ann. Mat. Pura Appl. (4) (1961), 315--321.
- [Wo72] Woodall, D. R., *Sufficient conditions for circuits in graphs*. Proc. London Math. Soc.
  (3) (1972), 739--755.
-/

open SimpleGraph

namespace Erdos1012

/-- Woodall/Ore edge threshold $\binom{n-k-1}{2}+\binom{k+2}{2}+1$. -/
def edgeThreshold (k n : ℕ) : ℕ :=
  (n - k - 1).choose 2 + (k + 2).choose 2 + 1

@[simp, category test, AMS 5]
lemma edgeThreshold_pos (k n : ℕ) : 1 ≤ edgeThreshold k n := by
  simp [edgeThreshold]

/--
`ForcesCycle k n` means that every graph on `n` vertices with at least
`edgeThreshold k n` edges contains a cycle of length $n-k$.
-/
def ForcesCycle (k n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    edgeThreshold k n ≤ G.edgeSet.ncard →
      n - k ∈ G.cycleLengths

/-- Specialising an all-lengths Woodall-style conclusion to `l = n - k` yields `ForcesCycle`. -/
@[category API, AMS 5]
lemma ForcesCycle.of_all_lengths {k n : ℕ}
    (h : ∀ G : SimpleGraph (Fin n),
      edgeThreshold k n ≤ G.edgeSet.ncard →
        ∀ l, 3 ≤ l → l ≤ n - k → l ∈ G.cycleLengths)
    (hnk : 3 ≤ n - k) : ForcesCycle k n :=
  fun G he ↦ h G he (n - k) hnk le_rfl

/-- A stronger edge count still forces an `(n-k)`-cycle once `ForcesCycle` holds. -/
@[category API, AMS 5]
lemma ForcesCycle.mono_ncard {k n : ℕ} (h : ForcesCycle k n)
    {G : SimpleGraph (Fin n)} {N : ℕ}
    (hN : edgeThreshold k n ≤ N) (he : N ≤ G.edgeSet.ncard) :
    n - k ∈ G.cycleLengths :=
  h G (le_trans hN he)

/--
$f(k)$ is the least positive $N$ such that every graph on $n\geq N$ vertices with at least
$\binom{n-k-1}{2}+\binom{k+2}{2}+1$ edges contains a cycle of length $n-k$.

The infimum is taken over positive $N$ so that $f(0)=1$ matches Ore. For $n=0$ the edge
threshold is already at least $1$, so the implication would hold vacuously.
-/
noncomputable def f (k : ℕ) : ℕ :=
  sInf {N : ℕ | 0 < N ∧ ∀ n ≥ N, ForcesCycle k n}

/-- If some positive `N` forces an `(n-k)`-cycle for every `n ≥ N`, then `f k ≤ N`. -/
@[category API, AMS 5]
lemma f_le {k N : ℕ} (hN : 0 < N) (h : ∀ n ≥ N, ForcesCycle k n) : f k ≤ N :=
  Nat.sInf_le ⟨hN, h⟩

/-- If some positive `N` witnesses the forcing property for all larger `n`, then `f k` is positive. -/
@[category API, AMS 5]
lemma zero_lt_f_of_bound {k N : ℕ} (hN : 0 < N) (h : ∀ n ≥ N, ForcesCycle k n) : 0 < f k :=
  (Nat.sInf_mem (s := {N : ℕ | 0 < N ∧ ∀ n ≥ N, ForcesCycle k n}) ⟨N, ⟨hN, h⟩⟩).1

/-- Positivity of `f k` means the defining set is nonempty, so `f k` itself is a forcing threshold. -/
@[category API, AMS 5]
lemma mem_forcesCycleSet_of_f_pos {k : ℕ} (hf : 0 < f k) :
    0 < f k ∧ ∀ n ≥ f k, ForcesCycle k n := by
  have hne : ({N : ℕ | 0 < N ∧ ∀ n ≥ N, ForcesCycle k n}).Nonempty := by
    by_contra hempty
    have : f k = 0 := by
      simp [f, Set.not_nonempty_iff_eq_empty.mp hempty]
    exact (hf.ne' this).elim
  exact Nat.sInf_mem hne

/-- Once `f k` is known positive, every `n ≥ f k` forces an `(n - k)`-cycle at the threshold. -/
@[category API, AMS 5]
lemma ForcesCycle_of_f_le {k n : ℕ} (hf : 0 < f k) (hn : f k ≤ n) : ForcesCycle k n :=
  (mem_forcesCycleSet_of_f_pos hf).2 n hn


/-- Woodall's all-lengths statement implies `f k ≤ 2 * k + 3`. -/
@[category API, AMS 5]
lemma f_le_two_mul_add_three_of_woodall
    (hW : ∀ (k n : ℕ), 2 * k + 3 ≤ n →
      ∀ G : SimpleGraph (Fin n),
        edgeThreshold k n ≤ G.edgeSet.ncard →
          ∀ l, 3 ≤ l → l ≤ n - k → l ∈ G.cycleLengths)
    (k : ℕ) : f k ≤ 2 * k + 3 := by
  refine f_le (by omega) fun n hn ↦
    ForcesCycle.of_all_lengths (hW k n hn) (by omega)

/--
Woodall [Wo72] proved that every graph on $n\geq 2k+3$ vertices with at least
$\binom{n-k-1}{2}+\binom{k+2}{2}+1$ edges contains a cycle on $l$ vertices for all
$3\leq l\leq n-k$.
-/
@[category research solved, AMS 5]
theorem erdos_1012.variants.woodall (k n : ℕ) (G : SimpleGraph (Fin n))
    (hn : 2 * k + 3 ≤ n)
    (he : edgeThreshold k n ≤ G.edgeSet.ncard) :
    ∀ l, 3 ≤ l → l ≤ n - k → l ∈ G.cycleLengths := by
  sorry

/--
Let $k\geq 0$. Let $f(k)$ be such that every graph on $n\geq f(k)$ vertices with at least
$\binom{n-k-1}{2}+\binom{k+2}{2}+1$ edges contains a cycle on $n-k$ vertices. Determine or
estimate $f(k)$.

Woodall [Wo72] proved that every graph on $n\geq 2k+3$ vertices with at least
$\binom{n-k-1}{2}+\binom{k+2}{2}+1$ edges contains a cycle on $l$ vertices for all
$3\leq l\leq n-k$. This settles this question completely.

The inequality is `f_le` at `N = 2k+3`, using Woodall specialised to `l = n-k`.
-/
@[category research solved, AMS 5]
theorem erdos_1012 (k : ℕ) : f k ≤ 2 * k + 3 :=
  f_le_two_mul_add_three_of_woodall
    (fun k n hn G he ↦ erdos_1012.variants.woodall k n G hn he) k

/--
Erdős [Er62e] proved that $f(k)$ exists for all $k\geq 0$; this is not immediately stated in
[Er62e], but Cambie has in the comments explained why the existence of $f(k)$ follows from the
result of [Er62e]. Existence also follows from Woodall via `zero_lt_f_of_bound`.
-/
@[category research solved, AMS 5]
theorem erdos_1012.variants.exists (k : ℕ) : 0 < f k :=
  zero_lt_f_of_bound (by omega : 0 < 2 * k + 3) fun n hn ↦
    ForcesCycle.of_all_lengths (erdos_1012.variants.woodall k n · hn) (by omega)

/--
Ore [Or61] proved that $f(0)=1$, in other words, every graph on $n\geq 1$ vertices with at least
$\binom{n-1}{2}+2$ edges contains a Hamiltonian cycle on $n$ vertices.
-/
@[category research solved, AMS 5]
theorem erdos_1012.variants.ore : f 0 = 1 := by
  sorry

/--
Bondy [Bo71b] proved that $f(1)=1$.
-/
@[category research solved, AMS 5]
theorem erdos_1012.variants.bondy : f 1 = 1 := by
  sorry

/-- Ore's edge count $\binom{n-1}{2}+2$ is the $k=0$ case of the general threshold. -/
@[category test, AMS 5]
theorem erdos_1012.variants.ore_threshold (n : ℕ) :
    edgeThreshold 0 n = (n - 1).choose 2 + 2 := by
  simp [edgeThreshold, Nat.choose_self]

/-- Bondy's edge count $\binom{n-2}{2}+4$ is the $k=1$ case of the general threshold. -/
@[category test, AMS 5]
theorem erdos_1012.variants.edgeThreshold_one {n : ℕ} (hn : 2 ≤ n) :
    edgeThreshold 1 n = (n - 2).choose 2 + 4 := by
  have hsub : n - 1 - 1 = n - 2 := by
    have := hn
    omega
  have hfour : (3).choose 2 + 1 = 4 := rfl
  unfold edgeThreshold
  rw [hsub, show (1 + 2) = 3 from rfl, Nat.add_assoc, hfour]

end Erdos1012
