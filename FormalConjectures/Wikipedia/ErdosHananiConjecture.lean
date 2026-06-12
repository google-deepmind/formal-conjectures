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
# Erdős–Hanani conjecture

For integers $2 \leq r < k$, let $m(n, k, r)$ denote the maximum number of $k$-element
subsets of an $n$-element set such that every $r$-element subset is contained in *at most*
one of them (a *packing*, also known as a partial Steiner system), and let $M(n, k, r)$
denote the minimum number of $k$-element subsets such that every $r$-element subset is
contained in *at least* one of them (a *covering*).

Counting $r$-subsets gives the trivial bounds
$$m(n, k, r) \leq \binom{n}{r}\Big/\binom{k}{r} \leq M(n, k, r),$$
and Erdős and Hanani [ErHa63] conjectured that both are asymptotically sharp:
$$\lim_{n \to \infty} \frac{m(n, k, r)}{\binom{n}{r}/\binom{k}{r}}
  = \lim_{n \to \infty} \frac{M(n, k, r)}{\binom{n}{r}/\binom{k}{r}} = 1.$$

The conjecture was proved by Rödl [Ro85]; the semi-random method introduced in his proof
became known as the *Rödl nibble* and was vastly generalised, notably by Frankl–Rödl,
Pippenger–Spencer and Kahn. Much later Keevash, and subsequently Glock–Kühn–Lo–Osthus,
proved the existence of exact Steiner systems $S(r, k, n)$ for all sufficiently large $n$
satisfying the necessary divisibility conditions.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/R%C3%B6dl_nibble)

*References:*
- [ErHa63] P. Erdős and H. Hanani, *On a limit theorem in combinatorial analysis*,
  Publ. Math. Debrecen **10** (1963), 10–13
- [Ro85] V. Rödl, *On a packing and covering problem*,
  European J. Combin. **6** (1985), 69–78
-/

namespace ErdosHanani

/--
`IsPacking n k r F` means that `F` is a family of `k`-element subsets of `{0, …, n - 1}`
such that every `r`-element subset is contained in at most one member of `F`. Such a
family is called a *packing* (or *partial Steiner system*).
-/
def IsPacking (n k r : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  (∀ s ∈ F, s.card = k) ∧
    ∀ t : Finset (Fin n), t.card = r → (F.filter fun s => t ⊆ s).card ≤ 1

/--
`IsCovering n k r F` means that `F` is a family of `k`-element subsets of `{0, …, n - 1}`
such that every `r`-element subset is contained in at least one member of `F`. Such a
family is called a *covering*.
-/
def IsCovering (n k r : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  (∀ s ∈ F, s.card = k) ∧
    ∀ t : Finset (Fin n), t.card = r → ∃ s ∈ F, t ⊆ s

/--
`maxPacking n k r` is the quantity $m(n, k, r)$: the maximum size of a family of
`k`-element subsets of `{0, …, n - 1}` in which every `r`-element subset is contained in
at most one member. The supremum is over a nonempty (the empty family is a packing) and
bounded (a packing has at most $2^n$ members) set, so it is attained.
-/
noncomputable def maxPacking (n k r : ℕ) : ℕ :=
  sSup {N | ∃ F : Finset (Finset (Fin n)), IsPacking n k r F ∧ F.card = N}

/--
`minCovering n k r` is the quantity $M(n, k, r)$: the minimum size of a family of
`k`-element subsets of `{0, …, n - 1}` containing every `r`-element subset in at least one
member. For $r \leq k \leq n$ a covering exists (take all `k`-element subsets); when no
covering exists, `sInf` takes the junk value `0`, which does not affect the asymptotic
statements below.
-/
noncomputable def minCovering (n k r : ℕ) : ℕ :=
  sInf {N | ∃ F : Finset (Finset (Fin n)), IsCovering n k r F ∧ F.card = N}

/--
The **Erdős–Hanani conjecture**, packing version, proved by Rödl [Ro85]: for fixed
$2 \leq r < k$,
$$\lim_{n \to \infty} \frac{m(n, k, r)}{\binom{n}{r}/\binom{k}{r}} = 1.$$
-/
@[category research solved, AMS 5]
theorem erdos_hanani_packing (k r : ℕ) (hr : 2 ≤ r) (hk : r < k) :
    Filter.Tendsto
      (fun n => (maxPacking n k r : ℝ) / ((n.choose r : ℝ) / (k.choose r : ℝ)))
      Filter.atTop (nhds 1) := by
  sorry

/--
The **Erdős–Hanani conjecture**, covering version, proved by Rödl [Ro85]: for fixed
$2 \leq r < k$,
$$\lim_{n \to \infty} \frac{M(n, k, r)}{\binom{n}{r}/\binom{k}{r}} = 1.$$
-/
@[category research solved, AMS 5]
theorem erdos_hanani_covering (k r : ℕ) (hr : 2 ≤ r) (hk : r < k) :
    Filter.Tendsto
      (fun n => (minCovering n k r : ℝ) / ((n.choose r : ℝ) / (k.choose r : ℝ)))
      Filter.atTop (nhds 1) := by
  sorry

/-- The empty family is a packing, so the set defining `maxPacking` is nonempty. -/
@[category test, AMS 5]
theorem isPacking_empty (n k r : ℕ) : IsPacking n k r ∅ := by
  refine ⟨by simp, fun t ht => ?_⟩
  simp

/-- Every packing has at most $2^n$ members, so the set defining `maxPacking` is bounded
above and the supremum is attained. -/
@[category test, AMS 5]
theorem maxPacking_le_two_pow (n k r : ℕ) : maxPacking n k r ≤ 2 ^ n := by
  have hne : {N | ∃ F : Finset (Finset (Fin n)), IsPacking n k r F ∧ F.card = N}.Nonempty :=
    ⟨0, ∅, isPacking_empty n k r, rfl⟩
  refine csSup_le hne ?_
  rintro N ⟨F, -, rfl⟩
  calc F.card ≤ Fintype.card (Finset (Fin n)) := F.card_le_univ
    _ = 2 ^ n := by simp

/-- For $r \leq k \leq n$, the family of all `k`-element subsets is a covering, so the set
defining `minCovering` is nonempty. -/
@[category test, AMS 5]
theorem isCovering_powersetCard (n k r : ℕ) (hrk : r ≤ k) (hkn : k ≤ n) :
    IsCovering n k r ((Finset.univ : Finset (Fin n)).powersetCard k) := by
  refine ⟨fun s hs => (Finset.mem_powersetCard.mp hs).2, fun t ht => ?_⟩
  obtain ⟨s, hts, hs⟩ := Finset.exists_superset_card_eq (ht.le.trans hrk)
    (by simpa using hkn)
  exact ⟨s, Finset.mem_powersetCard.mpr ⟨s.subset_univ, hs⟩, hts⟩

end ErdosHanani
