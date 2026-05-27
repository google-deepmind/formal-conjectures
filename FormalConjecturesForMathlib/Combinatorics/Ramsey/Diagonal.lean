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


public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Lattice
public import FormalConjecturesForMathlib.Combinatorics.Ramsey

@[expose] public section

/-!
# Erdős–Szekeres 1935 upper bound for the diagonal Ramsey number

**Statement (Erdős–Szekeres 1935):** For every `k : ℕ`, the diagonal Ramsey number satisfies
`Combinatorics.hypergraphRamsey 2 k ≤ 4 ^ k`.

**Proof sketch.** Use the symmetric recursion `R(s, t) ≤ R(s-1, t) + R(s, t-1)` with base
cases `R(0, t) = R(s, 0) = 1`. Induction on `s + t` then gives `R(s, t) ≤ C(s+t, s)`; for
`s = t = k` this is `R(k, k) ≤ C(2k, k) ≤ 4 ^ k` (the Catalan-like central binomial
coefficient bound).

The whole argument is phrased directly on the Mathlib-style coloring data
`c : Finset (Fin m) → Bool` of 2-element subsets — no auxiliary "edge colouring" structure
is introduced.

**Reference:** [ES35] Erdős, P. and Szekeres, G. (1935). "A combinatorial problem in
geometry." *Compositio Math.* **2**, pp. 463–470.
-/

namespace Combinatorics
namespace Diagonal

/-- **Central binomial bound (Mathlib wrapper).** `C(2n, n) ≤ 4 ^ n`.

This specialises `Nat.choose_middle_le_pow : (2n+1).choose n ≤ 4^n` by observing that
`(2n).choose n ≤ (2n+1).choose n` via the monotonicity lemma `Nat.choose_le_succ`. -/
lemma central_binomial_le_four_pow (n : ℕ) : (2 * n).choose n ≤ 4 ^ n := by
  have h₁ : (2 * n).choose n ≤ (2 * n + 1).choose n := Nat.choose_le_succ (2 * n) n
  exact h₁.trans (Nat.choose_middle_le_pow n)

/-! ## Off-diagonal Ramsey via a subset-indexed predicate

Rather than introduce an auxiliary edge-colouring structure, we phrase the off-diagonal
Ramsey statement as a property of an arbitrary `Finset (Fin m)` of sufficient cardinality
inside a `Bool`-valued coloring of all subsets of `Fin m`. We only ever query the coloring
on 2-element subsets. This setup matches the shape of
`Combinatorics.hypergraphRamsey 2` directly. -/

/-- `HasRamseyProperty N s t` asserts: for every `m`, every coloring
`c : Finset (Fin m) → Bool`, and every `V : Finset (Fin m)` with `V.card ≥ N`, the subset
`V` contains either a subset of size `s` whose 2-element subsets are all `false`-coloured,
or a subset of size `t` whose 2-element subsets are all `true`-coloured.

This is the "off-diagonal Ramsey number does not exceed `N`" form of the classical
Erdős–Szekeres Ramsey recurrence, packaged in the same shape used by
`Combinatorics.hypergraphRamsey`. -/
def HasRamseyProperty (N s t : ℕ) : Prop :=
  ∀ {m : ℕ} (c : Finset (Fin m) → Bool) (V : Finset (Fin m)), N ≤ V.card →
    (∃ S ⊆ V, S.card = s ∧ ∀ e ⊆ S, e.card = 2 → c e = false) ∨
    (∃ S ⊆ V, S.card = t ∧ ∀ e ⊆ S, e.card = 2 → c e = true)

/-- **Monotonicity.** If `N ≤ N'` then `HasRamseyProperty N s t → HasRamseyProperty N' s t`. -/
lemma HasRamseyProperty.mono {N N' s t : ℕ} (hNN' : N ≤ N') (h : HasRamseyProperty N s t) :
    HasRamseyProperty N' s t := by
  intro m c V hV
  exact h c V (hNN'.trans hV)

/-- **Base case `s = 0`.** Any `V` contains an empty `false`-monochromatic set. -/
lemma hasRamseyProperty_zero_left (N t : ℕ) : HasRamseyProperty N 0 t := by
  intro m c V _hV
  refine Or.inl ⟨∅, Finset.empty_subset _, by simp, ?_⟩
  intro e he _
  -- e ⊆ ∅, so e = ∅, but e.card = 2.
  have he_empty : e = ∅ := Finset.subset_empty.mp he
  simp [he_empty] at *

/-- **Base case `t = 0`.** Any `V` contains an empty `true`-monochromatic set. -/
lemma hasRamseyProperty_zero_right (N s : ℕ) : HasRamseyProperty N s 0 := by
  intro m c V _hV
  refine Or.inr ⟨∅, Finset.empty_subset _, by simp, ?_⟩
  intro e he _
  have he_empty : e = ∅ := Finset.subset_empty.mp he
  simp [he_empty] at *

/-- A singleton has no 2-element subsets, hence is monochromatic of any colour. -/
lemma forall_two_subset_singleton {m : ℕ} (v : Fin m) (b : Bool)
    (c : Finset (Fin m) → Bool) :
    ∀ e ⊆ ({v} : Finset (Fin m)), e.card = 2 → c e = b := by
  intro e he hecard
  -- e ⊆ {v} forces e.card ≤ 1, contradicting e.card = 2.
  have : e.card ≤ 1 := by
    have := Finset.card_le_card he
    simpa using this
  omega

/-- **Base case `s = 1`.** Any nonempty `V` contains a singleton `false`-monochromatic set. -/
lemma hasRamseyProperty_one_left (t : ℕ) : HasRamseyProperty 1 1 t := by
  intro m c V hV
  obtain ⟨v, hv⟩ : V.Nonempty := Finset.card_pos.mp (by omega)
  refine Or.inl ⟨{v}, by simpa using hv, by simp, ?_⟩
  exact forall_two_subset_singleton v false c

/-- **Base case `t = 1`.** Any nonempty `V` contains a singleton `true`-monochromatic set. -/
lemma hasRamseyProperty_one_right (s : ℕ) : HasRamseyProperty 1 s 1 := by
  intro m c V hV
  obtain ⟨v, hv⟩ : V.Nonempty := Finset.card_pos.mp (by omega)
  refine Or.inr ⟨{v}, by simpa using hv, by simp, ?_⟩
  exact forall_two_subset_singleton v true c

/-- **Pigeonhole step: splitting `V \ {v}` by colour.** For any vertex `v ∈ V`, the set
`V.erase v` partitions into `false`-neighbours of `v` and `true`-neighbours of `v`, and the
cardinalities sum to `V.card - 1`. -/
lemma card_false_true_split {m : ℕ} (c : Finset (Fin m) → Bool) (V : Finset (Fin m))
    {v : Fin m} (hv : v ∈ V) :
    ((V.erase v).filter (fun u => c {v, u} = false)).card
      + ((V.erase v).filter (fun u => c {v, u} = true)).card = V.card - 1 := by
  classical
  have hsplit :
      ((V.erase v).filter (fun u => c {v, u} = false)).card
        + ((V.erase v).filter (fun u => ¬ c {v, u} = false)).card = (V.erase v).card :=
    Finset.card_filter_add_card_filter_not (s := V.erase v) (fun u => c {v, u} = false)
  have hne_true : ∀ u : Fin m, ¬ (c {v, u} = false) ↔ c {v, u} = true := by
    intro u
    cases c {v, u} <;> simp
  have hrw : ((V.erase v).filter (fun u => ¬ c {v, u} = false)).card
      = ((V.erase v).filter (fun u => c {v, u} = true)).card := by
    congr 1
    ext u
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro _
    exact hne_true u
  rw [hrw] at hsplit
  rw [hsplit, Finset.card_erase_of_mem hv]

/-- Extending a `false`-monochromatic clique `S` by a vertex `v` that is `false`-adjacent
to every element of `S`. -/
private lemma mono_false_insert {m : ℕ} {c : Finset (Fin m) → Bool}
    {S : Finset (Fin m)} (hSmono : ∀ e ⊆ S, e.card = 2 → c e = false)
    {v : Fin m} (hvAdj : ∀ u ∈ S, c {v, u} = false) :
    ∀ e ⊆ insert v S, e.card = 2 → c e = false := by
  classical
  intro e he hecard
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hecard
  -- Each of x, y is in insert v S, so equals v or lives in S.
  have hx : x ∈ insert v S := he (Finset.mem_insert_self _ _)
  have hy : y ∈ insert v S :=
    he (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))
  rcases Finset.mem_insert.mp hx with hx_eq | hxS
  · rcases Finset.mem_insert.mp hy with hy_eq | hyS
    · exact (hxy (hx_eq.trans hy_eq.symm)).elim
    · -- x = v, y ∈ S; pair {x, y} = {v, y}, use hvAdj.
      rw [hx_eq]; exact hvAdj y hyS
  · rcases Finset.mem_insert.mp hy with hy_eq | hyS
    · -- x ∈ S, y = v; pair {x, y} = {x, v} = {v, x}.
      rw [hy_eq, Finset.pair_comm]; exact hvAdj x hxS
    · -- {x, y} ⊆ S.
      have hsub : ({x, y} : Finset (Fin m)) ⊆ S := by
        intro z hz
        rcases Finset.mem_insert.mp hz with hz_eq | hz'
        · rw [hz_eq]; exact hxS
        · rw [Finset.mem_singleton.mp hz']; exact hyS
      have hcard2 : ({x, y} : Finset (Fin m)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
      exact hSmono _ hsub hcard2

/-- Extending a `true`-monochromatic clique `S` by a vertex `v` that is `true`-adjacent
to every element of `S`. -/
private lemma mono_true_insert {m : ℕ} {c : Finset (Fin m) → Bool}
    {S : Finset (Fin m)} (hSmono : ∀ e ⊆ S, e.card = 2 → c e = true)
    {v : Fin m} (hvAdj : ∀ u ∈ S, c {v, u} = true) :
    ∀ e ⊆ insert v S, e.card = 2 → c e = true := by
  classical
  intro e he hecard
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hecard
  have hx : x ∈ insert v S := he (Finset.mem_insert_self _ _)
  have hy : y ∈ insert v S :=
    he (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))
  rcases Finset.mem_insert.mp hx with hx_eq | hxS
  · rcases Finset.mem_insert.mp hy with hy_eq | hyS
    · exact (hxy (hx_eq.trans hy_eq.symm)).elim
    · rw [hx_eq]; exact hvAdj y hyS
  · rcases Finset.mem_insert.mp hy with hy_eq | hyS
    · rw [hy_eq, Finset.pair_comm]; exact hvAdj x hxS
    · have hsub : ({x, y} : Finset (Fin m)) ⊆ S := by
        intro z hz
        rcases Finset.mem_insert.mp hz with hz_eq | hz'
        · rw [hz_eq]; exact hxS
        · rw [Finset.mem_singleton.mp hz']; exact hyS
      have hcard2 : ({x, y} : Finset (Fin m)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
      exact hSmono _ hsub hcard2

/-- **Recurrence.** If `HasRamseyProperty Ns s (t+1)` and `HasRamseyProperty Nt (s+1) t`
hold, then `HasRamseyProperty (Ns + Nt) (s+1) (t+1)` holds.

This is the core Erdős–Szekeres 1935 pigeonhole step: pick any vertex `v ∈ V`, split
`V.erase v` into `false`-neighbours `R_v` and `true`-neighbours `B_v`; by pigeonhole
`|R_v| ≥ Ns` or `|B_v| ≥ Nt`. In the first case, invoke `HasRamseyProperty Ns s (t+1)`
on `R_v`: either we get a `false`-mono `K_s` on `R_v` (extend by `v` to a `false`-mono
`K_{s+1}` on `V`), or a `true`-mono `K_{t+1}` on `R_v ⊆ V` (done). The second case is
symmetric. -/
lemma HasRamseyProperty.step {Ns Nt s t : ℕ}
    (hs : HasRamseyProperty Ns s (t + 1))
    (ht : HasRamseyProperty Nt (s + 1) t) (hNs : 1 ≤ Ns) :
    HasRamseyProperty (Ns + Nt) (s + 1) (t + 1) := by
  classical
  intro m c V hV
  -- V is nonempty since V.card ≥ Ns + Nt ≥ 1.
  have hVpos : 0 < V.card := by
    have : 1 ≤ V.card := Nat.le_trans hNs (Nat.le_trans (Nat.le_add_right _ _) hV)
    exact this
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hVpos
  -- Split V.erase v by colour of pair {v, u}.
  set R := (V.erase v).filter (fun u => c {v, u} = false) with hR_def
  set B := (V.erase v).filter (fun u => c {v, u} = true) with hB_def
  have hsplit : R.card + B.card = V.card - 1 :=
    card_false_true_split c V hv
  have hRsubV : R ⊆ V := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hBsubV : B ⊆ V := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hvnR : v ∉ R := fun h => Finset.notMem_erase _ _ (Finset.mem_of_mem_filter _ h)
  have hvnB : v ∉ B := fun h => Finset.notMem_erase _ _ (Finset.mem_of_mem_filter _ h)
  -- Pigeonhole: either R.card ≥ Ns or B.card ≥ Nt.
  by_cases hRcard : Ns ≤ R.card
  · -- Case 1: apply `hs` on R to get false K_s (extend by v) or true K_{t+1}.
    rcases hs c R hRcard with ⟨S, hSsub, hScard, hSmono⟩ | ⟨S, hSsub, hScard, hSmono⟩
    · -- false K_s on R ⊆ V; extend by v (false-adjacent to all of R) to false K_{s+1}.
      have hvS : v ∉ S := fun h => hvnR (hSsub h)
      refine Or.inl ⟨insert v S, ?_, ?_, ?_⟩
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu'
        · exact hv
        · exact hRsubV (hSsub hu')
      · rw [Finset.card_insert_of_notMem hvS, hScard]
      · apply mono_false_insert hSmono
        intro u hu
        have hu' : u ∈ R := hSsub hu
        exact (Finset.mem_filter.mp hu').2
    · -- true K_{t+1} on R ⊆ V.
      exact Or.inr ⟨S, hSsub.trans hRsubV, hScard, hSmono⟩
  · -- Case 2: R.card < Ns, so B.card ≥ Nt. Apply `ht` on B symmetrically.
    push_neg at hRcard
    have hBcard : Nt ≤ B.card := by
      have hV_sub : Ns + Nt ≤ V.card := hV
      omega
    rcases ht c B hBcard with ⟨S, hSsub, hScard, hSmono⟩ | ⟨S, hSsub, hScard, hSmono⟩
    · -- false K_{s+1} on B ⊆ V.
      exact Or.inl ⟨S, hSsub.trans hBsubV, hScard, hSmono⟩
    · -- true K_t on B; extend by v (true-adjacent to all of B) to true K_{t+1}.
      have hvS : v ∉ S := fun h => hvnB (hSsub h)
      refine Or.inr ⟨insert v S, ?_, ?_, ?_⟩
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu'
        · exact hv
        · exact hBsubV (hSsub hu')
      · rw [Finset.card_insert_of_notMem hvS, hScard]
      · apply mono_true_insert hSmono
        intro u hu
        have hu' : u ∈ B := hSsub hu
        exact (Finset.mem_filter.mp hu').2

/-- **Binomial bound via Erdős–Szekeres induction.**
`HasRamseyProperty (Nat.choose (s + t) s) s t` for all `s, t`. -/
lemma hasRamseyProperty_choose : ∀ (s t : ℕ),
    HasRamseyProperty (Nat.choose (s + t) s) s t := by
  -- Induction on `s + t` via `Nat.strong_induction_on`.
  suffices h : ∀ (n : ℕ), ∀ (s t : ℕ), s + t = n → HasRamseyProperty (Nat.choose n s) s t by
    intro s t
    exact h (s + t) s t rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s t hst
    match s, t, hst with
    | 0, t, hst =>
      -- C(n, 0) = 1; we want HasRamseyProperty 1 0 t, which follows from the s = 0 base.
      show HasRamseyProperty (Nat.choose n 0) 0 t
      rw [Nat.choose_zero_right]
      exact HasRamseyProperty.mono (Nat.zero_le _) (hasRamseyProperty_zero_left 0 t)
    | s+1, 0, hst =>
      -- C(n, s+1) with t = 0. Use the t = 0 base case.
      show HasRamseyProperty (Nat.choose n (s+1)) (s+1) 0
      exact HasRamseyProperty.mono (Nat.zero_le _) (hasRamseyProperty_zero_right 0 (s+1))
    | s+1, t+1, hst =>
      -- Pascal: C(n, s+1) = C(n-1, s) + C(n-1, s+1), where n = s+1+t+1 = s+t+2.
      -- i.e. n - 1 = s + (t+1) = (s+1) + t.
      have hn_pred : n - 1 + 1 = n := by omega
      have hs_ih : HasRamseyProperty (Nat.choose (n - 1) s) s (t + 1) := by
        apply ih (n - 1) (by omega) s (t + 1)
        omega
      have ht_ih : HasRamseyProperty (Nat.choose (n - 1) (s + 1)) (s + 1) t := by
        apply ih (n - 1) (by omega) (s + 1) t
        omega
      have hNs_pos : 1 ≤ Nat.choose (n - 1) s := by
        have : s ≤ n - 1 := by omega
        exact Nat.choose_pos this
      have hrec : HasRamseyProperty (Nat.choose (n - 1) s + Nat.choose (n - 1) (s + 1))
          (s + 1) (t + 1) := HasRamseyProperty.step hs_ih ht_ih hNs_pos
      -- Pascal's identity: C(n, s+1) = C(n-1, s) + C(n-1, s+1) when n ≥ 1.
      have hpascal : Nat.choose n (s + 1) = Nat.choose (n - 1) s + Nat.choose (n - 1) (s + 1) := by
        conv_lhs => rw [← hn_pred]
        rw [Nat.choose_succ_succ]
      show HasRamseyProperty (Nat.choose n (s + 1)) (s + 1) (t + 1)
      rw [hpascal]
      exact hrec

end Diagonal

/-- **Erdős–Szekeres 1935** in `hypergraphRamsey` form:
`Combinatorics.hypergraphRamsey 2 k ≤ 4 ^ k` for all `k`.

**Proof.** `Diagonal.hasRamseyProperty_choose` applied at `s = t = k` and the full vertex
set `V = Finset.univ` of `Fin (C(2k, k))` shows that `C(2k, k)` is a member of the defining
set of `hypergraphRamsey 2 k`, hence by `Nat.sInf_le` we get
`hypergraphRamsey 2 k ≤ C(2k, k)`; the central binomial bound
`C(2k, k) ≤ 4 ^ k` closes the result. -/
lemma _root_.Combinatorics.hypergraphRamsey_two_le_four_pow (k : ℕ) :
    Combinatorics.hypergraphRamsey 2 k ≤ 4 ^ k := by
  -- Show C(2k, k) is in the hypergraphRamsey defining set.
  have hprop : Diagonal.HasRamseyProperty (Nat.choose (k + k) k) k k :=
    Diagonal.hasRamseyProperty_choose k k
  have hmem : Nat.choose (k + k) k ∈ { m | ∀ (c : Finset (Fin m) → Bool),
      ∃ (S : Finset (Fin m)), S.card = k ∧ ∃ (color : Bool),
        ∀ (e : Finset (Fin m)), e ⊆ S → e.card = 2 → c e = color } := by
    intro c
    have hV : Nat.choose (k + k) k ≤
        (Finset.univ : Finset (Fin (Nat.choose (k + k) k))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
    rcases hprop c Finset.univ hV with ⟨S, _hSsub, hScard, hSmono⟩ | ⟨S, _hSsub, hScard, hSmono⟩
    · exact ⟨S, hScard, false, hSmono⟩
    · exact ⟨S, hScard, true, hSmono⟩
  have hle : Combinatorics.hypergraphRamsey 2 k ≤ Nat.choose (k + k) k := Nat.sInf_le hmem
  have h2kk : Nat.choose (k + k) k = Nat.choose (2 * k) k := by rw [two_mul]
  rw [h2kk] at hle
  exact hle.trans (Diagonal.central_binomial_le_four_pow k)

end Combinatorics
