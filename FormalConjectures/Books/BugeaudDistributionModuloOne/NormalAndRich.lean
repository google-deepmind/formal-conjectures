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
# Normal and rich numbers and the sequence $(b^n \xi)$ modulo one

Let $b \ge 2$ be an integer. A real number $\xi$ is normal in base $b$ if and only if the
sequence $(b^n \xi)_{n \ge 0}$ is uniformly distributed modulo one. This was proved by Wall
[Wal49]; see also [Bug12, Theorem 4.14] and [EvdPSW03, p. 127].

A real number $\xi$ is rich (or disjunctive) in base $b$ if every finite block of digits occurs in
its base-$b$ expansion. By the same argument, $\xi$ is rich in base $b$ if and only if the
sequence $(b^n \xi)_{n \ge 0}$ is dense modulo one [Bug12, Section 4.4].

The two easy implications, normal implies rich and uniformly distributed implies dense, are
`NormalNumber.IsNormalInBase.isRichInBase` and `IsEquidistributedModuloOne.dense_range`.

*References:*
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Cambridge Tracts in Mathematics 193. Cambridge University Press, 2012. Chapter 4.
  - [Wal49] Wall, Donald Dines. "Normal numbers." Ph.D. thesis, University of California,
    Berkeley, 1949.
  - [EvdPSW03] Everest, Graham, Alf van der Poorten, Igor Shparlinski, and Thomas Ward.
    "Recurrence sequences." Mathematical Surveys and Monographs 104. American Mathematical
    Society, Providence, RI, 2003.
-/

@[expose] public section

open NormalNumber Filter Topology

namespace BugeaudNormalAndRich

/-- The natural number formed by the first `k` base-`b` digits of the fractional part of `y`. -/
noncomputable def digitPrefix (b k : ℕ) (y : ℝ) : ℕ :=
  ⌊(b : ℝ) ^ k * Int.fract y⌋₊

/-- The natural number with base-`b` digits `w 0, …, w (k - 1)`, most significant first. -/
def ofBlock (b : ℕ) (w : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => b * ofBlock b w k + w k

/-- The proportion of indices `m < n` such that the fractional part of `s m` lies in `S`. -/
noncomputable def visitFreq (s : ℕ → ℝ) (S : Set ℝ) [DecidablePred (· ∈ S)] (n : ℕ) : ℝ :=
  (((Finset.range n).filter fun m => Int.fract (s m) ∈ S).card : ℝ) / n

@[category API, AMS 11]
theorem digitPrefix_zero (b : ℕ) (y : ℝ) : digitPrefix b 0 y = 0 := by
  simp [digitPrefix, Int.fract_lt_one]

@[category API, AMS 11]
theorem digitPrefix_succ {b : ℕ} (hb : 0 < b) (k : ℕ) (y : ℝ) :
    digitPrefix b (k + 1) y = b * digitPrefix b k y + digitSeq b y k := by
  have hb' : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
  have h : digitPrefix b (k + 1) y / b = digitPrefix b k y := by
    rw [digitPrefix, digitPrefix, ← Nat.floor_div_natCast]
    congr 1
    field_simp
    ring
  rw [← h]
  exact (Nat.div_add_mod _ _).symm

@[category API, AMS 11]
theorem digitPrefix_lt {b : ℕ} (hb : 0 < b) (k : ℕ) (y : ℝ) : digitPrefix b k y < b ^ k := by
  have hB : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  rw [digitPrefix, Nat.floor_lt (mul_nonneg hB.le (Int.fract_nonneg y))]
  push_cast
  exact mul_lt_of_lt_one_right hB (Int.fract_lt_one y)

@[category API, AMS 11]
theorem digitPrefix_eq_iff {b : ℕ} (hb : 0 < b) (k m : ℕ) (y : ℝ) :
    digitPrefix b k y = m ↔
      Int.fract y ∈ Set.Ico ((m : ℝ) / (b : ℝ) ^ k) (((m : ℝ) + 1) / (b : ℝ) ^ k) := by
  have hB : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  rw [digitPrefix, Nat.floor_eq_iff (mul_nonneg hB.le (Int.fract_nonneg y)), Set.mem_Ico,
    div_le_iff₀ hB, lt_div_iff₀ hB, mul_comm (Int.fract y)]

@[category API, AMS 11]
theorem digitPrefix_add {b : ℕ} (i j : ℕ) (x : ℝ) :
    digitPrefix b (i + j) x = digitPrefix b j ((b : ℝ) ^ i * x) + b ^ j * digitPrefix b i x := by
  have hnn : 0 ≤ (b : ℝ) ^ i * Int.fract x := mul_nonneg (by positivity) (Int.fract_nonneg x)
  have hfr : Int.fract ((b : ℝ) ^ i * x) =
      (b : ℝ) ^ i * Int.fract x - (⌊(b : ℝ) ^ i * Int.fract x⌋₊ : ℝ) := by
    have h1 : (b : ℝ) ^ i * x = (b : ℝ) ^ i * Int.fract x + ((b ^ i * ⌊x⌋ : ℤ) : ℝ) := by
      push_cast
      rw [← Int.fract_add_floor x]
      ring_nf
      simp
    rw [h1, Int.fract_add_intCast, Int.fract, ← Int.natCast_floor_eq_floor hnn]
    push_cast
    ring
  rw [digitPrefix, digitPrefix, digitPrefix, hfr, add_comm, ← Nat.floor_add_natCast]
  · congr 1
    rw [pow_add]
    push_cast
    ring
  · exact mul_nonneg (by positivity) (sub_nonneg.2 (Nat.floor_le hnn))

@[category API, AMS 11]
theorem digitSeq_add {b : ℕ} (i j : ℕ) (x : ℝ) :
    digitSeq b x (i + j) = digitSeq b ((b : ℝ) ^ i * x) j := by
  have h := digitPrefix_add (b := b) i (j + 1) x
  rw [← add_assoc] at h
  change digitPrefix b (i + j + 1) x % b = digitPrefix b (j + 1) ((b : ℝ) ^ i * x) % b
  rw [h, pow_succ, mul_comm (b ^ j) b, mul_assoc, Nat.add_mul_mod_self_left]

@[category API, AMS 11]
theorem mul_add_eq_mul_add_iff {b a r a' r' : ℕ} (hb : 0 < b) (hr : r < b) (hr' : r' < b) :
    b * a + r = b * a' + r' ↔ a = a' ∧ r = r' := by
  refine ⟨fun h => ?_, fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ rfl⟩
  have h1 := congrArg (· / b) h
  have h2 := congrArg (· % b) h
  simp only [Nat.mul_add_div hb, Nat.div_eq_of_lt hr, Nat.div_eq_of_lt hr', add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr'] at h1 h2
  exact ⟨h1, h2⟩

@[category API, AMS 11]
theorem forall_digitSeq_eq_iff {b : ℕ} (hb : 0 < b) {w : ℕ → ℕ} (hw : ∀ j, w j < b) (k : ℕ)
    (y : ℝ) : (∀ j < k, digitSeq b y j = w j) ↔ digitPrefix b k y = ofBlock b w k := by
  induction k with
  | zero => simp [digitPrefix_zero, ofBlock]
  | succ k ih =>
    rw [Nat.forall_lt_succ_right, ih, digitPrefix_succ hb, ofBlock,
      mul_add_eq_mul_add_iff hb (show digitSeq b y k < b from Nat.mod_lt _ hb) (hw k)]

@[category API, AMS 11]
theorem ofBlock_lt {b : ℕ} {w : ℕ → ℕ} (hw : ∀ j, w j < b) (k : ℕ) : ofBlock b w k < b ^ k := by
  induction k with
  | zero => simp [ofBlock]
  | succ k ih =>
    calc b * ofBlock b w k + w k < b * (ofBlock b w k + 1) := by linarith [hw k]
      _ ≤ b * b ^ k := Nat.mul_le_mul_left _ ih
      _ = b ^ (k + 1) := by ring

@[category API, AMS 11]
theorem ofBlock_congr {b : ℕ} {w w' : ℕ → ℕ} (k : ℕ) (h : ∀ j < k, w j = w' j) :
    ofBlock b w k = ofBlock b w' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ofBlock, ofBlock, ih fun j hj => h j (by omega), h k (by omega)]

@[category API, AMS 11]
theorem exists_ofBlock_eq {b : ℕ} (hb : 0 < b) (k : ℕ) :
    ∀ m < b ^ k, ∃ w : ℕ → ℕ, (∀ j, w j < b) ∧ ofBlock b w k = m := by
  induction k with
  | zero =>
    intro m hm
    rw [pow_zero, Nat.lt_one_iff] at hm
    exact ⟨fun _ => 0, fun _ => hb, hm.symm⟩
  | succ k ih =>
    intro m hm
    obtain ⟨w, hw, hwm⟩ := ih (m / b) ((Nat.div_lt_iff_lt_mul hb).2 (by rwa [← pow_succ]))
    refine ⟨Function.update w k (m % b), fun j => ?_, ?_⟩
    · rcases eq_or_ne j k with rfl | hj
      · simpa using Nat.mod_lt m hb
      · simpa [hj] using hw j
    · rw [ofBlock, ofBlock_congr (w' := w) k fun j hj => Function.update_of_ne hj.ne _ _, hwm,
        Function.update_self]
      exact Nat.div_add_mod m b

@[category API, AMS 11]
theorem exists_extend {b k : ℕ} (hb : 0 < b) (wf : Fin k → ℕ) (hwf : ∀ j, wf j < b) :
    ∃ w : ℕ → ℕ, (∀ j, w j < b) ∧ ∀ j : Fin k, wf j = w j := by
  refine ⟨fun j => if hj : j < k then wf ⟨j, hj⟩ else 0, fun j => ?_, fun j => by simp [j.isLt]⟩
  dsimp only
  split_ifs
  exacts [hwf _, hb]

/-- A block of digits at position `i` corresponds to a `b`-adic interval for `b ^ i * x`. -/
@[category API, AMS 11]
theorem block_iff {b : ℕ} (hb : 0 < b) {w : ℕ → ℕ} (hw : ∀ j, w j < b) (k i : ℕ) (x : ℝ) :
    (∀ j : Fin k, digitSeq b x (i + j) = w j) ↔
      Int.fract ((b : ℝ) ^ i * x) ∈ Set.Ico ((ofBlock b w k : ℝ) / (b : ℝ) ^ k)
        (((ofBlock b w k : ℝ) + 1) / (b : ℝ) ^ k) := by
  rw [← digitPrefix_eq_iff hb, ← forall_digitSeq_eq_iff hb hw, Fin.forall_iff]
  simp only [digitSeq_add]

@[category API, AMS 11]
theorem visitFreq_mono {s : ℕ → ℝ} {S T : Set ℝ} [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ T)] (h : ∀ y ∈ Set.Ico (0 : ℝ) 1, y ∈ S → y ∈ T)
    (n : ℕ) : visitFreq s S n ≤ visitFreq s T n := by
  refine div_le_div_of_nonneg_right (Nat.cast_le.2 (Finset.card_le_card fun m hm => ?_))
    (Nat.cast_nonneg _)
  rw [Finset.mem_filter] at hm ⊢
  exact ⟨hm.1, h _ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩ hm.2⟩

@[category API, AMS 11]
theorem visitFreq_congr {s : ℕ → ℝ} {S T : Set ℝ} [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ T)] (h : S = T) : visitFreq s S = visitFreq s T := by
  subst h
  congr

@[category API, AMS 11]
theorem visitFreq_union {s : ℕ → ℝ} {S T : Set ℝ} [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ T)] (h : Disjoint S T) (n : ℕ) :
    visitFreq s (S ∪ T) n = visitFreq s S n + visitFreq s T n := by
  rw [visitFreq, visitFreq, visitFreq, ← add_div, ← Nat.cast_add, ← Finset.card_union_of_disjoint]
  · simp only [Set.mem_union, Finset.filter_or]
  · exact Finset.disjoint_filter.2 fun _ _ h1 h2 => Set.disjoint_left.1 h h1 h2

/-- Frequencies of unions of consecutive `b`-adic intervals. -/
@[category API, AMS 11]
theorem tendsto_visitFreq_Ico {b : ℕ} {s : ℕ → ℝ}
    (hA : ∀ k, ∀ m < b ^ k, Tendsto (visitFreq s (Set.Ico ((m : ℝ) / (b : ℝ) ^ k)
      (((m : ℝ) + 1) / (b : ℝ) ^ k))) atTop (𝓝 (1 / (b : ℝ) ^ k)))
    (k : ℕ) {m₁ m₂ : ℕ} (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ b ^ k) :
    Tendsto (visitFreq s (Set.Ico ((m₁ : ℝ) / (b : ℝ) ^ k) ((m₂ : ℝ) / (b : ℝ) ^ k))) atTop
      (𝓝 (((m₂ : ℝ) - m₁) / (b : ℝ) ^ k)) := by
  induction m₂, h₁₂ using Nat.le_induction with
  | base =>
    rw [sub_self, zero_div]
    refine tendsto_const_nhds.congr fun n => ?_
    simp [visitFreq]
  | succ m₂ h ih =>
    have hdiv : (m₁ : ℝ) / (b : ℝ) ^ k ≤ (m₂ : ℝ) / (b : ℝ) ^ k :=
      div_le_div_of_nonneg_right (Nat.cast_le.2 h) (by positivity)
    have hdiv' : (m₂ : ℝ) / (b : ℝ) ^ k ≤ ((m₂ : ℝ) + 1) / (b : ℝ) ^ k :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hset : Set.Ico ((m₁ : ℝ) / (b : ℝ) ^ k) (((m₂ + 1 : ℕ) : ℝ) / (b : ℝ) ^ k) =
        Set.Ico ((m₁ : ℝ) / (b : ℝ) ^ k) ((m₂ : ℝ) / (b : ℝ) ^ k) ∪
          Set.Ico ((m₂ : ℝ) / (b : ℝ) ^ k) (((m₂ : ℝ) + 1) / (b : ℝ) ^ k) := by
      rw [Set.Ico_union_Ico_eq_Ico hdiv hdiv']
      push_cast
      rfl
    have hsum := ((ih (by omega)).add (hA k m₂ (by omega))).congr
      (f₂ := visitFreq s (Set.Ico ((m₁ : ℝ) / (b : ℝ) ^ k) (((m₂ + 1 : ℕ) : ℝ) / (b : ℝ) ^ k)))
      fun n => by rw [visitFreq_congr hset, visitFreq_union Set.Ico_disjoint_Ico_same]
    convert hsum using 2
    push_cast
    ring

/-- `x` is normal in base `b` iff every `b`-adic interval has the expected frequency. -/
@[category API, AMS 11]
theorem isNormalInBase_iff_tendsto {b : ℕ} (hb : 0 < b) (x : ℝ) :
    IsNormalInBase b x ↔ ∀ k, ∀ m < b ^ k,
      Tendsto (visitFreq (fun n => (b : ℝ) ^ n * x) (Set.Ico ((m : ℝ) / (b : ℝ) ^ k)
        (((m : ℝ) + 1) / (b : ℝ) ^ k))) atTop (𝓝 (1 / (b : ℝ) ^ k)) := by
  constructor
  · intro h k m hm
    obtain ⟨w, hw, rfl⟩ := exists_ofBlock_eq hb k m hm
    refine (h k (fun j => w j) fun j => hw j).congr fun n => ?_
    simp only [visitFreq]
    congr 3
    exact Finset.filter_congr fun i _ => block_iff hb hw k i x
  · intro h k wf hwf
    obtain ⟨w, hw, hwf'⟩ := exists_extend hb wf hwf
    refine (h k _ (ofBlock_lt hw k)).congr fun n => ?_
    simp only [visitFreq, hwf']
    congr 3
    exact (Finset.filter_congr fun i _ => block_iff hb hw k i x).symm

/-- `x` is rich in base `b` iff every `b`-adic interval is visited. -/
@[category API, AMS 11]
theorem isRichInBase_iff_exists {b : ℕ} (hb : 0 < b) (x : ℝ) :
    IsRichInBase b x ↔ ∀ k, ∀ m < b ^ k, ∃ n, Int.fract ((b : ℝ) ^ n * x) ∈
      Set.Ico ((m : ℝ) / (b : ℝ) ^ k) (((m : ℝ) + 1) / (b : ℝ) ^ k) := by
  constructor
  · intro h k m hm
    obtain ⟨w, hw, rfl⟩ := exists_ofBlock_eq hb k m hm
    obtain ⟨i, hi⟩ := h k (fun j => w j) fun j => hw j
    exact ⟨i, (block_iff hb hw k i x).1 hi⟩
  · intro h k wf hwf
    obtain ⟨w, hw, hwf'⟩ := exists_extend hb wf hwf
    obtain ⟨i, hi⟩ := h k _ (ofBlock_lt hw k)
    refine ⟨i, fun j => ?_⟩
    rw [hwf']
    exact (block_iff hb hw k i x).2 hi j

@[category API, AMS 11]
theorem exists_one_div_pow_lt {b : ℕ} (hb : 2 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, 1 / (b : ℝ) ^ k < ε := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε
    ((div_lt_one (by positivity)).2 (by exact_mod_cast (by omega : 1 < b)) : (1 : ℝ) / b < 1)
  exact ⟨k, by rwa [div_pow, one_pow] at hk⟩

@[category API, AMS 11]
theorem add_one_div_pow_le_one {b k m : ℕ} (hm : m < b ^ k) :
    ((m : ℝ) + 1) / (b : ℝ) ^ k ≤ 1 :=
  div_le_one_of_le₀ (by exact_mod_cast Nat.succ_le_of_lt hm) (by positivity)

@[category API, AMS 11]
theorem coe_fract (y : ℝ) : ((Int.fract y : ℝ) : AddCircle (1 : ℝ)) = y := by
  rw [QuotientAddGroup.eq]
  exact ⟨⌊y⌋, by simp [← Int.self_sub_floor]⟩

@[category API, AMS 11]
theorem fract_eq_of_coe_eq {a c : ℝ} (h : (a : AddCircle (1 : ℝ)) = c) :
    Int.fract a = Int.fract c := by
  obtain ⟨z, hz⟩ := QuotientAddGroup.eq.1 h
  have hc : c = a + z := by
    simp only [zsmul_eq_mul, mul_one] at hz
    linarith
  rw [hc, Int.fract_add_intCast]

/-- Frequencies of `b`-adic intervals determine uniform distribution modulo one. -/
@[category API, AMS 11]
theorem tendsto_Ico_iff_isEquidistributedModuloOne {b : ℕ} (hb : 2 ≤ b) (s : ℕ → ℝ) :
    (∀ k, ∀ m < b ^ k, Tendsto (visitFreq s (Set.Ico ((m : ℝ) / (b : ℝ) ^ k)
      (((m : ℝ) + 1) / (b : ℝ) ^ k))) atTop (𝓝 (1 / (b : ℝ) ^ k))) ↔
    IsEquidistributedModuloOne s := by
  constructor
  · intro hA c d hcd hsub
    have hc0 : 0 ≤ c := (hsub ⟨le_rfl, hcd⟩).1
    have hd1 : d ≤ 1 := (hsub ⟨hcd, le_rfl⟩).2
    have hd0 : 0 ≤ d := hc0.trans hcd
    change Tendsto (visitFreq s (Set.Icc c d)) atTop (𝓝 ((d - c) / (1 - 0)))
    rw [sub_zero, div_one, tendsto_order]
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · obtain ⟨k, hk⟩ := exists_one_div_pow_lt hb (show 0 < (d - c - a) / 2 by linarith)
      have hB : (0 : ℝ) < (b : ℝ) ^ k := by positivity
      set B := (b : ℝ) ^ k with hBdef
      set m₂ := ⌊d * B⌋₊ with hm₂def
      set m₁ := min ⌈c * B⌉₊ m₂ with hm₁def
      have hm₂ : m₂ ≤ b ^ k := Nat.floor_le_of_le (by
        push_cast
        exact mul_le_of_le_one_left hB.le hd1)
      have hlim := tendsto_visitFreq_Ico hA k (min_le_right ⌈c * B⌉₊ m₂) hm₂
      have h1 : (m₁ : ℝ) < c * B + 1 :=
        (Nat.cast_le.2 (min_le_left _ _)).trans_lt (Nat.ceil_lt_add_one (mul_nonneg hc0 hB.le))
      have h2 : d * B - 1 < m₂ := Nat.sub_one_lt_floor _
      have h3 : 2 < d * B - c * B - a * B := by
        have := (div_lt_iff₀ hB).1 hk
        linarith
      have hgt : a < ((m₂ : ℝ) - m₁) / B := by
        rw [lt_div_iff₀ hB]
        linarith
      refine (hlim.eventually (lt_mem_nhds hgt)).mono fun n hn => hn.trans_le (visitFreq_mono ?_ n)
      rintro y - ⟨hy1, hy2⟩
      have hlt : m₁ < m₂ := by exact_mod_cast (div_lt_div_iff_of_pos_right hB).1 (hy1.trans_lt hy2)
      have hm₁ : m₁ = ⌈c * B⌉₊ := by
        rw [hm₁def]
        refine min_eq_left ?_
        by_contra hne
        rw [not_le] at hne
        rw [hm₁def, min_eq_right hne.le] at hlt
        exact lt_irrefl _ hlt
      constructor
      · calc c ≤ (m₁ : ℝ) / B := by
              rw [le_div_iff₀ hB, hm₁]
              exact Nat.le_ceil _
          _ ≤ y := hy1
      · calc y ≤ (m₂ : ℝ) / B := hy2.le
          _ ≤ d := by
              rw [div_le_iff₀ hB]
              exact Nat.floor_le (mul_nonneg hd0 hB.le)
    · obtain ⟨k, hk⟩ := exists_one_div_pow_lt hb (show 0 < (a - (d - c)) / 2 by linarith)
      have hB : (0 : ℝ) < (b : ℝ) ^ k := by positivity
      set B := (b : ℝ) ^ k with hBdef
      have hBnat : ((b ^ k : ℕ) : ℝ) = B := by push_cast; rfl
      set m₁ := ⌊c * B⌋₊ with hm₁def
      set m₂ := min (⌊d * B⌋₊ + 1) (b ^ k) with hm₂def
      have hm₁ : m₁ ≤ b ^ k := Nat.floor_le_of_le (by
        rw [hBnat]
        exact mul_le_of_le_one_left hB.le (hcd.trans hd1))
      have hm₁₂ : m₁ ≤ m₂ := le_min
        ((Nat.floor_le_floor (mul_le_mul_of_nonneg_right hcd hB.le)).trans (Nat.le_succ _)) hm₁
      have hlim := tendsto_visitFreq_Ico hA k hm₁₂ (min_le_right _ _)
      have h1 : c * B - 1 < m₁ := Nat.sub_one_lt_floor _
      have h2 : (m₂ : ℝ) ≤ d * B + 1 := by
        have : (m₂ : ℝ) ≤ ((⌊d * B⌋₊ + 1 : ℕ) : ℝ) := Nat.cast_le.2 (min_le_left _ _)
        push_cast at this
        linarith [Nat.floor_le (mul_nonneg hd0 hB.le)]
      have h3 : 2 < a * B - d * B + c * B := by
        have := (div_lt_iff₀ hB).1 hk
        linarith
      have hlt : ((m₂ : ℝ) - m₁) / B < a := by
        rw [div_lt_iff₀ hB]
        linarith
      refine (hlim.eventually (gt_mem_nhds hlt)).mono fun n hn => (visitFreq_mono ?_ n).trans_lt hn
      rintro y ⟨-, hy1⟩ ⟨hcy, hyd⟩
      constructor
      · calc (m₁ : ℝ) / B ≤ c := by
              rw [div_le_iff₀ hB]
              exact Nat.floor_le (mul_nonneg hc0 hB.le)
          _ ≤ y := hcy
      · rw [lt_div_iff₀ hB, hm₂def, Nat.cast_min, lt_min_iff]
        constructor
        · push_cast
          linarith [mul_le_mul_of_nonneg_right hyd hB.le, Nat.lt_floor_add_one (d * B)]
        · rw [hBnat]
          exact mul_lt_of_lt_one_left hB hy1
  · intro hud k m hm
    have hB : (0 : ℝ) < (b : ℝ) ^ k := by positivity
    have hc0 : 0 ≤ (m : ℝ) / (b : ℝ) ^ k := by positivity
    have hcd : (m : ℝ) / (b : ℝ) ^ k ≤ ((m : ℝ) + 1) / (b : ℝ) ^ k :=
      div_le_div_of_nonneg_right (by linarith) hB.le
    have hd1 := add_one_div_pow_le_one hm
    have h1 : Tendsto (visitFreq s (Set.Icc _ _)) atTop _ :=
      hud _ _ hcd (Set.Icc_subset_Icc hc0 hd1)
    have h2 : Tendsto (visitFreq s (Set.Icc _ _)) atTop _ :=
      hud _ _ le_rfl (Set.Icc_subset_Icc (hc0.trans hcd) hd1)
    have hsplit (n : ℕ) : visitFreq s (Set.Ico ((m : ℝ) / (b : ℝ) ^ k)
        (((m : ℝ) + 1) / (b : ℝ) ^ k)) n =
        visitFreq s (Set.Icc ((m : ℝ) / (b : ℝ) ^ k) (((m : ℝ) + 1) / (b : ℝ) ^ k)) n -
          visitFreq s (Set.Icc (((m : ℝ) + 1) / (b : ℝ) ^ k) (((m : ℝ) + 1) / (b : ℝ) ^ k)) n := by
      rw [eq_sub_iff_add_eq, ← visitFreq_union (Set.disjoint_left.2 fun y hy hy' =>
        lt_irrefl y (hy.2.trans_le hy'.1))]
      exact congrFun (visitFreq_congr (Set.Ico_union_Icc_eq_Icc hcd le_rfl)) n
    convert (h1.sub h2).congr fun n => (hsplit n).symm using 2
    ring

/-- Visits to `b`-adic intervals characterise density modulo one. -/
@[category API, AMS 11]
theorem exists_Ico_iff_dense {b : ℕ} (hb : 2 ≤ b) (s : ℕ → ℝ) :
    (∀ k, ∀ m < b ^ k, ∃ n, Int.fract (s n) ∈
      Set.Ico ((m : ℝ) / (b : ℝ) ^ k) (((m : ℝ) + 1) / (b : ℝ) ^ k)) ↔
    Dense (Set.range fun n => (s n : AddCircle (1 : ℝ))) := by
  have hb0 : 0 < b := by omega
  constructor
  · intro hE
    rw [dense_iff_inter_open]
    rintro U hU ⟨p, hp⟩
    obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective p
    have hpt : ((Int.fract q : ℝ) : AddCircle (1 : ℝ)) ∈ U := (coe_fract q).symm ▸ hp
    have hpre : IsOpen ((↑) ⁻¹' U : Set ℝ) := hU.preimage (AddCircle.continuous_mk' 1)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hpre _ hpt
    obtain ⟨k, hk⟩ := exists_one_div_pow_lt hb hε
    have hq := (digitPrefix_eq_iff hb0 k _ q).1 rfl
    obtain ⟨n, hn⟩ := hE k _ (digitPrefix_lt hb0 k q)
    refine ⟨_, ?_, n, rfl⟩
    have hw : ((digitPrefix b k q : ℝ) + 1) / (b : ℝ) ^ k - (digitPrefix b k q : ℝ) / (b : ℝ) ^ k =
        1 / (b : ℝ) ^ k := by ring
    have hmem : Int.fract (s n) ∈ Metric.ball (Int.fract q) ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hn.1, hn.2, hq.1, hq.2]
    simpa [coe_fract] using hball hmem
  · intro hd k m hm
    have hB : (0 : ℝ) < (b : ℝ) ^ k := by positivity
    have hc0 : 0 ≤ (m : ℝ) / (b : ℝ) ^ k := by positivity
    have hcd : (m : ℝ) / (b : ℝ) ^ k < ((m : ℝ) + 1) / (b : ℝ) ^ k :=
      div_lt_div_of_pos_right (by linarith) hB
    have hd1 := add_one_div_pow_le_one hm
    obtain ⟨_, ⟨n, rfl⟩, t, ht, hnt⟩ := hd.exists_mem_open
      (QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo) ((Set.nonempty_Ioo.2 hcd).image _)
    refine ⟨n, ?_⟩
    rw [← fract_eq_of_coe_eq hnt, Int.fract_eq_self.2 ⟨hc0.trans ht.1.le, ht.2.trans_le hd1⟩]
    exact ⟨ht.1.le, ht.2⟩

/-- A real number $\xi$ is normal in base $b$ if and only if $(b^n \xi)_{n \ge 0}$ is uniformly
distributed modulo $1$ [Wal49], [Bug12, Theorem 4.14]. -/
@[category research solved, AMS 11]
theorem isNormalInBase_iff_isEquidistributedModuloOne (b : ℕ) (hb : 2 ≤ b) (ξ : ℝ) :
    IsNormalInBase b ξ ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * ξ :=
  (isNormalInBase_iff_tendsto (by omega) ξ).trans (tendsto_Ico_iff_isEquidistributedModuloOne hb _)

/-- A real number $\xi$ is rich in base $b$ if and only if $(b^n \xi)_{n \ge 0}$ is dense
modulo $1$ [Bug12, Section 4.4]. -/
@[category textbook, AMS 11]
theorem isRichInBase_iff_dense (b : ℕ) (hb : 2 ≤ b) (ξ : ℝ) :
    IsRichInBase b ξ ↔ Dense (Set.range fun n => (↑((b : ℝ) ^ n * ξ) : AddCircle (1 : ℝ))) :=
  (isRichInBase_iff_exists (by omega) ξ).trans (exists_Ico_iff_dense hb _)

end BugeaudNormalAndRich
