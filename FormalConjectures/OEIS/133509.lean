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
# Exponents with a unique positive decimal digit-sum fixed point

Let $s_{10}(n)$ denote the sum of the base-$10$ digits of $n$. Sequence `A133509` defines the set
of nonnegative exponents $k$ for which $m = 1$ is the only positive integer satisfying
$s_{10}(m^k) = m$ and lists its initial terms $0, 105, 164, 186, \dots$ (with OEIS keywords
`nonn,base`, without `fini`). Companion entry `A046471(k)` counts nontrivial fixed points $m > 1$
for $k \ge 1$ (so $k \in \text{A133509} \iff \text{A046471}(k) = 0$ for $k \ge 1$), while
`A046000(k)` records the largest positive fixed point of $m \mapsto s_{10}(m^k)$, for which
M. F. Hasler (June 12, 2026) conjectured the upper bound
$m < (5 + 2.7 \log(k + 1))(k + 1)$.

The infinitude question `infinite_exponents` below is not stated in `A133509` itself; it is posed
here as a new open question motivated by `A133509` (and its shifted analogue studied in
[Liu, *Digit Sums of Powers*](https://github.com/LiuChang-ao/digit-sum-powers-formal)).

*References:*
- [A133509](https://oeis.org/A133509)
- [A046471](https://oeis.org/A046471)
- [A046000](https://oeis.org/A046000)
-/

@[expose] public section

namespace OeisA133509

/-- The set of nonnegative exponents $k$ in `A133509`, for which $m = 1$ is the unique positive
solution to $s_{10}(m^k) = m$. -/
def exponents : Set ℕ :=
  {k | ∀ m : ℕ, 0 < m → (Nat.digits 10 (m ^ k)).sum = m → m = 1}

/-- The set of nontrivial fixed points $m > 1$ satisfying $s_{10}(m^k) = m$, counted at $k \ge 1$
by `A046471`. -/
def nontrivialRoots (k : ℕ) : Set ℕ :=
  {m | 1 < m ∧ (Nat.digits 10 (m ^ k)).sum = m}

@[category API, AMS 11]
theorem mem_iff_roots_empty (k : ℕ) : k ∈ exponents ↔ nontrivialRoots k = ∅ := by
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro m ⟨hm, he⟩
    have := h m (by omega) he
    omega
  · intro h m hm he
    by_contra! hn
    have hmem : m ∈ nontrivialRoots k := ⟨by omega, he⟩
    rw [h] at hmem
    exact hmem

@[category test, AMS 11]
theorem zero_mem : 0 ∈ exponents := by
  intro m _ h
  have e : (Nat.digits 10 1).sum = 1 := by decide
  simpa only [pow_zero, e] using h.symm

@[category test, AMS 11]
theorem one_notMem : 1 ∉ exponents := by
  intro h
  have := h 2 (by decide) (by decide)
  omega

/-- `A133509` equivalently lists the exponents $k$ at which `A046000(k)` equals $1$. -/
@[category API, AMS 11]
theorem mem_iff_one_greatest (k : ℕ) :
    k ∈ exponents ↔ IsGreatest {m : ℕ | 0 < m ∧ (Nat.digits 10 (m ^ k)).sum = m} 1 := by
  constructor
  · intro h
    refine ⟨⟨by decide, by simp only [one_pow]; decide⟩, ?_⟩
    intro m hm
    exact (h m hm.1 hm.2).le
  · intro h m hm he
    have := h.2 (show m ∈ {x : ℕ | 0 < x ∧ (Nat.digits 10 (x ^ k)).sum = x} from ⟨hm, he⟩)
    omega

/-- Open question motivated by `A133509` (not stated in the OEIS entry itself): are there
infinitely many exponents $k$ for which $m = 1$ is the only positive solution to
$s_{10}(m^k) = m$? -/
@[category research open, question, AMS 11]
theorem infinite_exponents : exponents.Infinite := by
  sorry

/-- Hasler's proposed upper bound in the `A046000` comments, stated for every positive fixed point
$s_{10}(m^k) = m$ (where $\log$ denotes the natural logarithm). -/
@[category research open, AMS 11]
theorem hasler_upper_bound (k m : ℕ) (hm : 0 < m) (h : (Nat.digits 10 (m ^ k)).sum = m) :
    (m : ℝ) < (5 + (27 / 10 : ℝ) * Real.log ((k : ℝ) + 1)) * ((k : ℝ) + 1) := by
  sorry

end OeisA133509
