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
# Green's Open Problem 13

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.13)
- [Go20] Gowers, W. T. "A uniform set with fewer than expected arithmetic progressions of
  length 4." Acta Mathematica Hungarica 161.2 (2020): 756-767.
- [DTZ25] Deng, Mingyang, Jonathan Tidor, and Yufei Zhao. "Uniform sets with few progressions
  via colourings." Mathematical Proceedings of the Cambridge Philosophical Society 179.1 (2025):
  79-103. [arXiv:2307.06914](https://arxiv.org/abs/2307.06914)
- [ShDo26] Shi, Ruizhe, and Yiqi Dong. "An improved upper bound for colorings without
  symmetrically colored $k$-term arithmetic progressions." (2026).
  [arXiv:2607.20752](https://arxiv.org/abs/2607.20752)
-/

@[expose] public section

open Finset

namespace Green13

/--
The number of pairs $(n, d) \in (\mathbb{Z}/N\mathbb{Z})^2$ with $n, n + d, n + 2d, n + 3d \in A$.
This is $N^2 \Lambda_4(1_A)$ in the notation of [DTZ25]: progressions with $d = 0$ are counted,
and each nontrivial progression is counted twice (forwards and backwards).
-/
def fourAPCount {N : ℕ} [NeZero N] (A : Finset (ZMod N)) : ℕ :=
  #{p : ZMod N × ZMod N | p.1 ∈ A ∧ p.1 + p.2 ∈ A ∧ p.1 + 2 * p.2 ∈ A ∧ p.1 + 3 * p.2 ∈ A}

/--
A set $A \subseteq \mathbb{Z}/N\mathbb{Z}$ is `η`-Fourier uniform if every nontrivial Fourier
coefficient of $1_A$ has modulus at most $\eta N$, that is
$\left|\sum_{x \in A} e(rx/N)\right| \leq \eta N$ for all $r \neq 0$. For $r \neq 0$ these are
also the Fourier coefficients of $1_A - \alpha$.
-/
def IsFourierUniform {N : ℕ} [NeZero N] (η : ℝ) (A : Finset (ZMod N)) : Prop :=
  ∀ r : ZMod N, r ≠ 0 → ‖∑ x ∈ A, ZMod.stdAddChar (r * x)‖ ≤ η * N

/--
There is an absolute constant $c > 0$ such that, for every $\alpha \in (0, 1]$, every
sufficiently Fourier-uniform set $A \subseteq \mathbb{Z}/N\mathbb{Z}$ with $|A| \geq \alpha N$
and $N$ large contains at least $c \alpha^C N^2$ 4-term arithmetic progressions.

The quantifiers follow Gowers's conjecture as stated in [DTZ25, Conjecture 1.1]: the uniformity
parameter `η` and the threshold `N₀` may depend on `α`, the constant `c` may not.
-/
def ManyFourAPs (C : ℝ) : Prop :=
  ∃ c > (0 : ℝ), ∀ α : ℝ, 0 < α → α ≤ 1 → ∃ η > (0 : ℝ), ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N], ∀ A : Finset (ZMod N),
      α * N ≤ #A → IsFourierUniform η A → c * α ^ C * (N : ℝ) ^ 2 ≤ fourAPCount A

/--
Suppose that $A \subset \mathbb{Z}/N\mathbb{Z}$ has density $\alpha$ and is Fourier uniform (that
is, all Fourier coefficients of $1_A - \alpha$ are $o(N)$). Does $A$ contain at least
$\gg \alpha^{100} N^2$ 4-term arithmetic progressions?

At most $4N$ pairs $(n, d)$ have $d = 0$, $2d = 0$ or $3d = 0$ in $\mathbb{Z}/N\mathbb{Z}$, so
counting these degenerate progressions does not change the answer.
The answer is no for every exponent below $5$ (`green_13.variants.shi_dong`).
-/
@[category research open, question, AMS 5 11]
theorem green_13 : ManyFourAPs 100 := by
  sorry

/--
The exponent $100$ stands for some absolute constant: Gowers [Go20] states the same question,
due to Ruzsa, with $\alpha^{1000}$ and writes that "1000" is "just an informal way of referring to
some absolute constant". Deng, Tidor and Zhao conjecture that no exponent works
[DTZ25, Conjecture 1.4].
-/
@[category research open, question, AMS 5 11]
theorem green_13.variants.some_exponent : ∃ C : ℝ, ManyFourAPs C := by
  sorry

/--
Deng, Tidor and Zhao [DTZ25, Corollary 1.9] show that the minimum 4-AP density of a
Fourier-uniform set of density $\alpha$ is $O(\alpha^{3 + \frac{1}{2}\log_3 22})$, where
$3 + \frac{1}{2}\log_3 22 \approx 4.406$. Gowers's construction [Go20], with a tensor power trick,
gives the exponent $4 + c$ with $c \approx 2 \times 10^{-8}$ [DTZ25, Section 1.1]. So the statement
fails for every exponent below $3 + \frac{1}{2}\log_3 22$.
-/
@[category research solved, AMS 5 11]
theorem green_13.variants.deng_tidor_zhao :
    ∀ C : ℝ, C < 3 + Real.logb 3 22 / 2 → ¬ ManyFourAPs C := by
  sorry

/--
Shi and Dong [ShDo26] improve the bound of [DTZ25] to $O_\varepsilon(\alpha^{5 - \varepsilon})$
for every $\varepsilon > 0$, so the statement fails for every exponent below $5$.
-/
@[category research solved, AMS 5 11]
theorem green_13.variants.shi_dong : ∀ C : ℝ, C < 5 → ¬ ManyFourAPs C := by
  sorry

/--
A colouring `χ` of $\{1, \dots, N\}$ has no symmetrically coloured 4-term arithmetic progression
if there are no $n, d \geq 1$ with $n + 3d \leq N$, $\chi(n) = \chi(n + 3d)$ and
$\chi(n + d) = \chi(n + 2d)$ [DTZ25].
-/
def NoSymmetricFourAP {k : ℕ} (N : ℕ) (χ : ℕ → Fin k) : Prop :=
  ∀ n d : ℕ, 1 ≤ n → 1 ≤ d → n + 3 * d ≤ N →
    ¬ (χ n = χ (n + 3 * d) ∧ χ (n + d) = χ (n + 2 * d))

/--
For all $N$, there exists an $N^{o(1)}$-colouring of $\{1, \dots, N\}$ without symmetrically
coloured 4-term arithmetic progressions [DTZ25, Conjecture 1.6].
-/
def SymmetricColouringConjecture : Prop :=
  ∀ ε > (0 : ℝ), ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∃ k : ℕ, (k : ℝ) ≤ (N : ℝ) ^ ε ∧ ∃ χ : ℕ → Fin k, NoSymmetricFourAP N χ

/-- [DTZ25, Conjecture 1.6]. If true, the answer to Green's question is no
(`green_13.variants.of_symmetricColouringConjecture`). -/
@[category research open, AMS 5 11]
theorem green_13.variants.symmetricColouringConjecture : SymmetricColouringConjecture := by
  sorry

/--
[DTZ25, Theorem 1.7]: the colouring conjecture implies Ruzsa's question [DTZ25, Conjecture 1.4],
that the minimum 4-AP density of a Fourier-uniform set of density $\alpha$ is less than
$\alpha^C$ for every $C$ and all sufficiently small $\alpha$. In particular the statement then
fails for every exponent.
-/
@[category research solved, AMS 5 11]
theorem green_13.variants.of_symmetricColouringConjecture :
    SymmetricColouringConjecture → ∀ C : ℝ, ¬ ManyFourAPs C := by
  sorry

/-- A larger exponent gives a weaker statement, since $\alpha \leq 1$. -/
@[category test, AMS 5 11]
theorem manyFourAPs_mono {C C' : ℝ} (hC : C ≤ C') (h : ManyFourAPs C) : ManyFourAPs C' := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c, hc, fun α hα hα1 => ?_⟩
  obtain ⟨η, hη, N₀, h⟩ := h α hα hα1
  refine ⟨η, hη, N₀, fun N hN _ A hA hU => le_trans ?_ (h N hN A hA hU)⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hα hα1 hC) hc.le) (by positivity)

/-- The whole group is perfectly Fourier uniform: every nontrivial character sums to zero. -/
@[category test, AMS 5 11]
theorem isFourierUniform_univ (N : ℕ) [NeZero N] :
    IsFourierUniform 0 (univ : Finset (ZMod N)) := by
  intro r hr
  have h := AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N hr)
  simp only [AddChar.mulShift_apply] at h
  simp [h]

/-- The whole group $\mathbb{Z}/N\mathbb{Z}$ has $N^2$ pairs $(n, d)$. -/
@[category test, AMS 5 11]
theorem fourAPCount_univ (N : ℕ) [NeZero N] : fourAPCount (univ : Finset (ZMod N)) = N ^ 2 := by
  simp [fourAPCount, sq]

/-- In $\{0, 1, 2, 3\} \subseteq \mathbb{Z}/7\mathbb{Z}$ the progressions are the $4$ trivial
ones and $0, 1, 2, 3$ in both directions. -/
@[category test, AMS 5 11]
theorem fourAPCount_range_four : fourAPCount ({0, 1, 2, 3} : Finset (ZMod 7)) = 6 := by
  decide

/-- $\{0, 1, 2, 4\} \subseteq \mathbb{Z}/6\mathbb{Z}$ contains no progression with four distinct
terms. Besides the $4$ pairs with $d = 0$ it has $8$ degenerate ones, with $2d = 0$ or $3d = 0$. -/
@[category test, AMS 5 11]
theorem fourAPCount_degenerate_six : fourAPCount ({0, 1, 2, 4} : Finset (ZMod 6)) = 12 := by
  decide

/-- A single point is not $0$-uniform: its Fourier coefficient at $r = 1$ has modulus $1$. -/
@[category test, AMS 5 11]
theorem not_isFourierUniform_zero_singleton : ¬ IsFourierUniform 0 ({0} : Finset (ZMod 2)) := by
  intro h
  have := h 1 (by decide)
  norm_num at this

/-- An injective colouring has no symmetrically coloured 4-term progression. -/
@[category test, AMS 5 11]
theorem noSymmetricFourAP_of_injective (N : ℕ) (χ : ℕ → Fin (N + 1))
    (hχ : Function.Injective χ) : NoSymmetricFourAP N χ := by
  intro n d _ hd _ h
  have := hχ h.1
  omega

/-- A constant colouring of $\{1, 2, 3, 4\}$ colours $1, 2, 3, 4$ symmetrically. -/
@[category test, AMS 5 11]
theorem not_noSymmetricFourAP_const : ¬ NoSymmetricFourAP 4 (fun _ => (0 : Fin 1)) :=
  fun h => h 1 1 le_rfl le_rfl (by norm_num) ⟨rfl, rfl⟩

/-- The 3-colouring $1333221232131211333233$ of $\mathbb{Z}/22\mathbb{Z}$ given after
[DTZ25, Theorem 1.8], with colours $1, 2, 3$ written as $0, 1, 2$ and read on $\mathbb{N}$
modulo $22$. -/
def dtzColouring (n : ℕ) : Fin 3 :=
  (![0, 2, 2, 2, 1, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 0, 2, 2, 2, 1, 2, 2] : Fin 22 → Fin 3)
    ⟨n % 22, Nat.mod_lt _ (by norm_num)⟩

/-- The colouring given after [DTZ25, Theorem 1.8] has no symmetrically coloured 4-term
progression in $\{1, \dots, 22\}$. -/
@[category test, AMS 5 11]
theorem noSymmetricFourAP_dtzColouring : NoSymmetricFourAP 22 dtzColouring := by
  have key : ∀ n ∈ range 23, ∀ d ∈ range 8, 1 ≤ n → 1 ≤ d → n + 3 * d ≤ 22 →
      ¬ (dtzColouring n = dtzColouring (n + 3 * d) ∧
        dtzColouring (n + d) = dtzColouring (n + 2 * d)) := by
    decide
  intro n d hn hd hN
  exact key n (mem_range.2 (by omega)) d (mem_range.2 (by omega)) hn hd hN

/-- With $N$ colours, $n \mapsto n \bmod N$ works for every $N \geq 1$, so the condition in
`SymmetricColouringConjecture` holds for every $\varepsilon \geq 1$. -/
@[category test, AMS 5 11]
theorem symmetricColouring_of_one_le {ε : ℝ} (hε : 1 ≤ ε) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∃ k : ℕ, (k : ℝ) ≤ (N : ℝ) ^ ε ∧ ∃ χ : ℕ → Fin k, NoSymmetricFourAP N χ := by
  refine ⟨1, fun N hN => ⟨N, ?_, fun n => ⟨n % N, Nat.mod_lt _ (by omega)⟩, ?_⟩⟩
  · simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN : (1 : ℝ) ≤ N) hε
  · intro n d hn hd hnd h
    have h1 : n % N = (n + 3 * d) % N := congrArg Fin.val h.1
    rw [Nat.mod_eq_of_lt (by omega : n < N)] at h1
    rcases Nat.lt_or_ge (n + 3 * d) N with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at h1
      omega
    · rw [show n + 3 * d = N by omega, Nat.mod_self] at h1
      omega

end Green13
