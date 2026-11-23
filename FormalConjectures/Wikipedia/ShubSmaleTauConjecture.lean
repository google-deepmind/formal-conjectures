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
# The Shub–Smale $\tau$-conjecture

Proposed by Shub and Smale [SS95] and listed as the 4th problem in Smale's problems for the
twenty-first century [Sm98], the $\tau$-conjecture concerns a nonzero polynomial
$f \in \mathbb{Z}[X]$ and its division-free straight-line program complexity $\tau(f)$: the
smallest number of ring operations ($+$, $-$, $\times$) needed to construct $f$ starting from
$1$ and $X$. Shub and Smale conjectured the existence of an absolute constant $c \in \mathbb{N}$
such that every nonzero $f \in \mathbb{Z}[X]$ has at most $(1 + \tau(f))^c$ distinct integer
roots. A proof would imply $\mathrm{P}_{\mathbb{C}} \neq \mathrm{NP}_{\mathbb{C}}$ in the
Blum–Shub–Smale model [SS95, Bu00].

*References:*
- [Wikipedia: Smale's problems](https://en.wikipedia.org/wiki/Smale%27s_problems)
- [SS95] M. Shub and S. Smale, *On the intractability of Hilbert's Nullstellensatz and an
  algebraic version of "NP $\neq$ P?"*, Duke Math. J. **81** (1995), no. 1, 47–54.
- [Sm98] S. Smale, *Mathematical problems for the next century*, Math. Intelligencer **20**
  (1998), no. 2, 7–15.
- [Bu00] P. Bürgisser, *Completeness and Reduction in Algebraic Complexity Theory*, Algorithms
  and Computation in Mathematics **7**, Springer, 2000, p. 141.
-/

@[expose] public section

namespace ShubSmaleTauConjecture

/-- Inductive relation `SLPBuilds k ctx` asserting that the context list `ctx` of integer
polynomials is obtained in `k` division-free arithmetic steps (`+`, `-`, `*`) from `[1, X]`. -/
inductive SLPBuilds : ℕ → List (Polynomial ℤ) → Prop
  | init : SLPBuilds 0 [1, Polynomial.X]
  | add {k ctx p q} : SLPBuilds k ctx → p ∈ ctx → q ∈ ctx → SLPBuilds (k + 1) ((p + q) :: ctx)
  | sub {k ctx p q} : SLPBuilds k ctx → p ∈ ctx → q ∈ ctx → SLPBuilds (k + 1) ((p - q) :: ctx)
  | mul {k ctx p q} : SLPBuilds k ctx → p ∈ ctx → q ∈ ctx → SLPBuilds (k + 1) ((p * q) :: ctx)

/-- Every context produced by `SLPBuilds` contains $1$. -/
@[category API, AMS 12 68]
theorem slpBuilds_one_mem {k : ℕ} {ctx : List (Polynomial ℤ)} (hb : SLPBuilds k ctx) :
    (1 : Polynomial ℤ) ∈ ctx := by
  induction hb with
  | init => simp
  | add _ _ _ ih | sub _ _ _ ih | mul _ _ _ ih => exact List.mem_cons_of_mem _ ih

/-- Every context produced by `SLPBuilds` contains $X$. -/
@[category API, AMS 12 68]
theorem slpBuilds_X_mem {k : ℕ} {ctx : List (Polynomial ℤ)} (hb : SLPBuilds k ctx) :
    Polynomial.X ∈ ctx := by
  induction hb with
  | init => simp
  | add _ _ _ ih | sub _ _ _ ih | mul _ _ _ ih => exact List.mem_cons_of_mem _ ih

/-- Any two `SLPBuilds` derivations can be replayed into a single combined context containing
both lists of polynomials. -/
@[category API, AMS 12 68]
theorem slpBuilds_merge {k₁ k₂ : ℕ} {ctx₁ ctx₂ : List (Polynomial ℤ)}
    (hb₁ : SLPBuilds k₁ ctx₁) (hb₂ : SLPBuilds k₂ ctx₂) :
    ∃ k₃ ctx₃, SLPBuilds k₃ ctx₃ ∧ (∀ g ∈ ctx₁, g ∈ ctx₃) ∧ (∀ g ∈ ctx₂, g ∈ ctx₃) := by
  induction hb₂ with
  | init =>
    refine ⟨k₁, ctx₁, hb₁, fun _ hg => hg, fun g hg => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact slpBuilds_one_mem hb₁
    · exact slpBuilds_X_mem hb₁
  | add _ hp₂ hq₂ ih =>
    rcases ih with ⟨k₃, ctx₃, hb₃, hsub₁, hsub₂⟩
    refine ⟨k₃ + 1, (_ + _) :: ctx₃, SLPBuilds.add hb₃ (hsub₂ _ hp₂) (hsub₂ _ hq₂),
      fun g hg => List.mem_cons_of_mem _ (hsub₁ g hg), fun g hg => ?_⟩
    rcases List.mem_cons.mp hg with rfl | hg'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hsub₂ g hg')
  | sub _ hp₂ hq₂ ih =>
    rcases ih with ⟨k₃, ctx₃, hb₃, hsub₁, hsub₂⟩
    refine ⟨k₃ + 1, (_ - _) :: ctx₃, SLPBuilds.sub hb₃ (hsub₂ _ hp₂) (hsub₂ _ hq₂),
      fun g hg => List.mem_cons_of_mem _ (hsub₁ g hg), fun g hg => ?_⟩
    rcases List.mem_cons.mp hg with rfl | hg'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hsub₂ g hg')
  | mul _ hp₂ hq₂ ih =>
    rcases ih with ⟨k₃, ctx₃, hb₃, hsub₁, hsub₂⟩
    refine ⟨k₃ + 1, (_ * _) :: ctx₃, SLPBuilds.mul hb₃ (hsub₂ _ hp₂) (hsub₂ _ hq₂),
      fun g hg => List.mem_cons_of_mem _ (hsub₁ g hg), fun g hg => ?_⟩
    rcases List.mem_cons.mp hg with rfl | hg'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hsub₂ g hg')

/-- Every power $X^n$ ($n \in \mathbb{N}$) can be built by `SLPBuilds`. -/
@[category API, AMS 12 68]
theorem slpBuilds_X_pow (n : ℕ) :
    ∃ k ctx, SLPBuilds k ctx ∧ Polynomial.X ^ n ∈ ctx := by
  induction n with
  | zero => exact ⟨0, [1, Polynomial.X], SLPBuilds.init, by simp⟩
  | succ d ih =>
    rcases ih with ⟨k, ctx, hb, hXd⟩
    have hmul := SLPBuilds.mul hb hXd (slpBuilds_X_mem hb)
    rw [← pow_succ] at hmul
    exact ⟨k + 1, (Polynomial.X ^ (d + 1)) :: ctx, hmul, List.mem_cons_self⟩

/-- Every natural constant polynomial $(m : \mathbb{Z}[X])$ can be built by `SLPBuilds`. -/
@[category API, AMS 12 68]
theorem slpBuilds_natCast (m : ℕ) :
    ∃ k ctx, SLPBuilds k ctx ∧ (m : Polynomial ℤ) ∈ ctx := by
  induction m with
  | zero =>
    exact ⟨1, ((1 : Polynomial ℤ) - 1) :: [1, Polynomial.X],
      SLPBuilds.sub SLPBuilds.init (by simp) (by simp), by simp⟩
  | succ j ih =>
    rcases ih with ⟨kj, ctxj, hbj, hj⟩
    exact ⟨kj + 1, ((j : Polynomial ℤ) + 1) :: ctxj,
      SLPBuilds.add hbj hj (slpBuilds_one_mem hbj), by simp⟩

/-- Every polynomial $f \in \mathbb{Z}[X]$ can be built in finitely many steps from $1$ and $X$. -/
@[category API, AMS 12 68]
theorem exists_slpBuilds (f : Polynomial ℤ) :
    ∃ k : ℕ, ∃ ctx : List (Polynomial ℤ), SLPBuilds k ctx ∧ f ∈ ctx := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rcases hp with ⟨_, _, hbp, hmp⟩
    rcases hq with ⟨_, _, hbq, hmq⟩
    rcases slpBuilds_merge hbp hbq with ⟨k₃, ctx₃, hb₃, hsubp, hsubq⟩
    exact ⟨k₃ + 1, (p + q) :: ctx₃, SLPBuilds.add hb₃ (hsubp p hmp) (hsubq q hmq),
      List.mem_cons_self⟩
  | monomial n a =>
    rcases slpBuilds_X_pow n with ⟨_, _, hbn, hXn⟩
    rcases Int.eq_nat_or_neg a with ⟨m, rfl | rfl⟩
    · rcases slpBuilds_natCast m with ⟨_, _, hbm, hm⟩
      rcases slpBuilds_merge hbn hbm with ⟨k₃, ctx₃, hb₃, hsubn, hsubm⟩
      refine ⟨k₃ + 1, ((m : Polynomial ℤ) * Polynomial.X ^ n) :: ctx₃,
        SLPBuilds.mul hb₃ (hsubm _ hm) (hsubn _ hXn), ?_⟩
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_natCast]
      exact List.mem_cons_self
    · rcases slpBuilds_natCast m with ⟨_, _, hbm, hm⟩
      rcases slpBuilds_merge hbn hbm with ⟨k₃, ctx₃, hb₃, hsubn, hsubm⟩
      have h1 := slpBuilds_one_mem hb₃
      have hb0 := SLPBuilds.sub hb₃ h1 h1
      have hbneg := SLPBuilds.sub hb0 List.mem_cons_self
        (List.mem_cons_of_mem _ (hsubm _ hm))
      have hbmul := SLPBuilds.mul hbneg List.mem_cons_self
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hsubn _ hXn)))
      refine ⟨k₃ + 3, _, hbmul, ?_⟩
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp

open scoped Classical in
/-- Straight-line program complexity $\tau(f)$: the minimum number of arithmetic steps needed to
construct $f \in \mathbb{Z}[X]$ from $1$ and $X$. -/
noncomputable def tauComplexity (f : Polynomial ℤ) : ℕ :=
  Nat.find (exists_slpBuilds f)

/-- For a nonzero polynomial $f \in \mathbb{Z}[X]$, `f.roots.toFinset` consists precisely of the
integer roots of $f$ without multiplicity. -/
@[category API, AMS 12 68]
theorem mem_roots_toFinset_iff {f : Polynomial ℤ} (hf : f ≠ 0) (x : ℤ) :
    x ∈ f.roots.toFinset ↔ f.IsRoot x := by
  simp [hf]

/-- Verifies $\tau(1) = 0$ since $1$ belongs to the initial context $[1, X]$. -/
@[category test, AMS 12 68]
theorem tauComplexity_one : tauComplexity 1 = 0 := by
  classical
  unfold tauComplexity
  rw [Nat.find_eq_zero]
  exact ⟨[1, Polynomial.X], SLPBuilds.init, by simp⟩

/-- Verifies $\tau(X) = 0$ since $X$ belongs to the initial context $[1, X]$. -/
@[category test, AMS 12 68]
theorem tauComplexity_X : tauComplexity Polynomial.X = 0 := by
  classical
  unfold tauComplexity
  rw [Nat.find_eq_zero]
  exact ⟨[1, Polynomial.X], SLPBuilds.init, by simp⟩

/-- Verifies $\tau(X + 1) = 1$: one addition builds $X + 1$ from $[1, X]$, and $X + 1$ does not
belong to $[1, X]$. -/
@[category test, AMS 12 68]
theorem tauComplexity_X_add_one : tauComplexity (Polynomial.X + 1) = 1 := by
  classical
  have hle : tauComplexity (Polynomial.X + 1) ≤ 1 := by
    unfold tauComplexity
    exact Nat.find_le ⟨(Polynomial.X + 1) :: [1, Polynomial.X],
      SLPBuilds.add SLPBuilds.init (by simp) (by simp), List.mem_cons_self⟩
  have hne : tauComplexity (Polynomial.X + 1) ≠ 0 := by
    intro h0
    unfold tauComplexity at h0
    rw [Nat.find_eq_zero] at h0
    rcases h0 with ⟨_, hb, hmem⟩
    cases hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h1 | hX
    · have hev := congr_arg (Polynomial.eval (1 : ℤ)) h1
      norm_num at hev
    · have hev := congr_arg (Polynomial.eval (0 : ℤ)) hX
      norm_num at hev
  omega

/-- **Shub–Smale $\tau$-conjecture** [SS95, Bu00]: there exists a universal constant
$c \in \mathbb{N}$ such that every nonzero polynomial $f \in \mathbb{Z}[X]$ has at most
$(1 + \tau(f))^c$ distinct integer roots. Following [SS95] and [Bu00, p. 141], we count distinct
integer roots (since $(X - 1)^{2^k}$ has root multiplicity $2^k$ with $\tau \le k + 1$) and write
$(1 + \tau(f))^c$ rather than Wikipedia's shorthand $\tau(f)^c$ so that $\tau(X) = 0$ is
included. -/
@[category research open, AMS 12 68]
theorem shub_smale_tau_conjecture :
    ∃ c : ℕ, ∀ f : Polynomial ℤ, f ≠ 0 →
      f.roots.toFinset.card ≤ (1 + tauComplexity f) ^ c := by
  sorry

end ShubSmaleTauConjecture
