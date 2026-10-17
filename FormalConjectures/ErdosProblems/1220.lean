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
# Erdős Problem 1220

*References:*
- [erdosproblems.com/1220](https://www.erdosproblems.com/1220)
- [ErHa71] Erdős, Paul and Hajnal, András, Unsolved problems in set theory. Axiomatic Set
  Theory, Proc. Sympos. Pure Math. XIII Part I (1971), 17-48.
- [Ko25b] Komjáth, Péter, The Erdős–Hajnal problem list. Bull. Symb. Log. (2025), 418-461.
- [ShSt87] Shelah, Saharon and Stanley, Lee J., A theorem and some consistency results in
  partition calculus. Ann. Pure Appl. Logic 36 (1987), 119-152.
- [PALOMAR-2026-09-26-000001](https://palomar-registry.org/entry?id=PALOMAR-2026-09-26-000001&version=1):
  a Lean 4 proof, checked by Comparator and registered with the Palomar registry, that the
  affirmative answer to this problem is not provable in ZFC
  ([source](https://github.com/jbaelaw/erdos1220-lean/tree/9cb81ffa48ffb766127c7e485ccef77bd4160868)).
-/

@[expose] public section

open Cardinal Order Combinatorics

namespace Erdos1220

universe u

/--
Let $\lambda$ be a singular cardinal such that both $\lambda$ and $\mathrm{cf}(\lambda)$ are
$\aleph_0$-inaccessible. Does $\lambda \to (\lambda, \aleph_1)^2$ hold?

A cardinal $\kappa$ is $\aleph_0$-inaccessible if $\mu^{\aleph_0} < \kappa$ for every cardinal
$\mu < \kappa$. In the partition relation, colour $0$ asks for a homogeneous set of size
$\lambda$ and colour $1$ asks for one of size $\aleph_1$.

A problem of Erdős, Hajnal, and Rado [ErHa71], who note that the answer is positive under GCH.
The affirmative answer is not provable in ZFC: [PALOMAR-2026-09-26-000001] is a Lean 4 proof,
adapting the forcing of [ShSt87, §3], that some model of ZFC contains such a $\lambda$ with
$\lambda \not\to (\lambda, \aleph_1)^2$.
-/
@[category research open, AMS 3 5]
theorem erdos_1220 : answer(sorry) ↔
    ∀ lam : Cardinal.{u}, lam.IsSingular →
      (∀ μ < lam, μ ^ ℵ₀ < lam) → (∀ μ < lam.ord.cof, μ ^ ℵ₀ < lam.ord.cof) →
      cardinalPartitionRel lam 2 2 (fun i => if (i : Ordinal) = 0 then lam else ℵ_ 1) := by
  sorry

/--
The hypotheses of `erdos_1220` can be satisfied: $\beth_{\mathfrak{c}^+}$ is a singular strong
limit cardinal of cofinality $\mathfrak{c}^+$, so it and its cofinality are
$\aleph_0$-inaccessible.
-/
@[category test, AMS 3]
theorem erdos_1220.test.hypotheses_satisfiable :
    ∃ lam : Cardinal.{u}, lam.IsSingular ∧ (∀ μ < lam, μ ^ ℵ₀ < lam) ∧
      ∀ μ < lam.ord.cof, μ ^ ℵ₀ < lam.ord.cof := by
  have hc : ℵ₀ ≤ succ 𝔠 := aleph0_le_continuum.trans (le_succ _)
  have hlim : IsSuccLimit (succ 𝔠 : Cardinal.{u}).ord := isSuccLimit_ord hc
  have hlam : (ℶ_ (succ 𝔠 : Cardinal.{u}).ord).IsStrongLimit :=
    isStrongLimit_beth.mpr hlim.isSuccPrelimit
  have hlt : succ 𝔠 < ℶ_ (succ 𝔠 : Cardinal.{u}).ord :=
    (le_beth_ord _).lt_of_ne (hlam.isSuccLimit.succ_ne _)
  have hnormal : Order.IsNormal fun o : Ordinal.{u} ↦ (ℶ_ o).ord := by
    rw [Order.isNormal_iff]
    refine ⟨ord_strictMono.comp beth_strictMono, fun o ho a ha ↦ ?_⟩
    exact ord_le.mpr ((isNormal_beth.le_iff_forall_le ho).mpr fun b hb ↦ ord_le.mp (ha b hb))
  have hcof : (ℶ_ (succ 𝔠 : Cardinal.{u}).ord).ord.cof = succ 𝔠 := by
    rw [Ordinal.cof_map_of_isNormal hnormal hlim]
    exact (isRegular_succ aleph0_le_continuum).cof_ord
  refine ⟨ℶ_ (succ 𝔠 : Cardinal.{u}).ord, ⟨aleph0_le_beth _, ?_⟩, fun μ hμ ↦ ?_, ?_⟩
  · rw [hcof]
    exact hlt.ne
  · have hν : max μ ℵ₀ < ℶ_ (succ 𝔠 : Cardinal.{u}).ord := max_lt hμ (hc.trans_lt hlt)
    have h0 : max μ ℵ₀ ≠ 0 := (aleph0_pos.trans_le (le_max_right _ _)).ne'
    calc μ ^ ℵ₀ ≤ max μ ℵ₀ ^ max μ ℵ₀ :=
          (power_le_power_right (le_max_left _ _)).trans
            (power_le_power_left h0 (le_max_right _ _))
      _ = 2 ^ max μ ℵ₀ := power_self_eq (le_max_right _ _)
      _ < _ := hlam.isStrongPrelimit hν
  · rw [hcof]
    intro μ hμ
    calc μ ^ ℵ₀ ≤ 𝔠 ^ ℵ₀ := power_le_power_right (le_of_lt_succ hμ)
      _ = 𝔠 := continuum_power_aleph0
      _ < succ 𝔠 := lt_succ _

end Erdos1220
