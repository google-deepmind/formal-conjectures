/-
Copyright 2025 The Formal Conjectures Authors.

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
# Gauss circle problem

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Gauss_circle_problem)
-/

open Filter

open scoped EuclideanGeometry Real Topology

/-  # Gauss Circle Problem

Consider a circle in $\mathbb{R}^2$ with center at the origin and radius $r\geq 0$.
Gauss's circle problem asks how many points there are inside this circle of the form
$(m, n)$ where $m$ and $n$ are both integers. Equivalently, how many pairs of integers
$m$ and $n$ are there such that
$$
  m^2 + n^2 \leq r^2.
$$
-/

namespace GaussCircleProblem

/--
Let $N(r)$ be the number of points $(m, n)$ within a circle of radius $r$,
where $m$ and $n$ are both integers.
-/
noncomputable abbrev N (r : ℝ) : ℕ :=
  { (m, n) : ℤ × ℤ | !₂[↑m, ↑n] ∈ Metric.closedBall (0 : ℝ²) r }.ncard

/--
Let $E(r)$ be the error term between the number of integral points inside the circle and the
area of the circle; that is $N(r) = \pi r^2 + E(r)$.
-/
noncomputable abbrev E (r : ℝ) : ℝ := N r - π * r ^ 2

/--
Gauss proved that
$$
  |E(r)|\leq 2\sqrt{2}\pi r,
$$
for sufficiently large $r$.

[Ha59]  Hardy, G. H. (1959). _Ramanujan: Twelve Lectures on Subjects Suggested by His Life and Work_(3rd ed.). New York: Chelsea Publishing Company. p. 67
-/
@[category research solved, AMS 11]
theorem error_le : ∀ᶠ r in atTop, |E r| ≤ 2 * √2 * π * r := by
  push_cast[E,Filter.eventually_atTop, two_mul]
  norm_num[mul_left_comm, sub_eq_add_neg,GaussCircleProblem.N,abs_le]
  use(1),fun a s=>⟨(sub_le_iff_le_add'.1) ? _,?_⟩
  · trans↑(Nat.card (( Finset.Icc (-⌊a⌋) (⌊a⌋)).biUnion fun x=>.image (x,.) (.Icc (-⌊(a^2-x^2).sqrt⌋) (⌊(a^2-x^2).sqrt⌋))))
    · replace:= integral_sqrt_one_sub_sq
      replace:∫b in-a..a,(a^2-b^2 :).sqrt = a*∫x in(-1)..1,(a^2*(1-x^2):).sqrt
      · norm_num[intervalIntegral.integral_comp_mul_left (a^2 -·^2|>.sqrt),←mul_pow, mul_sub,mt (s).trans_eq]
      rewrite[mul_comm, sub_le_iff_le_add,Nat.card_eq_finsetCard,sq, mul_assoc, Finset.card_biUnion, Finset.Icc]
      · norm_num[LocallyFiniteOrder.finsetIcc, Finset.card_image_of_injective,Function.Injective,integral_sqrt_one_sub_sq,s.trans',sq] at this⊢
        norm_num[neg_add_eq_sub, add_nonneg _,←sq,←Int.natCast_floor_eq_floor ∘s.trans',integral_sqrt_one_sub_sq,Int.toNat_add,Int.floor_nonneg, Finset.sum_range_add, Finset.sum_add_distrib]at*
        have :∫b in-a..00,(a^2-b^2 :).sqrt=∫x in(0)..a,.sqrt (a^2-x^2) :=.trans (by rw [←neg_zero,←intervalIntegral.integral_comp_neg]) (by. (simp_rw [neg_sq]))
        rw [← Finset.sum_range_reflect _,a.sqrt_sq ↑(zero_le_one.trans s),← intervalIntegral.integral_add_adjacent_intervals (Continuous.intervalIntegrable (by fun_prop) (-a) 0) (Continuous.intervalIntegrable (by ·fun_prop) 0 a)]at*
        simp_all[←Int.natCast_floor_eq_floor ∘s.trans',Nat.floor_pos, sub_sub, add_assoc, zero_le_one.trans s,Nat.le_sub_one_of_lt ∘ Finset.mem_range.1,integral_sqrt_one_sub_sq]
        replace:∫b in(0)..a,(a^2-b^2 :).sqrt≤∑k ∈.range (.floor a),.sqrt (a^2-(1+k)^2)+a
        · trans ↑(∫b in(0).. (⌊a⌋₊), ↑(a^2-b^2).sqrt)+∫x in⌊a⌋₊..a,(a^2-x^2).sqrt
          · push_cast [intervalIntegral.integral_add_adjacent_intervals,le_rfl,(continuous_const.sub (continuous_pow (2))).sqrt.intervalIntegrable]
          have' := AntitoneOn.integral_le_sum fun and A B R L=>Real.sqrt_le_sqrt (sub_le_sub_left (pow_le_pow_left₀ A.left L @2) (a ^2))
          trans↑(∫b in(0).. (⌊a⌋₊),(a^2-b^2).sqrt)+∫x in⌊a⌋₊..a,(a^2 -⌊a⌋₊^2).sqrt
          use add_right_mono (intervalIntegral.integral_mono_on (Nat.floor_le (by positivity)) (ContinuousOn.intervalIntegrable (by fun_prop)) (by norm_num) fun and ⟨a, _⟩=>by gcongr)
          apply(add_le_add ((zero_add (_: ℝ)▸this)) (intervalIntegral.integral_const _).le).trans (by_contra fun and=>absurd (Finset.sum_range_sub (a^2-.^2|>.sqrt) (.floor a)) fun and=>? _)
          use‹¬_› ((add_le_of_le_sub_left ((mul_le_of_le_one_left (Real.sqrt_nonneg _) (sub_lt_comm.1 (by bound)).le).trans (by simp_all[add_comm (1 : ℝ),zero_le_one.trans ( s), sub_eq_iff_eq_add',add_assoc]))))
        rw [← Finset.sum_congr rfl fun and x =>by rw [←neg_add,add_comm (and : ℝ),neg_sq,←Int.cast_natCast,Int.toNat_of_nonneg (by positivity)]]
        use(ge_of_eq (by rw [_root_.funext fun and=>(Int.cast_natCast _).symm.trans (by rw [Int.toNat_of_nonneg (by positivity)])])).trans' ?_
        have := ( Finset.range (.floor a)).sum_le_sum fun and x =>(Int.lt_floor_add_one (a^2-(1+and)^2).sqrt).le
        nlinarith[Real.two_le_pi, this.trans (by rw [ Finset.sum_add_distrib, Finset.sum_const,nsmul_one, Finset.card_range]),mul_le_mul_of_nonneg_left (by bound: 1 ≤√2) Real.pi_nonneg]
      refine fun and _ _ _ dist=> Finset.disjoint_right.mpr (Finset.forall_mem_image.mpr fun and A B=> dist (congr_arg Prod.fst (( Finset.mem_image.mp B)).choose_spec.right))
    push_cast[norm,neg_le,Set.ncard,Prod.ext_iff,Int.le_floor,Finset.mem_Icc, Finset.mem_image, Finset.mem_biUnion]
    use((congr_arg _).comp (congr_arg _) ((congr_arg _).comp (le_antisymm fun and h=>Set.mem_setOf.mpr ? _) fun and (M) =>?_)).le
    · norm_num[←Real.sqrt_eq_rpow, (by nlinarith[(a^2-and.1^2).sq_sqrt (by nlinarith)]: a^2≥and.1^2+and.2^2),s.trans',Real.sqrt_le_iff]
    norm_num[sq_nonneg _,abs_le.1 ∘ M.out.trans',←Real.sqrt_eq_rpow,le_sub_iff_add_le',Real.abs_le_sqrt _,Real.sqrt_le_iff.1 ∘ M.out.trans']
    repeat use Real.le_sqrt_of_sq_le (by linarith![Real.sqrt_le_iff.1 ((Real.sqrt_eq_rpow _)▸if_neg (two_ne_zero' ℝ≥0∞)▸ M.out) |>.2.trans' (by norm_num:_≥ (and.1^2:ℝ)+and.2^2)])
  trans↑(Nat.card (( Finset.Icc (-⌊a⌋) ⌊a⌋).biUnion fun x=>.image (x,.) (.Icc (-⌊(a^2-x^2).sqrt⌋) (⌊(a^2-x^2).sqrt⌋))))
  · push_cast[neg_le,Set.ncard,Prod.ext_iff,Int.le_floor,Finset.mem_Icc, Finset.mem_image, Finset.mem_biUnion]
    use((congr_arg _).comp (congr_arg _) ((congr_arg _)<|Set.ext fun and=>?_)).le
    norm_num[norm,←abs_le]
    rw [←Real.sqrt_eq_rpow,Real.sqrt_le_left (by linarith)]
    use fun and=>⟨abs_le_of_sq_le_sq (and.trans' (by bound)) (zero_le_one.trans s),by repeat use Real.le_sqrt_of_sq_le (by linarith)⟩,fun p=>?_
    linear_combination .sq_sqrt (sub_nonneg.2 (sq_le_sq.2 (p.1.trans (le_sup_left))))+mul_le_mul_of_nonneg_left p.2.2 (sub_nonneg.2 p.2.1)
  have:=integral_sqrt_one_sub_sq
  replace:∫b in-a..a,(a^2-b^2 :).sqrt = a*∫x in(-1)..1,(a^2* (1-x^2):).sqrt
  · norm_num [intervalIntegral.integral_comp_mul_left fun and=>(a^2 - and^2).sqrt, mul_sub, ←mul_pow,mt (s).trans_eq]
  rw [←add_comm, mul_comm π _,Nat.card_eq_finsetCard,sq _, Finset.card_biUnion, Finset.Icc]
  · norm_num[LocallyFiniteOrder.finsetIcc,mul_assoc,<-two_mul,mul_comm (_*π),integral_sqrt_one_sub_sq,s.trans', Finset.card_image_of_injective,Function.Injective,sq] at this⊢
    norm_num[neg_add_eq_sub, two_mul,←mul_assoc, add_nonneg _,←sq,←Int.natCast_floor_eq_floor ∘s.trans',integral_sqrt_one_sub_sq,Int.toNat_add,Int.floor_nonneg, Finset.sum_range_add, Finset.sum_add_distrib]at*
    have :∫b in-a..00,(a^2-b^2 :).sqrt=∫x in(0)..a,.sqrt (a^2-x^2) :=.trans (by rw [←neg_zero,←intervalIntegral.integral_comp_neg]) (by. (simp_rw [neg_sq]))
    rw [← Finset.sum_range_reflect, a.sqrt_sq ↑(zero_le_one.trans s),← intervalIntegral.integral_add_adjacent_intervals (Continuous.intervalIntegrable (by fun_prop) (-a) 0) (Continuous.intervalIntegrable (by fun_prop) 0 a)] at *
    have :∑b ∈.range (.floor a), ↑⌊(a^2-(1 +b)^2).sqrt⌋ ≤∫x in(0)..a,(a^2-x^2).sqrt
    · trans∫b in(0).. (⌊a⌋₊), ( a^2-b^2).sqrt
      · exact (AntitoneOn.sum_le_integral fun and A B R L=>by cases A with gcongr).trans' (Finset.sum_le_sum (by norm_num[add_comm,Int.floor_le]))|>.trans (congr_arg₂ _ (by abel) (rfl)).le
      exact (monotone_of_hasDerivAt_nonneg fun and=>(Continuous.integral_hasStrictDerivAt (by fun_prop) _ _).hasDerivAt) ( fun and=>Real.sqrt_nonneg _)<|Nat.floor_le (zero_le_one.trans s)
    simp_all[←Int.natCast_floor_eq_floor ∘s.trans',Nat.floor_pos, sub_sub, add_assoc,Nat.le_sub_one_of_lt ∘ Finset.mem_range.1]
    use .trans (by rw [← Finset.sum_congr rfl fun and c=>by rw [←neg_add,add_comm (and : ℝ),neg_sq,←Int.cast_natCast,Int.toNat_of_nonneg (by positivity)]]) @?_
    use .trans (by rw [←_root_.funext fun and=>Int.cast_natCast (Int.toNat _),_root_.funext fun and=>congr_arg _ (Int.toNat_of_nonneg (by positivity))]) ?_
    nlinarith[congr_arg (a*π*.) (a.sq_sqrt (by linarith)),Nat.floor_le (zero_le_one.trans s), mul_le_mul_of_nonneg_left (by bound: 1 ≤√2) Real.pi_nonneg,Real.pi_gt_three]
  refine fun and _ _ _ dist=> Finset.disjoint_right.mpr (Finset.forall_mem_image.mpr fun and A B=> dist (congr_arg Prod.fst (Finset.mem_image.mp B).choose_spec.2))

/--
Hardy and Laundau independently found a lower bound by showing that
$$
  |E(r)| \neq o\left(r^{1/2}(\log r)^{1/4}\right)
$$
-/
@[category research solved, AMS 11]
theorem error_not_isLittleO : ¬E =o[atTop] (fun r => √r * √√r.log) := by
  sorry

/--
It is conjectured that the correct bound is
$$
  |E(r)| = O\left(r^{1/2 + o(1)}\right)
$$

[Ha59]  Hardy, G. H. (1959). _Ramanujan: Twelve Lectures on Subjects Suggested by His Life and Work_(3rd ed.). New York: Chelsea Publishing Company. p. 67

See also https://arxiv.org/abs/2305.03549
-/
@[category research open, AMS 11]
theorem error_isBigO : ∃ (o : ℝ → ℝ) (_ : Tendsto o atTop (𝓝 0)),
    E =O[atTop] fun r => r ^ (1/2 + o r) := by
  sorry

/--
The value of $N(r)$ can be expressed as
$$
  N(r) = 1 + 4\sum_{i=0}^{\infty}\left(\left\lfloor\frac{r^2}{4i+1}\right\rfloor -
    \left\lfloor\frac{r^2}{4i + 3}\right\rfloor\right).
$$
-/
@[category research solved, AMS 11]
theorem exact_form_floor (r : ℝ) (hr : 0 ≤ r) :
    N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋) := by
  sorry

end GaussCircleProblem
