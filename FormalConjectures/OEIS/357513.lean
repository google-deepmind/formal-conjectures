import FormalConjectures.Util.ProblemImports

open Nat


/-!
Numerator of $sum_{k = 1}^n \frac{1}{k^3} * \binom{n}{k}^2 * \binom{n+k}{k}^2 for $n \ge 1$
with $a(0) = 0$.


*Reference:* [A357513](https://oeis.org/A357513)
-/

namespace OeisA357513

/--
A357513: $a(n) = \text{numerator of }
\sum_{k = 1..n} \frac{1}{k^3} \binom{n}{k}^2 \binom{n+k}{k}^2
\text{ for } n \ge 1 \text{ with } a(0) = 0$.
-/
def a (n : ℕ) : ℕ :=
 ∑ k ∈ (Finset.Icc 1 n), ((n.choose k : ℚ) ^ 2 * ((n + k).choose k : ℚ) ^ 2) / k ^ 3 |>.num.natAbs


@[category test, AMS 11]
theorem zero : a 0 = 0 := rfl

@[category test, AMS 11]
theorem one : a 1 = 4 := by
  unfold a
  norm_num only [Nat.choose, Finset.sum_Icc_succ_top, Finset.Icc_self, Finset.sum_singleton]

@[category test, AMS 11]
theorem two : a 2 = 81 := by
  unfold a
  norm_num only [Nat.choose, Finset.sum_Icc_succ_top, Finset.Icc_self, Finset.sum_singleton]

@[category test, AMS 11]
theorem three : a 3 = 14651 := by
  unfold a
  norm_num only [Nat.choose, Finset.sum_Icc_succ_top, Finset.Icc_self, Finset.sum_singleton]

@[category test, AMS 11]
theorem four : a 4 = 956875 := by
  unfold a
  norm_num only [Nat.choose, Finset.sum_Icc_succ_top, Finset.Icc_self, Finset.sum_singleton]

@[category test, AMS 11]
theorem five : a 5 = 1335793103 := by
  unfold a
  norm_num only [Nat.choose, Finset.sum_Icc_succ_top, Finset.Icc_self, Finset.sum_singleton]


def is_p_integral (p : ℕ) (x : ℚ) : Prop := x.den % p ≠ 0

def q_modeq (p : ℕ) (k : ℕ) (x y : ℚ) : Prop :=
  ∃ z, is_p_integral p z ∧ x - y = (p ^ k : ℚ) * z

def term_rat (n k : ℕ) : ℚ :=
  (Nat.choose n k : ℚ) ^ 2 * (Nat.choose (n + k) k : ℚ) ^ 2 / (k : ℚ) ^ 3

def H (n r : ℕ) : ℚ := Finset.sum (Finset.Icc 1 n) (fun k => 1 / (k : ℚ)^r)

lemma rat_num_mod_pk (p k : ℕ) (x : ℚ) (hp : Nat.Prime p)
    (h_int : is_p_integral p x) (h_cong : q_modeq p k x 0) :
    (x.num : ℤ) ≡ 0 [ZMOD (p ^ k : ℤ)] := by
  delta is_p_integral q_modeq Int.ModEq at *
  refine h_cong.elim fun and h=>(h.2▸sub_zero _)▸ Rat.mul_num _ _▸mod_cast(? _)
  exact (.trans (by rw [Int.natAbs_mul,Int.natAbs_ofNat, one_mul,((hp.coprime_iff_not_dvd.2 (by valid)).pow_left _).mul and.reduced]) (by norm_num))

lemma q_modeq_sum {p k : ℕ} {s : Finset ℕ} {f g : ℕ → ℚ} (hp : Nat.Prime p) :
    (∀ i ∈ s, q_modeq p k (f i) (g i)) →
    q_modeq p k (Finset.sum s f) (Finset.sum s g) := by
  delta q_modeq Finset.sum
  norm_num[is_p_integral,mul_comm,hp.ne_zero,←div_eq_iff]
  use fun and=>ne_of_eq_of_ne (by rw [←s.sum_sub_distrib,s.sum_div]) @?_
  induction(s) using Finset.cons_induction with|empty=>field_simp [hp.ne_one]|cons=>_
  simp_all[mt (dvd_trans.comp p.dvd_of_mod_eq_zero · (Rat.add_den_dvd _ _)),hp.dvd_mul,p.dvd_iff_mod_eq_zero]

lemma q_modeq_mul_scaling (p k j : ℕ) (x y u : ℚ) (hp : Nat.Prime p)
  (hu : is_p_integral p u) (h : q_modeq p k x y) :
  q_modeq p (k + j) ((p^j : ℚ) * u * x) ((p^j : ℚ) * u * y) := by
  delta is_p_integral q_modeq at *
  refine h.elim fun A B=>⟨u*A,u.mul_den A▸hu ∘? _,.trans (by rw [←mul_sub, B.2]) (by ring)⟩
  refine (by valid ∘ hp.dvd_mul.mp).comp (p.dvd_of_mod_eq_zero · |>.trans (Nat.div_dvd_of_dvd ↑(gcd_dvd_right _ _)) )

lemma term_identity (p : ℕ) (k : ℕ) (hp : Nat.Prime p) (hk : k ∈ Finset.Icc 1 (p - 1)) :
  term_rat (p - 1) k = (p : ℚ)^2 / k^5 * ((1 - (p : ℚ)/k)^2 *
    (Finset.prod (Finset.Icc 1 (k - 1)) (fun j => 1 - (p : ℚ)^2 / j^2))^2) := by
  simp_all[term_rat]
  field_simp[*,Nat.cast_choose,k.ne_of_gt hk.1]
  field_simp [hp.pos,hp.ne_zero,←Nat.Ico_succ_right, Finset.prod_Ico_eq_prod_range,←Nat.factorial_mul_ascFactorial,Nat.ascFactorial_eq_prod_range]
  norm_cast
  simp_rw [add_comm 1,Int.subNatNat]
  trans p^2*((p-k)^2*(∏ a ∈.range (k-1),(p^2-(a+1)^2): Int)^2)*((k !*(p-1-k)!)^2*( (k : ℕ)!*(p-1)!)^2*k^3)
  · obtain ⟨l, rfl⟩:=k.exists_eq_succ_of_ne_zero<|by valid
    simp_all![sq_sub_sq,←Nat.factorial_mul_descFactorial hk.2, Finset.prod_range_succ', Finset.prod_mul_distrib, Finset.prod_pow]
    push_cast[l.le_of_lt hk,hp.pos,Nat.descFactorial_eq_prod_range,sq_sub_sq, Finset.prod_mul_distrib]
    field_simp [hp.pos, sub_sub, mul_pow,add_comm (1 : ℤ), ( Finset.mem_range.1 _).le.trans (le_of_lt hk),pow_succ,mul_assoc,mul_comm (p : ℤ), Finset.prod_mul_distrib]
    use symm<|.trans (by rw [_root_.funext fun i=>mul_self_sub_mul_self _ _, Finset.prod_mul_distrib])<|by ring
  split
  · omega
  push_cast[← Finset.prod_pow,Int.negSucc_eq]
  refine congr_arg (_*.* _) ((congrArg₂ _) ((congr_arg (.^2) (by valid)).trans (neg_sq _).symm) (Finset.prod_congr rfl fun a s=>?_))
  split
  · simp_all only[push_cast, sub_sq_comm,Int.ofNat_eq_coe,tsub_eq_zero_iff_le]
  · exact (congr_arg (.^2) ( sub_eq_of_eq_add (mod_cast (by valid)))).trans (neg_sq _).symm

lemma prod_approx_one (p : ℕ) (k : ℕ) (hp : Nat.Prime p) (hk : k ∈ Finset.Icc 1 (p - 1)) :
  q_modeq p 2 ((Finset.prod (Finset.Icc 1 (k - 1)) (fun j => 1 - (p : ℚ)^2 / j^2)) ^ 2) 1 := by
  push_cast[q_modeq,←div_pow,← Finset.prod_pow,←Nat.Ico_succ_right, Finset.prod_Ico_eq_prod_range, Finset.mem_Ico]at*
  field_simp [hp.ne_zero, sub_sq_comm,is_p_integral,add_comm,mul_comm,hp.one_le,←div_eq_iff]at*
  norm_cast
  push_cast[←p.dvd_iff_mod_eq_zero,div_eq_mul_inv, Rat.divInt_eq_div, Rat.mul_den]
  rw_mod_cast[p.dvd_div_iff_mul_dvd<|Nat.gcd_dvd_right _ _,Rat.inv_natCast_num_of_pos (by cases hp.pos with positivity),mul_one, one_mul, Rat.inv_natCast_den_of_pos (by cases hk.2 with positivity)]
  rw [← Finset.prod_congr rfl fun and β=>by rw [Int.subNatNat_of_le (pow_le_pow_left' ((List.mem_range.1 β).trans_le (by valid)) _)],sq,mul_right_comm, mul_dvd_mul_iff_right hp.ne_zero]
  use mt ((Nat.dvd_gcd (Int.natCast_dvd.1 ?_) (mul_dvd_mul_right ⟨_, rfl⟩ _)).trans) ?_
  · field_simp [hk.2.le.trans' ∘(k.sub_le (1)).trans_lt',<-ZMod.intCast_zmod_eq_zero_iff_dvd, Finset.mem_range.1,sq,Nat.mul_self_lt_mul_self,Nat.succ_le]
    field_simp [hk.2.le.trans',←sq, sub_sq',(k.sub_le (1)).trans' ∘ Finset.mem_range.1,dvd_trans ↑_ (sub_dvd_pow_sub_pow _ _ _),Nat.pow_le_pow_left, Finset.prod_int_mod]
    cases(p: Int)^2 using Int.negInduction with norm_num[<-ZMod.intCast_zmod_eq_zero_iff_dvd]
  · use (p.mul_dvd_mul_iff_left hp.pos).not.2 (hp.prime.not_dvd_finset_prod fun and=>mt hp.dvd_of_dvd_pow ∘mt hp.dvd_of_dvd_pow ∘mt p.eq_zero_of_dvd_of_lt ∘by valid ∘ Finset.mem_range.1)

lemma term_approx_mod_p4 (p : ℕ) (hp : Nat.Prime p) (h_ge5 : p ≥ 5)
    (k : ℕ) (hk : k ∈ Finset.Icc 1 (p - 1)) :
    q_modeq p 4 (term_rat (p - 1) k) ((p : ℚ)^2 / k^5 - 2 * (p : ℚ)^3 / k^6) := by
  have h_id := term_identity p k hp hk
  let P := (Finset.prod (Finset.Icc 1 (k - 1)) (fun j => 1 - (p : ℚ)^2 / j^2)) ^ 2
  have h_P : q_modeq p 2 P 1 := prod_approx_one p k hp hk
  have h_sq : q_modeq p 2 ((1 - (p : ℚ)/k)^2) (1 - 2 * p / k) := by
    simp_all[q_modeq, mul_div_assoc, sub_sq]
    norm_num[is_p_integral,term_rat,div_eq_mul_inv, mul_pow,hp.ne_zero] at h_id⊢
    exact (mod_cast(Rat.inv_natCast_den_of_pos ↑( k.pow_pos ↑(hk.1) )).symm▸by valid ∘p.eq_zero_of_dvd_of_lt ∘ hp.dvd_of_dvd_pow ∘p.dvd_of_mod_eq_zero)
  have h_inner : q_modeq p 2 ((1 - (p : ℚ)/k)^2 * P) (1 - 2 * p / k) := by
    simp_all[q_modeq]
    delta term_rat is_p_integral at*
    refine h_P.elim (h_sq.elim fun A B a s=>⟨(1-p/k)^2 * a+A,? _,by nlinarith⟩)
    field_simp[show k≠00by valid] at B(s)⊢
    rw [←a.num_div_den,← A.num_div_den]
    field_simp[<-p.dvd_iff_mod_eq_zero]at s B⊢
    norm_cast
    exact (hp.not_dvd_mul) (hp.not_dvd_mul s.1 B.1) (by valid ∘p.le_of_dvd hk.1 ∘hp.dvd_of_dvd_pow) ∘(·.trans (mod_cast Rat.den_dvd _ (_:Nat)))
  have h_scale : q_modeq p 4 ((p : ℚ)^2 / k^5 * ((1 - (p : ℚ)/k)^2 * P))
                             ((p : ℚ)^2 / k^5 * (1 - 2 * p / k)) := by
    simp_all[q_modeq]
    delta term_rat is_p_integral at*
    refine h_inner.elim fun A B=>⟨A/k^5,? _,.trans (by rw [←mul_sub, B.2]) (by ring)⟩
    norm_num[div_eq_mul_inv, A.mul_den,←inv_pow] at B⊢
    use (if_neg (by valid : ¬k=0)▸hp.not_dvd_mul (by valid) (by valid ∘p.le_of_dvd hk.1 ∘hp.dvd_of_dvd_pow) ∘ (p.dvd_of_mod_eq_zero ·|>.trans (Nat.div_dvd_of_dvd ↑(gcd_dvd_right _ _))))
  have h_rhs : (p : ℚ)^2 / k^5 * (1 - 2 * p / k) = (p : ℚ)^2 / k^5 - 2 * (p : ℚ)^3 / k^6 := by
    ring
  convert@h_rhs▸ h_scale

lemma harmonic_reflection (p : ℕ) (hp : Nat.Prime p) (h_ge5 : p ≥ 5) :
    q_modeq p 2 (2 * H (p - 1) 5) (-5 * (p : ℚ) * H (p - 1) 6) := by
  have h_term : ∀ k ∈ Finset.Icc 1 (p - 1), q_modeq p 2 (1 / ((p : ℚ) - k)^5) (-1/k^5 - 5*p/k^6) := by
    simp_all[ q_modeq, mul_div_assoc,neg_div]
    norm_num[is_p_integral,mul_comm,<-sub_add,<-inv_pow,hp.ne_zero,←div_eq_iff]
    field_simp+contextual[show∀x,x≤p-1 →p≠x by valid, sub_ne_zero,←p.dvd_iff_mod_eq_zero]
    use fun x a s=>mod_cast(? _)
    push_cast[mul_assoc,sq,Int.subNatNat_of_le (s.trans (p.pred_le)),div_eq_mul_inv, Rat.divInt_eq_div, Rat.mul_den]
    rw_mod_cast[p.dvd_div_iff_mul_dvd<|Nat.gcd_dvd_right _ _,Rat.inv_natCast_num_of_pos (by bound[ (by valid:x<p)]),mul_one, one_mul, Rat.inv_natCast_den_of_pos (by bound[ (by valid:x<p)])]
    field_simp[←add_mul,←mul_assoc, mul_dvd_mul_iff_right,s.trans (p.pred_le),Nat.gcd_dvd]
    by_cases h:p ∣(x^5+(p-x)^5)*x+p*5*(p-x)^5
    · rcases hp.dvd_mul.mp.comp (p.dvd_add_left ⟨ _,mul_assoc _ _ _⟩).mp h
      · use (by valid:).elim fun and true => true▸mt (dvd_gcd ?_ (mul_dvd_mul_right (dvd_mul_left _ _) _)).trans ?_
        · push_cast[mul_assoc,←mul_add,←Int.ofNat_inj,s.trans (p.pred_le)]at true⊢
          zify[s.trans (p.pred_le)]
          ring_nf at ( true)⊢
          use(5)*p^4*x^5-25*p^3*x^6+50*p^2*x^7-50*p*x^8+25*x^9+(p^3-5*p^2*x+10*p*x*x-10*x^3)*x^6,by linear_combination-x^6*true
        · field_simp [hp.dvd_mul,mt hp.dvd_of_dvd_pow, mul_dvd_mul_iff_right,x.not_dvd_of_pos_of_lt a (by valid:x<p),s.trans (p.pred_le),p.dvd_sub_iff_right]
      · use (by valid ∘p.le_of_dvd a) (by valid)
    · simp_all[←CharP.cast_eq_zero_iff (ZMod p),s.trans,pow_succ]
  delta q_modeq H Rat at*
  choose! I K V using(id) h_term
  delta is_p_integral at *
  replace h_term:∑ a ∈.Icc (1) (p-1),1/(p-a:ℚ)^5=∑ a ∈.Icc (1) (p-1), 1/(a^5:ℚ) :=.trans ( Finset.sum_Ico_eq_sum_range _ _ _) (.trans (by rw [← Finset.sum_range_reflect]) ? _)
  · use∑ a ∈.Icc (1) (p-1), I a, fun and=>? _,?_
    · replace V: (∑ a ∈.Icc (1) (p-1), I a).2 ∣∏ a ∈.Icc (1) (p-1),(I a).2:=(p-1).rec (by rfl ) fun and p=>.trans (by rw [ Finset.sum_Icc_succ_top and.succ_pos, Rat.add_def]) ?_
      · simp_rw [ Finset.prod_Icc_succ_top and.succ_pos, Rat.normalize_eq]
        exact (Nat.div_dvd_of_dvd ↑(gcd_dvd_right _ _)).trans (by gcongr)
      · exact (hp.prime.exists_mem_finset_dvd ((p.dvd_of_mod_eq_zero and).trans V)).choose_spec.elim (K _ · ·.modEq_zero_nat)
    · simp_all only[mul_one_div, two_mul,neg_mul,neg_div, sub_neg_eq_add,←sub_add,← Finset.sum_sub_distrib, Finset.mul_sum]
      simp_all only[← V,div_eq_mul_inv, one_mul,← Finset.mul_sum, two_mul, Finset.sum_add_distrib]
  · exact(( Finset.sum_Ico_eq_sum_range _ _ _).trans (Finset.sum_congr rfl (by field_simp+contextual[eq_self,add_sub,←sub_add,hp.one_lt,·.le_sub_one_of_lt]))).symm

lemma harmonic_vanish_6 (p : ℕ) (hp : Nat.Prime p) (h_ge5 : p ≥ 5) (h_neq7 : p ≠ 7) :
    q_modeq p 1 (H (p - 1) 6) 0 := by
  delta Ne q_modeq H at *
  field_simp[is_p_integral,mul_comm,←div_eq_iff]
  simp_rw [div_eq_mul_inv, one_mul, Rat.mul_den,←p.dvd_iff_mod_eq_zero]
  simp_all[p.dvd_div_iff_mul_dvd,hp.ne_zero,←inv_pow, Rat.inv_natCast_num_of_pos hp.pos,Nat.gcd_dvd]
  rw[Nat.Coprime.gcd_mul_left_cancel_right, mul_dvd_mul_iff_right hp.ne_zero]
  · have := (∑ a ∈.Icc (1) (p-1), (↑a)⁻¹^6:ℚ).num_div_den
    rw[div_eq_iff,Nat.gcd_eq_right ∘Int.natCast_dvd.mp]at *
    · replace: (∑ a ∈.Icc (1) (p-1),(a:ℚ)⁻¹^6).2 ∣∏ a ∈.Icc (1) (p-1), a^6:=(p-1).rec (refl _) fun and y=>.trans (by rw [ Finset.sum_Icc_succ_top and.succ_pos, Rat.add_def]) ?_
      · simp_all -contextual [ Finset.prod_Icc_succ_top, and.succ_pos, Rat.normalize]
        exact (Nat.div_dvd_of_dvd ↑(gcd_dvd_right _ _)).trans ↑(mul_dvd_mul y ↑(mod_cast↑( Rat.inv_natCast_den_of_pos (by·bound)).dvd))
      · exact (hp.prime.not_dvd_finset_prod fun and=>mt hp.dvd_of_dvd_pow ∘mt p.eq_zero_of_dvd_of_lt ∘by valid ∘ Finset.mem_Icc.mp).comp ↑(·.trans this)
    · replace:↑p ∣ (∑ a ∈.Icc (1) (p-1), (a : Rat)⁻¹^6).1*∏ a ∈.Icc (1) (p-1), a^6
      · trans∑ a ∈.Icc (1) (p-1), (∑ a ∈.Icc (1) (p-1),(a: (ℚ))⁻¹^6).2*∏ a ∈.Icc (1) (p-1)\singleton a, a^6
        · convert (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by_contra (absurd (Fact.mk hp) fun and=>(@IsCyclic.exists_generator (ZMod p)ˣ _ _).elim fun and h=>. (_)))
          trans∑S:_ˣ, ↑(∑ a ∈.Icc (1) (p-1),(a:ℚ)⁻¹^6).2*(∏ a ∈.Icc (1) (p-1), a ^6: ZMod p)/S.val^6
          · replace :.Icc (1) (p-1)= Finset.univ.image fun and: ( ZMod p)ˣ=>and.val.val:= Finset.eq_of_subset_of_card_le @(?_) ?_
            · field_simp only [mul_assoc, this, Int.cast_sum, Int.cast_mul, Int.cast_prod, Int.cast_pow,push_cast,ZMod.natCast_zmod_val, Finset.sum_image fun and _ _ _ h=>Units.ext (ZMod.val_injective p h), Finset.sdiff_singleton_eq_erase]
              exact Finset.sum_congr rfl fun and β=>by rw [← Finset.prod_erase_mul _ _ (( Finset.mem_image_of_mem _) β),eq_div_iff (by norm_num), and.1.natCast_zmod_val, mul_assoc]
            · use fun and μ=>(Finset.mem_Icc.1 μ).elim fun and b=> Finset.mem_image.2 ⟨Units.mk0 _ ((CharP.cast_eq_zero_iff _ _ _).not.2 (by valid ∘p.le_of_dvd and)), Finset.mem_univ _,ZMod.val_cast_of_lt (by valid)⟩
            · exact Finset.card_mono (Finset.image_subset_iff.mpr @fun R L=> Finset.mem_Icc.mpr ⟨ZMod.val_pos.mpr R.ne_zero, R.val.val_lt.le_pred⟩)
          · have:orderOf and=p-1:=by field_simp[orderOf_eq_card_of_forall_mem_zpowers,ZMod.card_units]
            by_cases h :orderOf and ∣6
            · match p with|5|6|8=>norm_num[*]at hp h | S+9=>cases Nat.eq_zero_of_dvd_of_lt h (by valid)
            · exact (eq_zero_of_mul_eq_self_left (inv_ne_one.2 (Units.ext_iff.not.1 (h ∘orderOf_dvd_of_pow_eq_one))) (( Finset.mul_sum _ _ _).trans (Fintype.sum_equiv (.mulLeft and) _ _ (by field_simp [h, mul_pow]))))
        · use(1), Rat.intCast_injective ↑(.trans (by rw [Int.cast_mul, this, Finset.sum_mul, Finset.sum_mul]) @? _)
          exact (.symm (.trans (by rw [mul_one, Int.cast_sum]) (Finset.sum_congr rfl fun and=> (by cases Finset.mem_Icc.1 · with field_simp only [push_cast, one_pow, one_mul, Finset.sdiff_singleton_eq_erase, Finset.prod_erase_mul,mul_assoc]))))
      · exact (Int.Prime.dvd_mul' hp this).resolve_right (mod_cast hp.prime.not_dvd_finset_prod fun and=>mt hp.dvd_of_dvd_pow ∘mt p.eq_zero_of_dvd_of_lt ∘by valid ∘Finset.mem_Icc.1)
    · positivity
  · exact ( Rat.reduced _).symm

lemma sum_is_integral (p : ℕ) (hp : Nat.Prime p) (h_ge5 : p ≥ 5) :
    is_p_integral p (Finset.sum (Finset.Icc 1 (p - 1)) (fun k => term_rat (p - 1) k)) := by
  push_cast[is_p_integral,term_rat,·≥ ·,←Nat.Ico_succ_right, false, Finset.sum_Ico_eq_sub] at*
  norm_num[←mul_pow,←p.dvd_iff_mod_eq_zero, Finset.sum_range_succ']
  have : ∀ (n : ℕ),(∑n ∈.range (n : ℕ),((p-1).choose (n + 1)*(p-1+ (n + 1)).choose (n + 1))^2/( (n + 1)^3):ℚ).2 ∣∏ a ∈.range (n : ℕ),(a+1)^3:=Nat.rec (by rfl ) fun and j=>.trans (by rw [ Finset.sum_range_succ]) ?_
  · rw[div_eq_mul_inv, Finset.prod_range_succ, Rat.add_def]
    simp_all[Rat.normalize,Rat.mul_den]
    exact (Nat.div_dvd_of_dvd ↑(gcd_dvd_right _ _)).trans ↑(mul_dvd_mul j ((Nat.div_dvd_of_dvd ↑(gcd_dvd_right _ _)).trans ((mod_cast (Rat.inv_natCast_den_of_pos (by ·bound)).dvd))))
  · exact (hp.prime.not_dvd_finset_prod fun and=>mt hp.dvd_of_dvd_pow ∘mt p.eq_zero_of_dvd_of_lt ∘by valid ∘ Finset.mem_range.1).comp (·.trans (this _))

/--
We have  $a(p-1) \equiv 0 \pmod{p^4}$ for all primes $p \ge 3$ except $p=7$.
-/
@[category research solved, AMS 11]
theorem a357513_supercongruence (p : ℕ) (hp : Nat.Prime p) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7) :
    (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4] := by
  rcases eq_or_ne p 3 with rfl | h_ne3
  · have h_a2 : (a 2 : ℤ) = 81 := by
      simp_all!
      delta a
      norm_num only [Nat.choose, Finset.sum_Icc_succ_top, Finset.Icc_self, Finset.sum_singleton]
    have h_mod : (81 : ℤ) ≡ 0 [ZMOD (3 : ℤ) ^ 4] := by
      simp_all +decide[a]
    clear h_a2 h_mod
    norm_num[a]
    norm_num+decide only[ Finset.sum_Icc_succ_top, Finset.Icc_self, Finset.sum_singleton,Nat.choose]
  · have hp_ge5 : p ≥ 5 := by
      if R :p=4 then{norm_num[R] at hp} else ·omega
    let n := p - 1
    let S : ℚ := Finset.sum (Finset.Icc 1 n) (fun k => term_rat n k)
    have h_sum_cong : q_modeq p 4 S 0 := by
      let H5 := H n 5
      let H6 := H n 6
      have h_term_cong : ∀ k ∈ Finset.Icc 1 n,
          q_modeq p 4 (term_rat n k) ((p : ℚ)^2 / k^5 - 2 * (p : ℚ)^3 / k^6) :=
        fun k hk => term_approx_mod_p4 p hp hp_ge5 k hk
      have h_sum_approx : q_modeq p 4 S ((p : ℚ)^2 * H5 - 2 * (p : ℚ)^3 * H6) := by
        simp_all only[term_rat, S, H6,q_modeq, H,n,div_eq_mul_inv,←inv_pow]
        choose! A B using‹_›
        simp_all only[is_p_integral, sub_eq_iff_eq_add, one_mul,n, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        exists∑ a ∈.Icc (1) n, A a, fun and=>?_
        · replace h_neq7:(∑ a ∈.Icc (1) n, A a).2 ∣∏ a ∈.Icc (1) (n : ℕ),(A a).2:=(Finset.Icc _ _).induction (by rfl ) fun and a s=>?_
          · exact (by field_simp [(Rat.add_den_dvd _ _).trans, mul_dvd_mul,·])
          · use(hp.prime.exists_mem_finset_dvd<| (p.dvd_of_mod_eq_zero and).trans h_neq7).elim (B · ·.1|>.1 (by omega))
        · exact (congr_arg₂ _) (Finset.mul_sum _ _ _).symm ((congr_arg₂ _) (( Finset.mul_sum _ _ _).symm.trans (congr_arg _ (Finset.sum_congr rfl (by bound)))) rfl )
      have h_refl : q_modeq p 2 (2 * H5) (-5 * (p : ℚ) * H6) := harmonic_reflection p hp hp_ge5
      have h_refl_scaled : q_modeq p 4 (2 * (p : ℚ)^2 * H5) (-5 * (p : ℚ)^3 * H6) := by
        delta term_rat q_modeq at*
        exact (h_refl).imp fun and=>.imp_right (by linear_combination2.*p^2)
      have h_rhs_val : q_modeq p 4 (2 * ((p : ℚ)^2 * H5 - 2 * (p : ℚ)^3 * H6)) (-9 * (p : ℚ)^3 * H6) := by
        delta q_modeq at*
        exact (by valid:).imp fun and=>.imp_right (.trans (by ring))
      have h_H6_van : q_modeq p 1 H6 0 := harmonic_vanish_6 p hp hp_ge5 h_neq7
      have h_vanish : q_modeq p 4 (-9 * (p : ℚ)^3 * H6) 0 := by
        norm_num[ q_modeq]at‹_›⊢
        norm_num[is_p_integral]at‹_›⊢
        refine (by valid:).elim fun A B=>⟨-9*A, B.1 ∘p.mod_eq_zero_of_dvd ∘ fun and=>?_, B.2▸by ring⟩
        rw[ Rat.mul_den]at and
        exact (p.dvd_of_mod_eq_zero and).trans (by. (norm_num[Nat.div_dvd_of_dvd _,Nat.gcd_dvd]))
      have h_2S : q_modeq p 4 (2 * S) 0 := by
        rw[ q_modeq]at*
        norm_num[is_p_integral, sub_eq_iff_eq_add] at h_sum_approx‹∃_, _∧H6-0 =_›h_rhs_val‹_›⊢
        refine h_sum_approx.elim (h_vanish.elim (h_rhs_val.elim fun a s A B R L=>⟨2*R+a+A,?_, L.2▸by linarith⟩))
        apply lt_self_iff_false 10 |>.elim fun and x =>mt (p.dvd_of_mod_eq_zero · |>.trans ( Rat.add_den_dvd _ _)) ?_
        use hp.not_dvd_mul (mt (·.trans ( Rat.add_den_dvd _ _)) ? _)<|by valid
        norm_num[*,hp.dvd_mul,mt (dvd_trans · (Rat.mul_den_dvd _ _)),p.dvd_iff_mod_eq_zero]
      have h_S : q_modeq p 4 S 0 := by
        norm_num[q_modeq] at h_2S⊢
        field_simp[is_p_integral,mul_comm (2 :ℚ),←div_eq_iff]at h_2S⊢
        refine h_2S.elim fun A B=>⟨A/2, B.1 ∘ fun and=>p.mod_eq_zero_of_dvd ? _,by bound⟩
        rw[div_eq_mul_inv, A.mul_den]at and
        exact ( (p.coprime_primes hp (by decide ) ).mpr (by valid)).dvd_mul_right.mp (Rat.inv_natCast_den_of_pos two_pos▸ (p.dvd_of_mod_eq_zero and).trans ↑(Nat.div_dvd_of_dvd ↑(gcd_dvd_right _ _)))
      valid
    have h_S_int : is_p_integral p S := sum_is_integral p hp hp_ge5
    have h_a_val : (a n : ℤ) = S.num := by
      norm_num[a,term_rat,S]
      positivity
    simp_all[is_p_integral,q_modeq,Int.modEq_zero_iff_dvd,n]
    choose _ _ _simpa using(id) h_sum_cong
    norm_num[*, Rat.mul_num, Rat.mul_den]
    field_simp[Int.natAbs_mul,Int.natAbs_pow,((hp.coprime_iff_not_dvd.2 (by valid ∘p.mod_eq_zero_of_dvd)).pow_left _).mul (Rat.reduced _),id]

end OeisA357513
