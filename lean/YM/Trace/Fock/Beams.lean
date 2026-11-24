import YM.Trace.Fock.Dilation
/-! Polynomial coefficient beams with a single joint spacetime factor as L² weights. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace YM.Trace.Shell
open YM Boundary Complex Set Function MeasureTheory Filter
open scoped BigOperators Pointwise Topology ENNReal InnerProductSpace
variable {q n m : ℕ} (c : chartIdx q n→ℂ)
def degrees (q n : ℕ) := Finset.univ.image (@beamDegree q n)
def sectionFunc (d : ℕ) (x:Cords n) := ∑ i ∈ Finset.univ.filter (fun i=> beamDegree i = d), termFunc c i x
  where termFunc (c : chartIdx q n → ℂ) (i : chartIdx q n) (x:Cords n) := c i * ∏ l, dividedSlot (i l) (x l)
def termFunc := @sectionFunc.termFunc

lemma section_sum (x): release c x=∑ d ∈ degrees q n, sectionFunc c d x := Eq.symm (Finset.sum_fiberwise_of_maps_to (f:=fun i=>termFunc c i x)
   (h:=fun i (_hi:i∈(Finset.univ:Finset (chartIdx q n)))=> Finset.mem_image.mpr ⟨i,by simp,rfl⟩))
lemma dividedSlot_smul (t : ℝ) (ht : 0<t) (b : momentSlot q) (p : Mom) (hb : momentDegree b ≠ 0) : dividedSlot b (t • p) = ↑(t^(momentDegree b-1)) * dividedSlot b p := by
    unfold dividedSlot; rw [momentEntry_smul t ht.le b p,norm_smul,Real.norm_of_nonneg ht.le,show momentDegree b=(momentDegree b-1)+1 from by omega]
    push_cast; rw [pow_succ] -- issue rewriting both; check
    have hc (p : Mom) : (t:ℂ) ≠0 := ofReal_ne_zero.mpr ht.ne'
    by_cases h : ‖p‖=0
    · rw [h]; simp
    have : (↑‖p‖:ℂ)≠0 := by norm_cast
    field_simp [hc p]
lemma termFunc_smul (i) (x) {t : ℝ} (ht:0<t) (hc : highCap c) : termFunc c i (t • x) = ↑(t^(beamDegree i))*termFunc c i x := by
 unfold termFunc sectionFunc.termFunc
 by_cases h:c i=0; · rw [h,zero_mul,zero_mul,mul_zero]
 have hb (j):momentDegree (i j)≠0 := fun hx=>h (hc _ _ hx)
 simp_rw [Pi.smul_apply, fun j => dividedSlot_smul t ht _ (x j) (hb j)]
 rw [Finset.prod_mul_distrib]; push_cast; rw [Finset.prod_pow_eq_pow_sum, ← mul_assoc, mul_comm (c i), mul_assoc]; rfl
lemma section_smul (d) (x) {t : ℝ} (ht : 0<t) (hc : highCap c) : sectionFunc c d (t • x)= (t:ℂ)^d * sectionFunc c d x := by
 unfold sectionFunc; rw [Finset.mul_sum]
 apply Finset.sum_congr rfl (fun i hi => by push_cast at *; have hh := termFunc_smul c i x ht hc; push_cast at hh; rw [Finset.mem_filter.mp hi|>.2] at hh; exact hh)
@[fun_prop] lemma divided_meas (b : momentSlot q) : Measurable (dividedSlot b) := (momentEntry_cont b).measurable.div (by fun_prop)
@[fun_prop] lemma termFunc_meas (i) : Measurable (termFunc c i) := measurable_const.mul (Finset.measurable_prod _ (fun j _=> (divided_meas ..).comp (measurable_pi_apply j)))
@[fun_prop] lemma section_meas (d) : Measurable (sectionFunc c d) := Finset.measurable_sum _ (fun i _=> termFunc_meas ..)
lemma divided_bound (b : momentSlot q) (hb : 0<momentDegree b) : ∃ C≥(0:ℝ), ∀ p : Mom, ‖dividedSlot b p‖ ≤ C*weight (q+1) p := by
   obtain ⟨C,hC,H⟩ := momentEntry_bound b
   let d := momentDegree b
   let B := C*2^d
   have hB : 0≤ B := mul_nonneg hC (by positivity)
   have hd : d-1 ≤ q+1 := by dsimp [d,momentDegree]; have := b.2.1.isLt; split <;> omega
   refine ⟨B,hB,fun p=> ?_⟩
   by_cases hp:p=0; · subst p; unfold dividedSlot; rw [norm_zero,ofReal_zero,div_zero,norm_zero]; exact mul_nonneg hB (weight_pos ..|>.le)
   let s := ‖p‖⁻¹ • p
   have hx : 0<‖p‖ := norm_pos_iff.mpr hp
   have hS : ‖s‖=1 := by dsimp only [s]; rw [norm_smul,Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hx.ne']
   have ht := dividedSlot_smul (‖p‖) hx b s hb.ne'
   rw [show ‖p‖ • s=p from smul_inv_smul₀ (α:=ℝ) (norm_ne_zero_iff.mpr hp) _] at ht
   rw [ht,norm_mul,norm_real,Real.norm_of_nonneg (by positivity),mul_comm B]
   have hQ := mul_le_mul ((pow_le_pow_left₀ hx.le (show ‖p‖ ≤ 1+‖p‖ by linarith) _).trans (pow_le_pow_right₀ (by linarith) hd))
     (show ‖dividedSlot b s‖ ≤ B from ?_) (norm_nonneg _) (weight_pos ..|>.le)
   exact hQ
   rw [dividedSlot,norm_div,norm_real, hS,Real.norm_eq_abs,abs_one, div_one]
   exact (H s).trans_eq (by rw [weight,hS,one_add_one_eq_two])

lemma divided_tail (b : momentSlot q) (hb : 0<momentDegree b) : Integrable (fun p=> (((weight (q+3) p)⁻¹ * ‖dividedSlot b p‖)^2)) ν := by
    obtain ⟨C,hC,hB⟩:= divided_bound b hb
    refine integrable_shell_arbitrary_bound _ (by unfold weight; fun_prop) (C^2) 4 (by norm_num) (fun x=> ?_)
    have hX : 0≤ (1+‖x‖) := by positivity
    have hm := mul_le_mul_of_nonneg_left (α:=ℝ) (hB x) (inv_nonneg.mpr (weight_pos (q+3) x|>.le))
    have hk : (1+‖x‖)^(-(4:ℝ)) = (((1+‖x‖)^2)⁻¹)^2 := by rw [Real.rpow_neg hX,← show (↑(4:ℕ):ℝ)=4 by norm_num, Real.rpow_natCast,inv_pow,← pow_mul]
    rw [hk,←mul_pow,Real.norm_of_nonneg (by positivity)]
    have hwEq : _ = _ := show (weight (q+3) x)⁻¹ * (C*weight (q+1) x)=C*((1+‖x‖)^2)⁻¹ by unfold weight; rw [show q+3=q+1+2 by omega, pow_add, mul_inv]; field_simp
    exact pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr (weight_pos ..|>.le)) (norm_nonneg _)) (hm.trans_eq hwEq) _
variable (f : Test4)
@[fun_prop] lemma testedSection_meas (d) : Measurable (fun x=> plus f (total x) * sectionFunc c d x) := (((plus f).continuous.comp (continuous_total n)).measurable.mul (section_meas ..))
private lemma tester_bound (K:ℕ) : ∃ C≥(0:ℝ), ∀ p:Cords n, ‖plus f (total p)‖ ≤ C * packing p K := by
    have hh (p : Cords n) (i) : ‖p i‖ ≤ ‖total p‖ := by
         refine (le_of_le_of_eq (by exact Finset.single_le_sum (fun j _=>norm_nonneg (p j)) (Finset.mem_univ i)) (by rw [time_equal]; rfl' : (∑ j, ‖p j‖)=time (total p))).trans ((le_abs_self (time (total p))).trans (by exact PiLp.norm_apply_le (total p) _))
    refine ⟨(orderCost (plus f) (K*n))*2^(K*n),mul_nonneg (orderCost_nonneg ..) (by positivity),fun p=> (weighted_test _ (K*n) _).trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (orderCost_nonneg ..) (by positivity))
    unfold packing weight
    rw [pow_mul,← inv_pow,show (((1+‖(total p)‖)^K)⁻¹)^n=∏ i : Fin n, (((1+‖total p‖)^K)⁻¹) by rw [Finset.prod_const,Finset.card_fin]]
    exact Finset.prod_le_prod (fun _ _=> by positivity) (fun i _=> by have := hh p i; gcongr)

lemma beam_memLp (hc : highCap c) (d) : MemLp (fun x=> plus f (total x) * sectionFunc c d x) 2 (νpow n) := by
    obtain ⟨C,hC,hB⟩:= tester_bound (n:=n) f (q+3)
    unfold sectionFunc; simp_rw [Finset.mul_sum]
    apply memLp_finsetSum _
    intro i _
    change MemLp (fun x=> plus f (total x) * termFunc c i x) 2 (νpow n)
    unfold termFunc sectionFunc.termFunc
    by_cases hi:c i=0; · simp only [hi, zero_mul,mul_zero]; exact MemLp.zero ..
    have hmi : Measurable (fun p:Cords n=>plus f (total p) * termFunc c i p) := ((plus f).continuous.measurable.comp (continuous_total n).measurable).mul (termFunc_meas c i)
    refine (memLp_two_iff_integrable_sq_norm hmi.aestronglyMeasurable).2 ?_
    have hd (j) : 0<momentDegree (i j) := Nat.pos_of_ne_zero fun hj=> hi (hc i j hj)
    have ht := fun j => divided_tail (i j) (hd j)
    have hP := Integrable.fintype_prod (fun j : Fin n=> divided_tail (i j) (hd j))
    let K := q+3; let B j (p : Cords n) := ‖dividedSlot (i j) (p j)‖
    have hyp (p : Cords n) : (packing p K)^2 * (∏ j, B j p)^2 = ∏ j, ((weight K (p j))⁻¹ * B j p)^2 := by unfold packing; simp_rw [mul_pow,Finset.prod_mul_distrib,Finset.prod_pow]
    let D (p:Cords n) := ‖plus f (total p)‖
    refine (hP.const_mul ((C*‖c i‖)^2)).mono' ((hmi.norm.pow_const 2).aestronglyMeasurable) (.of_forall (fun p=> ?_))
    unfold termFunc sectionFunc.termFunc
    rw [Real.norm_of_nonneg (by positivity : 0≤ ‖plus f (total p)*(c i*∏ l, dividedSlot (i l) (p l))‖^2),norm_mul,norm_mul, norm_prod]
    change (D p*(‖c i‖ * ∏ j, B j p))^2 ≤ (C*‖c i‖)^2 * ∏ j, ((weight K (p j))⁻¹ * B j p)^2
    rw [← hyp]; rw [← mul_pow, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) (le_trans (b:=_) (mul_le_mul_of_nonneg_right (hB p) (by exact mul_nonneg (norm_nonneg _) (by positivity))) (show _ ≤ _ from le_of_eq (by rw [mul_assoc C]; ac_rfl))) _
end YM.Trace.Shell
