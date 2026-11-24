import YM.Contact.Dilation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Integrable majorants for subtraction radii which in the scaling variable may cover a large ball. Account for both the inner remainder (one extra power) and the outer Taylor test by itself (at most polynomial of the subtracted order). -/

set_option autoImplicit false
noncomputable section
open Set Function Filter MeasureTheory LinearMap TopologicalSpace
open scoped BigOperators Topology Classical ContDiff
namespace YM.Contacts.Patch
noncomputable section
variable {A B:Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable [FiniteDimensional ℝ A][MeasureSpace A][BorelSpace A][μ : (volume:Measure A).IsAddHaarMeasure]
omit [FiniteDimensional ℝ A] μ in
lemma exterior_power_meas (p R:ℝ):Measurable (fun x:A=> (Ioi R).indicator (fun r:ℝ=> Real.rpow r p) ‖x‖) := ((measurable_id.pow_const p).indicator measurableSet_Ioi).comp continuous_norm.measurable

lemma exterior_power {p R:ℝ}(hR:0<R) (hd:0<normal A)(hp : p < -(normal A:ℝ)): Integrable (fun x:A=> (Ioi R).indicator (fun r=> Real.rpow r p) ‖x‖):=by
     let E:= (normal A:ℤ)-1; let q:= (E:ℝ)+p
     have hd' : q < -1 := by unfold q E;push_cast; linarith
     have hn: (Module.finrank ℝ A - 1:ℕ) = (E:ℝ):=by dsimp [normal] at hd; dsimp [normal,E]; push_cast [Nat.le_of_lt_succ];exact_mod_cast (Nat.cast_sub (by omega))
     have _h : Nontrivial A:= Module.nontrivial_of_finrank_pos hd
     have hx:Integrable ((Ioi R).indicator (fun r:ℝ=> Real.rpow r q)):= (integrableOn_Ioi_rpow_of_lt hd' hR).integrable_indicator measurableSet_Ioi
     refine (integrable_fun_norm_addHaar volume).mpr (IntegrableOn.congr_fun hx.integrableOn ?_ measurableSet_Ioi)
     intro y hy; dsimp only [indicator];split_ifs;have hy':y>0:=hy
     change y^q = y ^ (Module.finrank ℝ A - 1) * (y^p)
     rw [← Real.rpow_natCast _ (Module.finrank ℝ A -1),hn,←Real.rpow_add hy']
     exact (smul_zero _).symm
open Metric
/-- Unit kernel majorant on inner and outer regions. `m.toNat`: avoid casting a negative `m` when using the integrable tail. -/
def force (A:Type*) [NormedAddCommGroup A] (R:ℝ)(p:ℝ)(m:ℤ)(x:A):ℝ:= if x∈closedBall 0 R then (‖x‖^(p+((m+1).toNat:ℕ))) else (if m<0 then 0 else ‖x‖^(p+(m.toNat:ℕ)))
omit [NormedSpace ℝ A] [FiniteDimensional ℝ A] [MeasureSpace A] [BorelSpace A] μ in
lemma force_inside {R p:ℝ}{m:ℤ}{x:A}(hx:‖x‖ ≤ R):force A R p m x=‖x‖^(p+((m+1).toNat:ℕ)):=if_pos (mem_closedBall_zero_iff.mpr hx)
omit [NormedSpace ℝ A] [FiniteDimensional ℝ A] [MeasureSpace A] [BorelSpace A] μ in
lemma force_nonneg (R p m) (x:A): force A R p m x≥0:=by unfold force;split_ifs <;> positivity
lemma integrable_force {R p:ℝ}{m:ℤ}(hR:R>0)(h:0 < normal A)(hm:-(normal A:ℝ)<p+((m+1).toNat:ℕ)) (hh: m<0 ∨ p+m.toNat < -(normal A:ℝ)): Integrable (force A R p m) := by
    by_cases hv:m<0
    · convert (bound_power h _ hm R) using 1; ext x
      by_cases hh:x∈closedBall 0 R <;> simp [force,hv,indicator,hh]
    have hw:=hh.resolve_left hv
    let b:=fun x:A=> (Ioi R).indicator (fun r=> Real.rpow r (p+m.toNat)) ‖x‖
    have hb:Integrable b:=exterior_power hR h hw
    convert! ((bound_power h _ hm R).add hb) using 1; ext x
    by_cases hh:x∈closedBall 0 R <;> dsimp only [force,b,indicator,Pi.add_apply]
    · rw [if_pos hh,if_pos hh,if_neg (by simpa only [mem_Ioi,not_lt] using mem_closedBall_zero_iff.mp hh),add_zero]
    rw [if_neg hh,if_neg hh,if_neg hv,if_pos (show ‖x‖ ∈ Ioi R from not_le.mp (mem_closedBall_zero_iff.not.mp hh)),zero_add];rfl
omit [NormedSpace ℝ A] [FiniteDimensional ℝ A] [MeasureSpace A] [BorelSpace A] μ in
lemma force_outside {R p:ℝ}{m:ℤ}{x:A}(hx:R<‖x‖)(hm:0≤m):force A R p m x=‖x‖^(p+m.toNat):= (if_neg fun he=>hx.not_ge (mem_closedBall_zero_iff.mp he)).trans (if_neg hm.not_gt)

omit [FiniteDimensional ℝ A] [MeasureSpace A] [BorelSpace A] μ in
private lemma outer_poly {m:ℤ}(φ:Trial A)(i:ℕ)(hi:i≤m.toNat){y:A}{q:ℝ}(hy:1≤‖y‖)(hq:Major (m+1).toNat φ q):‖jet i φ 0 y‖≤ ‖y‖^m.toNat*q:=by
    apply (norm_jet hq (show i≤(m+1).toNat from hi.trans (by omega)) ..).trans
    rw [sub_zero];exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hy hi) hq.nonneg

set_option maxHeartbeats 400000 in
omit [FiniteDimensional ℝ A] [MeasureSpace A] [BorelSpace A] μ in
lemma powerRow {φ:Trial A}{R p d r:ℝ}{m:ℤ}(hR:1≤R)(hr:1≤r)(hφ:(Function.support (⇑φ)) ⊆ Metric.closedBall 0 R)(hd:Major (m+1).toNat φ d){x:A}(hx:x≠0):
    ‖remainder r m φ x‖ * (‖x‖^p) ≤ ((((m+1).toNat:ℝ)+1)*d) * force A R p m x:=by
    let t:ℕ:=(m+1).toNat; let U:=(t+1:ℝ)*d
    have h0 : (1:ℝ) ≤ t+1:= by exact_mod_cast Nat.le_add_left 1 t
    have ht:0<r:=zero_lt_one.trans_le hr
    have hm:m.toNat ≤ t:=by omega
    have hp(s:1≤‖x‖):‖polynomial m.toNat φ 0 x‖ ≤ (m.toNat+1:ℝ)*(‖x‖^m.toNat*d):= by
       unfold polynomial; refine (norm_sum_le ..).trans ?_
       have he' := Finset.sum_le_card_nsmul _ _ _ (fun i hi=>outer_poly (m:=m) φ i (Finset.mem_range_succ_iff.mp hi) s hd)
       simpa only [nsmul_eq_mul,Finset.card_range,Nat.cast_add,Nat.cast_one,Nat.cast_succ] using! he'
    have hc:∀ z:ℂ, ‖chi (E:=A) r x • z‖≤‖z‖:=fun z=> (norm_smul ..|>.trans (congrArg₂ HMul.hMul (Real.norm_of_nonneg (chi_nonneg ..)) (Eq.refl ‖z‖))).trans_le (mul_le_of_le_one_left (norm_nonneg z) (chi_le_one r x))
    by_cases hh:‖x‖ ≤ R
    · rw [force_inside hh]
      suffices hg:‖remainder r m φ x‖ ≤ U*(‖x‖^t) by
           rw [Real.rpow_add (norm_pos_iff.mpr hx),Real.rpow_natCast,mul_comm (‖x‖^p),←mul_assoc];exact mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg (norm_nonneg _) _)
      by_cases hw:‖x‖≤r
      · exact (remainder_near _ ht hd _ hw).trans (by rw [mul_comm];exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hd.nonneg h0) (by positivity))
      by_cases hj:m<0
      · rw [remainder,taylorCut,if_neg (not_le.mpr hj),sub_zero,show ‖x‖^t=(1:ℝ) by simp only [show t=0 from by omega,pow_zero],mul_one];exact (hd.value ..).trans (le_mul_of_one_le_left hd.nonneg h0)
      rw [remainder,taylorCut,if_pos (not_lt.mp hj)];apply (norm_sub_le ..).trans
      have hx' : 1≤‖x‖:=hr.trans (not_le.mp hw).le
      refine (add_le_add (hd.value x) ((hc _).trans (hp hx'))).trans ?_
      dsimp [U]; have H:‖x‖^m.toNat ≤ ‖x‖^t:=pow_le_pow_right₀ hx' hm
      calc
        _ = d*(1+(m.toNat+1:ℝ)*‖x‖^m.toNat):=by ring
        _ ≤ _ := by
                        rw [mul_comm (t+1:ℝ),mul_assoc]; apply mul_le_mul_of_nonneg_left _ hd.nonneg
                        have ht': (m.toNat+1:ℝ) = t:=by exact_mod_cast (show m.toNat+1=t from by omega)
                        nlinarith only [H,(show 1 ≤ ‖x‖^t from one_le_pow₀ hx'),ht'] -- simpler rewrite
    · have hm':φ x=0:=notMem_support.mp fun e=>hh (mem_closedBall_zero_iff.mp (hφ e))
      rw [remainder,hm',taylorCut]
      have he:0≤force A R p m x:=force_nonneg ..
      split_ifs with h'
      · have hx':1≤‖x‖ := hR.trans (not_le.mp hh).le
        rw [zero_sub,norm_neg,force_outside (not_le.mp hh) h',Real.rpow_add (norm_pos_iff.mpr hx),Real.rpow_natCast,mul_comm (‖x‖^p),←mul_assoc]
        refine mul_le_mul_of_nonneg_right ((hc _).trans ((hp hx').trans ?_)) (Real.rpow_nonneg (norm_nonneg _) _); rw [mul_comm (_^_:ℝ),←mul_assoc];exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (add_le_add_left (Nat.cast_le (α:=ℝ).mpr hm) _) hd.nonneg) (by positivity)
      simp only [sub_zero,norm_zero,zero_mul];exact mul_nonneg (mul_nonneg (by positivity) hd.nonneg) he
end
end YM.Contacts.Patch
