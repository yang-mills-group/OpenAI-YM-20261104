import YM.SchemeRG11.Bubble.Fiber

/-! Integrable bounds after Taylor split. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.SchemeRG11.Bubble
open Function Set MeasureTheory Filter Metric Asymptotics Hot
open scoped Topology ContDiff
local notation "W" => ℝ × ℝ

local notation "volt" => (volume:Measure W)
lemma billets (s t : Set ℝ) : (volume:Measure W).restrict (s ×ˢ t) = (volume.restrict s).prod (volume.restrict t) := (Measure.prod_restrict ..).symm

variable {w : ℝ→ℂ} (hw : Continuous w) (j : Bool) {P : ℂ→ℝ→ℂ} {D : ℂ→ℂ} {C H R : ℝ} (hC : 0<C)
  (hw' : ∀ t∈slab, ‖w t‖ ≤ C)

lemma limit_w (hw : Continuous w) : ∃ C>0, ∀ t∈slab, ‖w t‖ ≤ C := by
  obtain ⟨C,hC⟩:= (isCompact_Icc (a:=(0:ℝ)) (b:=1)).exists_bound_of_continuousOn hw.continuousOn
  exact ⟨1+|C|,by positivity,fun t ht=> (hC t (Ioc_subset_Icc_self ht)).trans (by linarith [le_abs_self C])⟩

include hw' hC in
lemma estimate_small {z : ℂ} (hH : 0<H) (hh : Ticket (P z) (D z) R H) {p : W} (hp : p∈stem) :
    ‖purse w P D j z p‖ ≤ (C*H) * p.1^z.re := by
  have ht:= (show p.1∈slab from hp.1)
  have h := precis hp.2 ht.1
  have hq : halo p ∈ Icc 0 1 := ⟨h.1,h.2.trans ht.2⟩
  have hk := (hh.curve _ hq)
  have hu := hh.ray _ hq
  rw [purse,norm_mul,carrier,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
  have ht' :0<p.1:=ht.1
  grw [hw' _ hp.2]
  have hs : 0≤halo p:=hq.1
  have hx (n : ℕ) : p.1^(z.re-(n:ℝ))*p.1^n = p.1^z.re := by rw [← Real.rpow_natCast,← Real.rpow_add ht',sub_add_cancel]
  cases j
  · simp only [localTerms,Bool.false_eq_true,↓reduceIte, add_zero]
    grw [hu,h.2]; simp only [phase,index,Complex.sub_re,Nat.cast_zero,Complex.one_re,sub_zero]; linear_combination C * H * (by simpa using hx 1 : p.1^(z.re-1)*p.1 = p.1^z.re)
  simp only [localTerms,↓reduceIte]
  grw [hk,h.2]; simp only [phase,index,Complex.sub_re,Nat.cast_one,Complex.one_re]
  rw [show z.re-1-1=z.re-2 by ring]; linear_combination C*H*(by exact_mod_cast hx 2 : p.1^(z.re-2)*p.1^2=p.1^z.re)

include hw' hC in
lemma estimate_foil {A B : ℝ} {z : ℂ} (hH : 0<H) (hh : Ticket (P z) (D z) (A+B) H) (n : ℕ) (hn : z.re-1 ≤ (n:ℝ)) {p : W} (hp : p∈foil A B) :
    ‖pouch w P j z p‖ ≤ C*H*(A+B)^n := by
  have hv:=foil_span A B hp
  have ht : p.1∈Ioc 1 (A+B):=hv.1
  have ht':0<p.1:=lt_trans zero_lt_one ht.1
  have h:=precis hv.2 ht'
  have hh': p.1^(phase j z).re ≤ (A+B)^n := by
    have hh' : (phase j z).re ≤ n := (sub_le_self (z.re-1) (show 0 ≤ (index j : ℝ) by positivity)).trans hn |>.trans_eq ?_
    · refine (Real.rpow_le_rpow_of_exponent_le ht.1.le hh').trans ?_; rw [Real.rpow_natCast]; exact pow_le_pow_left₀ ht'.le ht.2 _
    rfl
  rw [pouch,carrier,norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht']
  grw [hw' _ hv.2,hh.body _ ⟨h.1,h.2.trans ht.2⟩,hh']; exact le_of_eq (by ring)

lemma pay_rpow (α : ℝ) (h : -1<α) : IntegrableOn (fun p:W=> p.1^α) stem := by
  unfold IntegrableOn stem
  rw [billets]
  have he:= ((intervalIntegral.intervalIntegrable_rpow' h (a:=0) (b:=1)).1).mul_prod (integrableOn_const (s:=slab) (μ:=volume) (C:=(1:ℝ)) (by simp [slab]))
  simpa only [mul_one,slab] using he

include hw
lemma till (hh : Glaze P D) (α : ℝ) (hα : -1<α) {U : Set ℂ} (hk : IsCompact U) (ht : ∀ z∈U, α≤z.re) :
    ∃ b : W→ℝ, IntegrableOn b stem ∧ ∀ z∈U, ∀ p∈stem, ‖purse w P D j z p‖ ≤ b p := by
  obtain ⟨C,hC,hW⟩:=limit_w hw; obtain ⟨H,hH,hP⟩:=hh.bills 1 le_rfl _ hk
  exact ⟨_, (pay_rpow α hα).const_mul (C*H), fun z hz p hp=> (estimate_small j hC hW hH (hP z hz) hp).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hp.1.1 hp.1.2 (ht z hz)) (by positivity))⟩
lemma trawl (hh : Glaze P D) (A B : ℝ) (ha : 1≤A+B) {U : Set ℂ} (hk : IsCompact U) :
    ∃ b : W→ℝ, IntegrableOn b (foil A B) ∧ ∀ z∈U, ∀ p∈foil A B, ‖pouch w P j z p‖ ≤ b p := by
  obtain ⟨n,hn⟩:=enough hk
  obtain ⟨C,hC,hW⟩:=limit_w hw; obtain ⟨H,hH,hP⟩:=hh.bills _ ha _ hk
  refine ⟨_,integrableOn_const (C:=C*H*(A+B)^(n+1)) (fpaid A B).ne, fun z hz p hp=>estimate_foil j hC hW hH (hP z hz) _ ?_ hp⟩
  have hh:=(hn z hz).2; push_cast; linarith
lemma pocket (hh : Glaze P D) {z : ℂ} (hz : -1<z.re) : IntegrableOn (purse w P D j z) stem := by
  obtain ⟨b,h,e⟩:= till hw j hh z.re hz (isCompact_singleton (x:=z)) (fun v hv=> by rw [mem_singleton_iff.mp hv])
  exact Integrable.mono' h ((purse_on j hh hw z).aestronglyMeasurable stem_meas) (ae_restrict_of_forall_mem stem_meas (e z rfl))
lemma palm (hh : Glaze P D) {A B : ℝ} (ha : 1≤A+B) (z : ℂ) : IntegrableOn (pouch w P j z) (foil A B) := by
  obtain ⟨b,h,e⟩:= trawl hw j hh A B ha (isCompact_singleton (x:=z))
  exact Integrable.mono' h ((pouch_on j hh hw z A B).aestronglyMeasurable (foil_meas ..)) (ae_restrict_of_forall_mem (foil_meas ..) (e z rfl))

end YM.SchemeRG11.Bubble
