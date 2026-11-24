import YM.Integration.WilsonMeasuredAdmission
import YM.OPE.Height
import YM.Work.I04

/-! Both the finer admission stop and the original bracketed Q have the
same logarithmic height as the prescribed physical length. These are scale
facts on the retained schedule, independent of field values and tests. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace YM.Integration.WilsonAdmissionHeight

open Filter Set OPE
open scoped Topology

variable {G : Gauge} (A : RG.Levels G) (hG : G.Simple)
include hG

lemma mast_log_rate : Tendsto
    (fun k => Real.log (WilsonMeasuredAdmission.mast A k) / A.S.scale k)
    atTop (𝓝 0) := by
  have hconst : Tendsto (fun k => (2 : ℝ) / A.S.scale k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop A.S.divergent
  have hupper := hconst.add (Work.I04.hat_receipt A hG).tendsto_div_nhds_zero
  rw [zero_add] at hupper
  apply squeeze_zero' ?_ ?_ hupper
  · filter_upwards [A.S.divergent.eventually_ge_atTop 0] with k hk
    exact div_nonneg (Real.log_nonneg (WilsonMeasuredAdmission.mast_gt_one A k).le) hk
  filter_upwards [A.S.divergent.eventually_ge_atTop 0] with k hk
  have h := div_le_div_of_nonneg_right
    (Real.log_le_self (WilsonMeasuredAdmission.mast_pos A k).le) hk
  simpa only [WilsonMeasuredAdmission.mast, WilsonAdmissionScale.logarithm, add_div] using h

variable {ι : Type} {l : Filter ι} {T ρ : ι → ℝ} {q : ι → ℕ}

omit hG in
private lemma height_from_log (hT : Tendsto T l atTop) (hρ : RateIs l T ρ (-1))
    (hq : Tendsto q l atTop)
    (hlog : Tendsto (fun i => Real.log (ρ i) / A.S.scale (q i)) l (𝓝 (-1))) :
    Height A.S l T q 1 := by
  have hsmall := (hρ.tends neg_one_lt_zero hT).eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hh := hρ.rate.div hlog (show (-1 : ℝ) ≠ 0 by norm_num)
  norm_num only [neg_div_neg_eq, one_div_one] at hh
  refine ⟨hq, hh.congr' ?_⟩
  filter_upwards [hρ.pos, hsmall] with i hi hs
  have hn : Real.log (ρ i) ≠ 0 := (Real.log_neg hi hs).ne
  change (Real.log (ρ i) / T i) / (Real.log (ρ i) / A.S.scale (q i)) = A.S.scale (q i) / T i
  field_simp [hn]

variable (paced : ∀ k, ((A.S.block k).val : ℝ) ≤ WilsonAdmissionScale.logarithm A k)
include paced

/-- Native Height of the constructed finer stop; no inverse price premise. -/
theorem measured_stop_height (hT : Tendsto T l atTop) (hρ : RateIs l T ρ (-1)) :
    Height A.S l T (fun i => WilsonMeasuredAdmission.stop A hG (ρ i)) 1 := by
  let m := fun i => WilsonMeasuredAdmission.stop A hG (ρ i)
  have hρ0 : Tendsto ρ l (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hρ.tends neg_one_lt_zero hT, hρ.pos⟩
  have hm : Tendsto m l atTop := (WilsonMeasuredAdmission.stop_tendsto A hG).comp hρ0
  have hs := (A.S.divergent.comp hm).eventually_gt_atTop 0
  have hsmall := (hρ.tends neg_one_lt_zero hT).eventually (gt_mem_nhds (A.S.a_pos 0))
  have hMast := (mast_log_rate A hG).comp hm
  have hlow : Tendsto
      (fun i => -1 + 5 * (Real.log (WilsonMeasuredAdmission.mast A (m i)) / A.S.scale (m i)))
      l (𝓝 (-1)) := by simpa using (hMast.const_mul 5).const_add (-1)
  have hupp : Tendsto
      (fun i => -1 + 6 * (Real.log (WilsonMeasuredAdmission.mast A (m i)) / A.S.scale (m i)))
      l (𝓝 (-1)) := by simpa using (hMast.const_mul 6).const_add (-1)
  apply height_from_log A hT hρ hm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [hρ.pos, hsmall, hs] with i hi hsmall hs
    change 0 < A.S.scale (m i) at hs
    have hw := (WilsonMeasuredAdmission.window A hG paced hi hsmall.le).1
    have hp := Real.log_le_log (mul_pos (A.S.a_pos (m i))
      (pow_pos (WilsonMeasuredAdmission.mast_pos A (m i)) _)) hw
    rw [Real.log_mul (A.S.a_pos (m i)).ne'
      (pow_pos (WilsonMeasuredAdmission.mast_pos A (m i)) _).ne', Real.log_pow] at hp
    have ha : Real.log (A.S.a (m i)) = -A.S.scale (m i) := by simp [Schedule.scale]
    rw [ha] at hp
    have hd := div_le_div_of_nonneg_right hp hs.le
    simpa only [add_div, neg_div, div_self hs.ne', mul_div_assoc, Nat.cast_ofNat] using hd
  filter_upwards [hρ.pos, hsmall, hs] with i hi hsmall hs
  change 0 < A.S.scale (m i) at hs
  have hw := (WilsonMeasuredAdmission.window A hG paced hi hsmall.le).2
  have hp := Real.log_le_log hi hw
  rw [Real.log_mul (A.S.a_pos (m i)).ne'
    (pow_pos (WilsonMeasuredAdmission.mast_pos A (m i)) _).ne', Real.log_pow] at hp
  have ha : Real.log (A.S.a (m i)) = -A.S.scale (m i) := by simp [Schedule.scale]
  rw [ha] at hp
  have hd := div_le_div_of_nonneg_right hp hs.le
  simpa only [add_div, neg_div, div_self hs.ne', mul_div_assoc, Nat.cast_ofNat] using hd

/-- Every original Q satisfying the native enclosing bracket has the same
height. No new crossing-index choice replaces that Q. -/
theorem original_height (hT : Tendsto T l atTop) (hρ : RateIs l T ρ (-1))
    (hbracket : ∀ᶠ i in l, A.S.a (q i + 1) < ρ i ∧ ρ i ≤ A.S.a (q i)) :
    Height A.S l T q 1 := by
  have hρ0 := hρ.tends neg_one_lt_zero hT
  have hq : Tendsto q l atTop := by
    apply tendsto_atTop.mpr
    intro Q
    filter_upwards [hbracket, hρ0.eventually (gt_mem_nhds (A.S.a_pos Q))] with i hi hsmall
    by_contra! h
    have ha := A.S.strictAnti.antitone (show q i + 1 ≤ Q by omega)
    linarith
  have hs := (A.S.divergent.comp hq).eventually_gt_atTop 0
  have hβ := (Work.I04.hat_receipt A hG).tendsto_div_nhds_zero.comp hq
  have hlow : Tendsto
      (fun i => -1 - Real.log (A.clock.hatBeta (q i)) / A.S.scale (q i))
      l (𝓝 (-1)) := by simpa using tendsto_const_nhds.sub hβ
  apply height_from_log A hT hρ hq
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [hρ.pos, hbracket, hs] with i hi hbr hs
    change 0 < A.S.scale (q i) at hs
    have hβpos : 0 < A.clock.hatBeta (q i) := zero_lt_one.trans (A.fits.delayed _)
    have hblock : ((A.S.block (q i)).val : ℝ) ≤ A.clock.hatBeta (q i) :=
      (paced _).trans (Real.log_le_self hβpos.le)
    have hnext : A.S.a (q i) / A.clock.hatBeta (q i) ≤ A.S.a (q i + 1) := by
      rw [A.S.a_step]
      exact div_le_div_of_nonneg_left (A.S.a_pos _).le (by positivity) hblock
    have hp := Real.log_le_log (div_pos (A.S.a_pos _) hβpos) (hnext.trans hbr.1.le)
    rw [Real.log_div (A.S.a_pos _).ne' hβpos.ne'] at hp
    have ha : Real.log (A.S.a (q i)) = -A.S.scale (q i) := by simp [Schedule.scale]
    rw [ha] at hp
    have hd := div_le_div_of_nonneg_right hp hs.le
    simpa only [sub_div, neg_div, div_self hs.ne'] using hd
  filter_upwards [hρ.pos, hbracket, hs] with i hi hbr hs
  change 0 < A.S.scale (q i) at hs
  have hp := Real.log_le_log hi hbr.2
  have ha : Real.log (A.S.a (q i)) = -A.S.scale (q i) := by simp [Schedule.scale]
  rw [ha] at hp
  have hd := div_le_div_of_nonneg_right hp hs.le
  simpa only [neg_div, div_self hs.ne'] using hd

end YM.Integration.WilsonAdmissionHeight
