import YM.Integration.WilsonPositionScaleLawGuardGradeClock
import YM.Integration.WilsonPositionScaleLawCompactNative
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawPhysicalClockRatio
open Function Filter Set Spec Table Extraction OPE Climb PhysMS Trace.Pilot Maxwell Maxwell.Free
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPositionScaleLawCompactNative (bothHomes positive)
open WilsonPositionScaleLawGuardGradeClock (age)
open scoped Topology Classical
variable [W : RangeSpec]

private theorem increment (t : Ratio) {r : ℝ} (rp : 0<r) :
    age (t.val*r) - age r = -Real.log t.val / Real.log 2 := by
  have tp := positive t
  have law : 1/(t.val*r) = (1/r)/t.val := by field_simp
  unfold age
  rw [law,Real.log_div (one_div_ne_zero rp.ne') tp.ne']
  ring

private theorem width (t : Ratio) : |Real.log t.val| ≤ |Real.log W.left| := by
  have hi := Real.log_nonpos (positive t).le t.property.2
  have lo := Real.log_le_log W.positive t.property.1
  rw [abs_of_nonpos hi,abs_of_nonpos (lo.trans hi)]
  linarith

theorem ratio (b : ℝ → ℝ) {c : ℝ} (nonzero : c ≠ 0)
    (small : Tendsto b trail (𝓝 0)) (mass : Tendsto (fun r => age r * b r) trail (𝓝 c)) :
    Tendsto (fun z : ℝ×Ratio => b z.1 / b (z.2.val*z.1)) sweep (𝓝 1) := by
  let bound := |Real.log W.left| / |Real.log 2|
  have home : Tendsto (fun z : ℝ×Ratio => z.1) sweep trail := tendsto_fst
  have rp := home.eventually (self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0))
  have error : Tendsto (fun z : ℝ×Ratio => (age (z.2.val*z.1)-age z.1) * b z.1) sweep (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero,Real.norm_eq_abs]
    have bounds : ∀ᶠ z : ℝ×Ratio in sweep,
        |(age (z.2.val*z.1)-age z.1)*b z.1| ≤ bound*|b z.1| := rp.mono (fun z pos => by
      rw [increment z.2 pos,abs_mul,abs_div,abs_neg]
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (width z.2) (abs_nonneg _)) (abs_nonneg _))
    apply squeeze_zero' (.of_forall (fun z => abs_nonneg _)) bounds
    simpa [bound] using (tendsto_const_nhds (x:=bound)).mul ((small.comp home).abs)
  have num : Tendsto (fun z : ℝ×Ratio => age (z.2.val*z.1)*b z.1) sweep (𝓝 c) := by
    have earn := (mass.comp home).add error
    rw [add_zero] at earn
    apply earn.congr
    intro z
    change age z.1 * b z.1 + _ = _
    ring
  have den := mass.comp bothHomes
  have nz : ∀ᶠ z : ℝ×Ratio in sweep, age (z.2.val*z.1)*b (z.2.val*z.1) ≠ 0 :=
    den.eventually (isOpen_ne.mem_nhds nonzero)
  have pay := num.div den nonzero
  rw [div_self nonzero] at pay
  apply pay.congr'
  filter_upwards [nz] with z ok
  change (age (z.2.val*z.1)*b z.1)/(age (z.2.val*z.1)*b (z.2.val*z.1)) = _
  field_simp [left_ne_zero_of_mul ok,right_ne_zero_of_mul ok]

variable {G : Gauge} {b g : ℝ → ℝ}
theorem anchored (simple : G.Simple) (heat : Coupling G g) {κ : ℝ} (slope : κ ≠ 0)
    (measured : Tendsto (fun r => b r / g r^2) trail (𝓝 κ)) :
    Tendsto (fun z : ℝ×Ratio => b z.1 / b (z.2.val*z.1)) sweep (𝓝 1) := by
  let c := G.slopeConstant⁻¹/Real.log 2
  have pos : 0<c := div_pos (inv_pos.mpr (Gauge.slopeConstant_pos simple)) (Real.log_pos (by norm_num))
  have running := WilsonPositionScaleLawGuardGradeClock.rate simple heat
  have nz : ∀ᶠ r in trail, g r^2 ≠ 0 :=
    (running.eventually (isOpen_ne.mem_nhds pos.ne')).mono (fun r h => right_ne_zero_of_mul h)
  have vanishes : Tendsto (fun u => g u^2) trail (𝓝 0) := by
    simpa only [zero_pow (by decide : 2≠0)] using (heat.conforms simple).pow 2
  apply ratio b (mul_ne_zero slope pos.ne')
  · have law := measured.mul vanishes
    rw [mul_zero] at law
    apply law.congr'
    filter_upwards [nz] with r h
    exact div_mul_cancel₀ _ h
  · apply (measured.mul running).congr'
    filter_upwards [nz] with r h
    calc (b r/g r^2)*(age r*g r^2) = age r*((b r/g r^2)*g r^2) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ h]

variable {C : Family G} {f : Extraction.Order} {S : Table C.book} (F : Final C f S) (J : ℝ→tower S)
theorem original (simple : G.Simple) (cal : TendC F (fun r=>J r 4) b) (heat : Coupling G g) :
    Tendsto (fun z : ℝ×Ratio => b z.1 / b (z.2.val*z.1)) sweep (𝓝 1) := by
  apply anchored simple heat _ (cal.measures g heat)
  change -(11*G.casimir/(48*Real.pi^2))/2 ≠ 0
  have hs := Gauge.casimir_pos simple
  have hp : 0 < 11*G.casimir/(48*Real.pi^2) := div_pos (mul_pos (by norm_num) hs)
    (mul_pos (by norm_num) (pow_pos Real.pi_pos _))
  exact (div_neg_of_neg_of_pos (neg_neg_of_pos hp) (by norm_num)).ne

end YM.Integration.WilsonPositionScaleLawPhysicalClockRatio
end
