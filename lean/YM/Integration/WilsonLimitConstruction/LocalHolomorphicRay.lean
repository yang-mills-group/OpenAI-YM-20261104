import YM.Integration.WilsonLimitConstruction.FundedWilsonMeasure
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Complex disks in normalized real rays of a fixed native local
power series. The disk and norm bound belong to the local field before
it is placed on a lattice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.LocalHolomorphicRay

open Filter Metric Set
open scoped Topology ContDiff NNReal ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}

structure Sheet (f : E → ℝ) where
  series : FormalMultilinearSeries ℝ E ℝ
  radius : ℝ≥0
  radius_pos : 0 < radius
  constant : ℝ
  positive : 0 < constant
  realSeries : HasFPowerSeriesOnBall f series 0 radius
  bound k : ‖series k‖ * (radius : ℝ)^k ≤ constant

theorem purchase (hf : AnalyticAt ℝ f 0) : Nonempty (Sheet f) := by
  obtain ⟨p,R,h⟩ := hf
  obtain ⟨r,hr,hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h.r_pos
  obtain ⟨C,hC,hb⟩ := p.norm_mul_pow_le_of_lt_radius (hrR.trans_le h.r_le)
  exact ⟨⟨p,r,ENNReal.coe_pos.mp hr,C,hC,h.mono hr hrR.le,hb⟩⟩

def coefficient (S : Sheet f) (a : E) (k : ℕ) : ℝ := S.series k (fun _ => a)

theorem coefficient_bound (S : Sheet f) {a : E} (ha : ‖a‖ ≤ 1) (k : ℕ) :
    ‖coefficient S a k‖ * (S.radius:ℝ)^k ≤ S.constant := by
  have hd : ‖coefficient S a k‖ ≤ ‖S.series k‖ := by
    calc _ ≤ ‖S.series k‖ * ‖a‖^k := by simpa [coefficient] using (S.series k).le_opNorm (fun _ => a)
         _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) ha)
  exact (mul_le_mul_of_nonneg_right hd (by positivity)).trans (S.bound k)

def complexSeries (S : Sheet f) (a : E) : FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars ℂ (fun k => (coefficient S a k : ℂ))

theorem complex_radius (S : Sheet f) {a : E} (ha : ‖a‖ ≤ 1) :
    (S.radius : ℝ≥0∞) ≤ (complexSeries S a).radius := by
  apply FormalMultilinearSeries.le_radius_of_bound _ S.constant
  intro k
  simpa [complexSeries,FormalMultilinearSeries.ofScalars_norm] using coefficient_bound S ha k

theorem complex_disc (S : Sheet f) {a : E} (ha : ‖a‖ ≤ 1) :
    HasFPowerSeriesOnBall (complexSeries S a).sum (complexSeries S a) 0 S.radius :=
  let hr := ENNReal.coe_pos.mpr S.radius_pos
  ((complexSeries S a).hasFPowerSeriesOnBall (hr.trans_le (complex_radius S ha))).mono hr
    (complex_radius S ha)

theorem real_axis (S : Sheet f) {a : E} (ha : ‖a‖ ≤ 1)
    {t : ℝ} (ht : ‖t‖ < (S.radius : ℝ)) :
    (complexSeries S a).sum (t:ℂ) = (f (t • a) : ℂ) := by
  have ht' : ‖t • a‖ < (S.radius:ℝ) := by
    rw [norm_smul]
    exact (mul_le_of_le_one_right (norm_nonneg _) ha).trans_lt ht
  have hR := S.realSeries.hasSum (y := t • a)
    (by simpa only [Metric.eball_coe,Metric.mem_ball,dist_zero_right] using ht')
  have hterm (k : ℕ) : S.series k (fun _ => t • a) = t^k * coefficient S a k := by
    simpa [coefficient,smul_eq_mul] using
      (S.series k).toMultilinearMap.map_smul_univ (fun _ : Fin k => t) (fun _ => a)
  rw [zero_add] at hR
  simp_rw [hterm] at hR
  have hc := (complex_disc S ha).hasSum (y := (t:ℂ))
    (by simpa only [Metric.eball_coe,Metric.mem_ball,dist_zero_right,Complex.norm_real] using ht)
  rw [zero_add] at hc
  have cast := (RCLike.hasSum_ofReal ℂ).mpr hR
  change HasSum (fun k => Complex.ofReal (t^k * coefficient S a k)) (f (t • a) : ℂ) at cast
  simp only [Complex.ofReal_mul,Complex.ofReal_pow] at cast
  apply hc.unique
  simpa only [complexSeries,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,mul_comm] using cast

theorem projector (S : Sheet f) {a : E} (ha : ‖a‖ ≤ 1) (k : ℕ) :
    iteratedDeriv k (complexSeries S a).sum 0 / (k.factorial : ℂ) = coefficient S a k := by
  have h := (complex_disc S ha).hasFPowerSeriesAt
  have he := h.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries h
  simpa only [complexSeries,FormalMultilinearSeries.coeff_ofScalars] using
    congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff k) he

theorem prior (G : Gauge) : Nonempty (Sheet (PertExtension.Chart.fee (XSpace.Bare.chart G))) := by
  obtain ⟨p,r,hr,hd,⟨C,hC,hb⟩,_⟩ := FundedWilsonMeasure.link G
  exact ⟨⟨p,r,hr,C,hC,hd,hb⟩⟩

end YM.Integration.WilsonLimitConstruction.LocalHolomorphicRay
end
