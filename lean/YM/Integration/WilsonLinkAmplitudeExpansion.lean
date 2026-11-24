import YM.Integration.WilsonLinkAmplitudeChart

/-! The asymptotic series of the genuine normalized Wilson expectation of a smooth signed link test. -/
noncomputable section
namespace YM.Integration.WilsonLinkAmplitudeExpansion
open YM RG RG02 Lattice Wilson Filter MeasureTheory Metric Precision PowerSeries
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open PertExtension.Series.Radial RG02.Asym RG02.Therm WilsonLinkAmplitudeChart
open scoped ContDiff Topology BigOperators
variable {G : Gauge} {c f : Side} (S : StepData c f)

def rawSeries (P : ChartRatio G) (w : Friction.W G → ℝ) : PowerSeries ℂ :=
  C (Complex.ofReal (Therm.leading (Friction.Γ S G) (Friction.rate G) 0)) *
    Therm.shuttle (Friction.Γ S G) (Friction.hinge S) (amplitude P w) 0

theorem numerator (P : ChartRatio G) (hP : LocalRatio P)
    (w : Friction.W G → ℝ) (cw : Continuous w)
    (hw : ContDiffAt ℝ ∞ (fun u : Friction.E G => w (expLinks G Unit u)) 0) :
    Near (fun t => ((t:ℂ)^Friction.cardinal G)⁻¹ *
      ↑(∫ x, weighted S w t x ∂Friction.roll G)) (rawSeries S P w) := by
  have hh : Measurable (Friction.hinge S (G:=G)) := by
    unfold Friction.hinge Friction.jetBase
    fun_prop
  have hm : Measurable (amplitude P w) :=
    (Complex.continuous_ofReal.measurable.comp ((Chart.Ratio.jacobian_meas hP).comp measurable_snd)).mul
      (Complex.continuous_ofReal.measurable.comp
        (cw.measurable.comp ((Chart.expLinks_meas (G:=G)).comp measurable_snd)))
  have hj : ContDiffAt ℝ ∞ (amplitude P w) 0 :=
    (Friction.costs P hP).mul (Complex.ofRealCLM.contDiff.contDiffAt.comp _
      (hw.comp (f:=Prod.snd) (0 : ℝ × Friction.E G) contDiffAt_snd))
  obtain ⟨r,hr,H⟩ := Therm.transmission (Friction.direction S G) (Friction.rate G) hh hj hm
  let a := min r (small G P/2)
  have hb : 0<a := lt_min hr (half_pos (Chart.Ratio.small_pos hP))
  have hE : a<small G P := (min_le_right ..).trans_lt (half_lt_self (Chart.Ratio.small_pos hP))
  have ht := (H (fun t => disc t a) ((Therm.Collars.body hb).raise (min_le_left r _))).2
  let U := chamber G Unit a
  have hv : Near (fun t => ((t:ℂ)^Friction.cardinal G)⁻¹ *
      ↑(∫ x in U, weighted S w t x ∂Friction.roll G)) _ :=
    Near.same ht (Tested.eventually_pos.mono fun t h => (inner S P hP w cw h hb hE).symm)
  intro n
  convert! bill_add (hv n) (outer S P hP w cw hb hE (n+1)) using 1
  funext t
  have hI : Integrable (weighted S w t) (Friction.roll G) :=
    ((Friction.line S t).mul cw).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [Pi.sub_apply,Pi.add_apply,← integral_add_compl (μ:=Friction.roll G) (s:=U)
    (Chart.Ratio.chamber_open hP hE.le|>.measurableSet)
    hI]
  simp only [Complex.ofReal_add,mul_add,Pi.sub_apply,rawSeries]
  abel

def mean (w : Friction.W G → ℝ) (t : ℝ) : ℂ :=
  ↑(∫ x, weighted S w t x ∂Friction.roll G) / Complex.ofReal (S.penaltyZ (t^2)⁻¹ G)

def normalizedSeries (P : ChartRatio G) (w : Friction.W G → ℝ) : PowerSeries ℂ :=
  rawSeries S P w * (Friction.paidSeries S P)⁻¹

theorem normalized (P : ChartRatio G) (hP : LocalRatio P)
    (w : Friction.W G → ℝ) (cw : Continuous w)
    (hw : ContDiffAt ℝ ∞ (fun u : Friction.E G => w (expLinks G Unit u)) 0) :
    Near (mean S w) (normalizedSeries S P w) := by
  have hz : coeff 0 (Friction.paidSeries S P) ≠ 0 := by
    rw [Friction.paid_base S P hP]
    exact Complex.ofReal_ne_zero.mpr (mul_pos (Therm.leading_pos ..) hP.scale).ne'
  apply Near.same (Near.mult (numerator S P hP w cw hw) (Near.fine_inverse (Friction.restored S P hP) hz))
  filter_upwards [Tested.eventually_pos] with t ht
  change (((t:ℂ)^Friction.cardinal G)⁻¹ * ↑(∫ x, weighted S w t x ∂Friction.roll G)) *
    (((t:ℂ)^Friction.cardinal G)⁻¹ * ↑(S.penaltyZ (t^2)⁻¹ G))⁻¹ = _
  unfold mean
  have htC := Complex.ofReal_ne_zero.mpr ht.ne'
  field_simp

end YM.Integration.WilsonLinkAmplitudeExpansion
