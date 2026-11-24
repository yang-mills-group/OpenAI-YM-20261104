import YM.Integration.WilsonThermometerPositionFilmReassembled
import YM.Integration.WilsonThermometerPositionFilmCubicGeometry
import YM.Integration.WilsonThermometerPositionFilmUpperTerms

/-! On the true translated fine marginal the entire ground is the finite exponential of the upper connected table. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmAngularGround
open Function Filter MeasureTheory RG Lattice Tree Wilson Exterior Precision Marker Multi Comparison.RG02
open Comparison.RG02.Order Comparison.RG02.Assembly QuadraticLocal.Mentor
open QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Extra.Trajectories Primitives.GCC.Anchor RegulatorIR.FVAAlt2.Booth
open WilsonThermometerPositionFilmCloudReading WilsonThermometerPositionFilmCubicGeometry
open WilsonThermometerPositionFilmChartContact
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} {c f:Side} {S:StepData c f} (F:Forest S.ratio)

private def chart (w:Bulk.Joint S F (G:=G)) : ℝ × fieldDir G f 1 := (w.1,Work.F03.axisLog F w.2)

private theorem head {k:ℕ} {z:ℝ → Config G f → ℂ} (h:GradeAt k (Bulk.projected z)) (u:Bulk.SliceDir S F G) :
    Assembly.jet (Bulk.posed S F z) k (1,u)=Assembly.jet (Bulk.projected z) k (1,direction F u) := by
  have zero:Work.F03.axisLog F (0:Bulk.SliceDir S F G)=0:=congrArg Prod.snd (Work.F03.inclusion_zero F)
  have smooth:ContDiffAt ℝ ω (Work.F03.axisLog F (G:=G)) 0:=(Work.F03.inclusion_smooth F).snd
  have lift:ContDiffAt ℝ ω (chart F (G:=G)) 0:=contDiffAt_fst.prodMk (smooth.comp (0:Bulk.Joint S F (G:=G)) contDiffAt_snd)
  have mount:chart F (0:Bulk.Joint S F (G:=G))=0:=Prod.ext rfl zero
  have localEq:Bulk.projected z ∘ chart F =ᶠ[𝓝 0] Bulk.posed S F z:=by
    have prior:=continuous_snd.tendsto (0:Bulk.Joint S F (G:=G))
    filter_upwards [prior.eventually (Work.F03.inclusion_works F)] with v h
    exact congrArg (z v.1) h
  let T:=Bulk.SliceDir S F G
  have sndAt:HasFDerivAt (Prod.snd : ℝ × T → T) (ContinuousLinearMap.snd ℝ ℝ T) 0:=hasFDerivAt_snd
  have fstAt:HasFDerivAt (Prod.fst : ℝ × T → ℝ) (ContinuousLinearMap.fst ℝ ℝ T) 0:=hasFDerivAt_fst
  have angAt:HasFDerivAt (Work.F03.axisLog F (G:=G)) (fderiv ℝ _ 0) (Prod.snd (0 : ℝ × T)):=
    (smooth.differentiableAt (by simp)).hasFDerivAt
  have derivative:=fstAt.prodMk (angAt.comp (f:=(Prod.snd : ℝ × T → T)) 0 sndAt)
  have curve:=WilsonThermometerPositionFilmContactHead.tangent h lift mount (1,u)
  change HasFDerivAt (chart F (G:=G)) _ 0 at derivative
  rw [derivative.fderiv] at curve
  calc
    Assembly.jet (Bulk.posed S F z) k (1,u)=Assembly.jet (Bulk.projected z ∘ chart F) k (1,u):=by
      unfold Assembly.jet;rw [(localEq.iteratedFDeriv ℝ k).eq_of_nhds]
    _ = _ := curve

variable {V:Type} [Fintype V] [DecidableEq V] {R:Census V} (C:Bulk.Colors R G f)
  (hw:∀t,GradeAt (C.power t) (Bulk.projected (C.mark t)))

include hw in
theorem original (s:R.Mode) (u:Bulk.SliceDir S F G):
    bent S F C s 0 u=(Air.discharge C 0 (direction F u)).pass.part s:=by
  let a:=curve C.power (Bulk.markFn S F C) (1,u)
  let z:=series R 1 a
  have sym:Symmetric z:=⟨a,rfl⟩
  have blank:z.part (Board R 1).quiet=0:=mark_books C.power (Bulk.markFn S F C) (1,u) 1
  have full:=mark_exp (r:=1) (mark_curve_quiet C.power (Bulk.markFn S F C) (1,u))
  have hc:PowerSeries.coeff 0 a=Air.discharge C 0 (direction F u):=by
    simp only [a,curve,PowerSeries.coeff_mk,Air.discharge,markLetter,Nat.add_zero]
    congr 1
    exact funext (fun i=>head F (hw i) u)
  have ink:First.buc z=Air.discharge C 0 (direction F u):=(observation R 1 a (by decide : 0≤1)).trans hc
  change (PowerSeries.coeff 0 (markExp a)).part s=_
  rw [←observation R 1 (markExp a) (by decide : 0≤1),full]
  change (First.buc (Poly.pass z)).part s=_
  rw [First.buc_pass sym blank,ink]

variable {clip:Clip} {P:PathData G} {O:ChartRatio G} (K:Bulk.Kernel S clip P O) (tag:S.Choices)
include hw in
theorem received (s:R.Mode)(x:fieldDir G c 1)(z:Precision.Key F G→ℝ):
    paid K F tag C s x 0 z=(Air.discharge C 0 (direction F (Bulk.translated K F x z).2)).pass.part s:=
  (ground K F tag C s x z).trans (original F C hw s _)

end YM.Integration.WilsonThermometerPositionFilmAngularGround
end
