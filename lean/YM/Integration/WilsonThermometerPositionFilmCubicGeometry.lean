import YM.Integration.WilsonThermometerPositionFilmContactHead
import YM.Integration.WilsonThermometerPositionFilmCloudQuiet

/-! The cubic difference in the conditional covariance reads the actual prior vacuum on this angular tangent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmCubicGeometry
open Function Filter MeasureTheory RG Lattice Tree Wilson Exterior Precision Marker Multi Comparison.RG02
open Comparison.RG02.Assembly WilsonThermometerPositionFilmCloudReading
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} {c f:Side} {S:StepData c f} (F:Forest S.ratio)

def direction (u:Bulk.SliceDir S F G) : fieldDir G f 1 := fderiv ℝ (Work.F03.axisLog F (G:=G)) 0 u

private def chart (w:Bulk.Joint S F (G:=G)) : ℝ × fieldDir G f 1 := (w.1,Work.F03.axisLog F w.2)

private theorem head {z:ℝ → Config G f → ℝ} (h:GradeAt 3 (Bulk.projected z)) (u:Bulk.SliceDir S F G) :
    Assembly.jet (Bulk.posed S F z) 3 (1,u)=Assembly.jet (Bulk.projected z) 3 (1,direction F u) := by
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
    Assembly.jet (Bulk.posed S F z) 3 (1,u)=Assembly.jet (Bulk.projected z ∘ chart F) 3 (1,u):=by
      unfold Assembly.jet;rw [(localEq.iteratedFDeriv ℝ 3).eq_of_nhds]
    _ = _ := curve

variable {clip:Clip} {P:PathData G} {O:ChartRatio G} (K:Bulk.Kernel S clip P O) (tag:S.Choices)
    {V W:Type} [DecidableEq V] [DecidableEq W] {R:Census V} {R':Census W}
    (C:Bulk.Colors R G f) (D:Bulk.Colors R' G f)

theorem jet_sub {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h l:E→ℝ) (k:ℕ)
    (a:ContDiffAt ℝ k h 0) (b:ContDiffAt ℝ k l 0) (x:E) :
    Assembly.jet (h-l) k x=Assembly.jet h k x-Assembly.jet l k x := by
  unfold Assembly.jet
  rw [iteratedFDeriv_sub_apply a b]
  exact smul_sub _ _ _

private theorem ready (G₀:GradeAt 3 (Bulk.projected C.vac)) : ContDiffAt ℝ ω (Bulk.geometric K F tag C) 0 := by
  have times:ContDiffAt ℝ ω (Bulk.pillar (S:=S) (F:=F) (G:=G)) 0:=contDiffAt_fst.pow 2
  exact (Bulk.stone_smooth K F tag).add ((times.mul (Bulk.officer_known K F).smooth).add
    (Bulk.joint_receipt S F G₀).smooth)

theorem difference (hC:GradeAt 3 (Bulk.projected C.vac)) (hD:GradeAt 3 (Bulk.projected D.vac))
    (u:Bulk.SliceDir S F G) :
    Assembly.jet (Bulk.geometric K F tag C) 3 (1,u)-Assembly.jet (Bulk.geometric K F tag D) 3 (1,u)=
    Assembly.jet (Bulk.projected C.vac) 3 (1,direction F u)-Assembly.jet (Bulk.projected D.vac) 3 (1,direction F u) := by
  rw [←head F hC u,←head F hD u,←jet_sub _ _ _ ((ready F K tag C hC).of_le le_top)
    ((ready F K tag D hD).of_le le_top),←jet_sub _ _ _ ((Bulk.joint_receipt S F hC).smooth.of_le le_top)
    ((Bulk.joint_receipt S F hD).smooth.of_le le_top)]
  congr 1
  funext v
  simp only [Pi.sub_apply,Bulk.geometric,Bulk.fee,Bulk.supplement]
  ring

theorem original (hC:GradeAt 3 (Bulk.projected C.vac)) (hD:GradeAt 3 (Bulk.projected D.vac))
    (x:fieldDir G c 1) (z:Precision.Key F G→ℝ) :
    noise K F tag C x z - noise K F tag D x z=
    let b:=direction F (Bulk.translated K F x z).2
    (Assembly.jet (Bulk.projected C.vac) 3 (1,b)-Assembly.jet (Bulk.projected D.vac) 3 (1,b):ℝ) := by
  have shift:Bulk.translated K F x z=(1,(Bulk.translated K F x z).2):=by rw [Bulk.footing]
  unfold noise
  dsimp only
  rw [←Complex.ofReal_sub]
  congr 1
  conv_lhs => rw [shift]
  exact difference F K tag C D hC hD _

end YM.Integration.WilsonThermometerPositionFilmCubicGeometry
