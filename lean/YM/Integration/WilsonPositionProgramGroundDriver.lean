import YM.Integration.WilsonPositionProgramReceivedRootGround
import YM.Integration.WilsonThermometerPositionFilmAxisSalary
import YM.Integration.WilsonThermometerPositionFilmReassembled
import YM.Integration.WilsonThermometerPositionFilmCubicGeometry
import YM.Integration.WilsonThermometerPositionFilmUpperTerms

/-! On the true translated fine marginal the entire ground is the finite exponential of the upper connected table. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramGroundDriver
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


open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02
open Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Order
open Extra.Trajectories (connected)
open scoped BigOperators Classical
open WilsonPositionProgramHeatedWallet WilsonPositionProgramFiledGaussianChange
variable {V:Type}[DecidableEq V][Fintype V]{R:Census V}
  {clip:Clip}{P:PathData G}{O:ChartRatio G}(K:Bulk.Kernel S clip P O)(tag:S.Choices)
  (W:Bulk.Colors R G f)(hw:∀i,GradeAt (W.power i) (Bulk.projected (W.mark i)))

include hw in
theorem original (A:fieldDir G c 1)(i:Multi.Hot (Comparison.RG02.Order.Board R 0))(z:Precision.Key F G→ℝ):
    Cloud.paint z (drivers K F tag W A 0 i)=
    (Air.discharge W 0 (direction F (Bulk.translated K F A z).2)).part (Join.left i.val):=by
  have hit:=WilsonPositionProgramHeatedWallet.zero i
  let s:Multi.Hot R:=⟨Join.left i.val,hit⟩
  have empty:(Join.right i.val).val=∅:=Finset.eq_empty_iff_forall_notMem.2 (fun a _=>Fin.elim0 a)
  have t:Assembly.translate (Bulk.stage K F A) (Bulk.hinge F) z=(1,(Bulk.translated K F A z).2):=by
    change Bulk.translated K F A z=_;rw [Bulk.footing]
  simp only [drivers,Assembly.generator,dif_pos hit,empty,Finset.card_empty,Nat.factorial_zero,Nat.cast_one,
    one_smul,Assembly.reading,t,add_zero]
  change Assembly.jet (Bulk.posed S F (W.mark s)) (W.power s) (1,(Bulk.translated K F A z).2)=_
  rw [head F (hw s)]
  unfold Air.discharge
  rw [Multi.part_lit _ s]
  simp only [add_zero]

end YM.Integration.WilsonPositionProgramGroundDriver
end
