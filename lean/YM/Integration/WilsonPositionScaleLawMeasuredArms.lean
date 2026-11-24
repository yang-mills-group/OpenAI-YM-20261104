import YM.Integration.WilsonPositionScaleLawMeasuredOPEDates
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredArms
open WilsonPhysicalRosePositionFace (located predicted)
open WilsonPositionProgramTrialPublicJointPivotRose (Live tested)
open scoped Classical Topology BigOperators
open Function Filter Set Finset PowerSeries MeasureTheory Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Rose PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open FVA2.Scale.Jury (Thin fxt)
open WilsonPositionScaleLawThermometerChart (response)
open WilsonPositionScaleLawIndependent (ψ)
open scoped Topology BigOperators Classical Polynomial


open Position Position.Axes Dframe Level Reg.Point Facets Equator Measure Reg.CoverTest
variable {G : Gauge} (Z : WilsonPrescription G) {hG : G.Simple}
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} {b : Bool} (H : Main.Match Z hG M σ b) (ν : ℝ)
open WilsonPositionProgramTrialPublicJointPivotForecast (forecast)


open scoped ContDiff
open WilsonPositionProgramTrialPublicJointPivotRestriction (coordinates)
open MS.Theater FVA2.Dframe
open WilsonPositionScaleLawMeasuredBank (fixed)

open WilsonPositionThermometerCapStation WilsonPositionCapTransport
open WilsonPositionScaleLawMeasuredCut (sample)
open WilsonPositionScaleLawMeasuredJoint (full)
variable {R:Run G}{o:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family o S)(J:ℝ→tower S){l:Ultrafilter (ℕ×ℕ)} {Y:(Bel R.family.book).Hierarchy}{B n:ℕ}
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "P" => WilsonPositionPrescribedFrame.positioned F J Z.store


open WilsonPositionScaleLawMeasuredOPEContour
variable {d h k:ℕ}

open WilsonPositionScaleLawMeasuredOPEDates (housed marked)
local notation "JH" => WilsonPositionHomogeneousFrame.homogeneous F J Z
def arm (r:ℝ)(v:Sec G d) : Sec G d :=
  Maxwell.Free.fields R.family.labels d (WilsonPositionHomogeneousFrame.change F J Z d r
    ((Maxwell.Free.fields R.family.labels d).symm v))
theorem physical (r:ℝ)(v:Sec G d) : P r d ((Maxwell.Free.fields R.family.labels d).symm (arm Z F J r v))=
    JH r d ((Maxwell.Free.fields R.family.labels d).symm v) := by
  simp only [arm,LinearEquiv.symm_apply_apply,WilsonPositionHomogeneousFrame.homogeneous,LinearEquiv.trans_apply]

theorem fixedExterior (r t:ℝ)(v:Sec G d) :
    P r d ((Maxwell.Free.fields R.family.labels d).symm (housed Z F J r t (arm Z F J t v)))=
      JH t d ((Maxwell.Free.fields R.family.labels d).symm v) :=
  (WilsonPositionScaleLawMeasuredOPEDates.sameExterior Z F J r t _).trans (physical Z F J t v)

theorem fitted (r:ℝ)(fit:Bijective (stand (WilsonPositionHomogeneousFrame.turn F J Z d r)))(v:Sec G d):
    arm Z F J r v=stand (WilsonPositionHomogeneousFrame.turn F J Z d r) v := by
  simp [arm,WilsonPositionHomogeneousFrame.change,dif_pos fit]

include H in
theorem lower (r:ℝ)(below:h≤d)(small:Bijective (stand (WilsonPositionHomogeneousFrame.turn F J Z h r)))
    (large:Bijective (stand (WilsonPositionHomogeneousFrame.turn F J Z d r)))(v:Sec G h):
    arm Z F J r (up below v)=up below (arm Z F J r v) := by
  rw [fitted Z F J r large,fitted Z F J r small]
  exact WilsonPositionHomogeneousNear.includes Z (WilsonPositionHomogeneousCoefficients.purchased Z H) below _ v

theorem hierarchy (r:ℝ)(rp:0<r)(φ:Test n)(v:Fin n→Sec G d) :
    WilsonPositionPrescribedScreen.hierarchy F P d r n φ (fun i=>arm Z F J r (v i)) =
      WilsonPositionPrescribedScreen.hierarchy F JH d r n φ v := by
  rw [WilsonPositionPrescribedScreen.actual F P d n φ _ rp,WilsonPositionPrescribedScreen.actual F JH d n φ _ rp]
  apply congrArg φ.applyTo
  funext x
  apply congrArg (S.classMoment (spectator F none) _ (r • x))
  funext i
  exact physical Z F J r (v i)
end YM.Integration.WilsonPositionScaleLawMeasuredArms
