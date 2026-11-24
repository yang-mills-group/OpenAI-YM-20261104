import YM.Integration.WilsonThermometerWardCloseCoverAssay

/-! Bind the solved original (6,4,4) field to the positioned thermometer
both on every Wilson configuration and on all copied bare Wick programmes. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerWardNamedProgram
open Filter Function Finset Lattice Wilson RG Source Marker Labels QuadraticLocal PhysMS
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open WilsonCapturedPrimaryActiveArms WilsonCapturedPrimaryWardGapAperture
open WilsonThermometerOwnOffsetField WilsonThermometerOffsetTrajectory
open WilsonOriginalThermometerPalette WilsonPositionThermometerCapStation
open WilsonPositionThermometerGradedSource WilsonOriginalThermometerTopDensity
open Tree Earn Sunrise QuadraticLocal.Affinity FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor WilsonPositionThermometerGradedReading
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G)
local notation "C" => R.family

theorem on_shelf {n k N p:ℕ} (d:Fin n→ℕ) (o:Fin n→Site ((C).side N p))
    (S:Shelf (N:=N) (p:=p) R k d o) (live:k≤N) (y:(i:Fin n)→Palette (C) (d i))
    (w:(i:Fin n)→(C).label (d i)) (actual:WilsonCapturedPrimaryNamedReturn.primary R (p:=p) d S.route live w y):
    exposed R d o S live y=w:=by
  funext i
  have found:=WilsonCapturedPrimaryWardGapAperture.funded R d o S live y i
  have same:=found.symm.trans (actual i)
  let a:=((C).S.a k:ℂ)^(d i)
  have non:a≠0:=pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ((C).S.a_pos _).ne')
  have exact:=congrArg (fun z:(C).label (d i)=>a • z) same
  simpa only [smul_smul,show a*(((C).S.a k:ℂ)^(d i))⁻¹=1 from mul_inv_cancel₀ non,one_smul] using exact

def axis (A:Group (C) 6) (N p:ℕ) (i:Fin 3):(C).label (levels i):=
  A.station.wheel.atCut (N,p) (index A (grade i)) (vector A univ i)

theorem original (A:Group (C) 6) (simple:G.Simple) {b p k₀:ℕ} (o:Positions (Fin 3) ((C).side (b+1) p))
    (S:Shelf (N:=b+1) (p:=p) R k₀ levels o.origin) (live:k₀≤b+1)
    (y:(i:Fin 3)→Palette (C) (levels i))
    (actual:WilsonCapturedPrimaryNamedReturn.primary R (p:=p) levels S.route live (axis R A (b+1) p) y)
    (refs:∀i,(C).ref (levels i)≤b+1):
    let w:=exposed R levels o.origin S live y
    (∀σ:ℝ,WilsonThermometerWardBareScene.models R levels (b+1) p o.origin w σ
      WilsonOriginalThermometerGradedPalette.positive = primitive R A (b+1) p o.origin σ) ∧
    WilsonThermometerWardBareScene.physical R levels (b+1) p o.origin w =
      WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self b) o ∧
    ∀(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (π:ℕ→Layout G)
      (φ:ℕ→ℕ) (stage:ℕ) (school:Syl.School stage),
      WilsonThermometerWardDeclaredPost.bare R D π (φ:=φ) school o levels
        WilsonOriginalThermometerGradedPalette.positive w=WilsonThermometerRegisteredPupil.bare R A D π (φ:=φ) school o:=by
  intro w
  have same:w=axis R A (b+1) p:=on_shelf R levels o.origin S live y _ actual
  rw [same]
  refine ⟨fun _=>rfl,?_,fun _ _ _ _ _=>rfl⟩
  funext x U
  exact (WilsonThermometerWardBareScene.offered R levels (b+1) p o.origin _ 1
    WilsonOriginalThermometerGradedPalette.positive refs x U).symm.trans
    (WilsonOriginalThermometerTopDensity.offered R A simple b p o refs 1 x U)

end YM.Integration.WilsonThermometerWardNamedProgram
