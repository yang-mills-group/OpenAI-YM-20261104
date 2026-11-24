import YM.Integration.WilsonPhysicalHistoryRetainedSpringValence
import YM.Integration.WilsonCoherentMayerNoise
import YM.Integration.WilsonCoherentMayerHearing

/-! The sitewise angular calculation uses precisely the original retained
Gaussian coordinates of the chosen forest and the actual compact group links. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Lattice RG Pressure Pressure.Tube Tree Wilson Finset Precision Exterior Work.F03 Bid
open ConnectedActivityE6 Shell Coat Matter SliceRows Channel Push SectorMeasure RGLocalTaylor
open AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

def angularSample (F : Forest S.ratio) (z : Coat.Air f G) : Dir G f :=
  fun i=>WilsonCoherentMayerNoise.row F z (i.1,axisEquiv.symm i.2)

theorem sampled_path {P : Teller G} (fund : P.Funds S T) (X : Coat T F) (V : X.V=1)
    (clear : Assembly.Clear S X.x X.seeds F) {β : ℝ} (pos : 0<β) (y : F.Slice G)
    (z : Coat.Air f G) (t : ℝ) :
    (X.wrapY y).input ((t*(Coat.gStep β)⁻¹) • (X.wrapY y).liftA β z)=
      represent (t • angularSample F z) := by
  let Y:=X.wrapY y
  have born : Y.input 0=(1:Config G f) := by
    rw [WilsonCoherentMayerClear.base Y clear,show Y.V=1 from V,replica_one]
  have state:=WilsonCoherentMayerNoise.drawn fund Y V clear pos z
  rw [WilsonCoherentMayerField.path,born,state]
  funext e
  rw [Work.F03.represent_link]
  simp only [Pi.smul_apply,angularSample,show axisEquiv.symm (coord e.2)=e.2 from axisEquiv.symm_apply_apply _,Pi.one_apply,mul_one]

theorem chamber_path {P : Teller G} (fund : P.Funds S T) (s K : ℝ) (χ : Chi)
    (i : Greenbelt.Reserve S) (v : Finset (LocalLTE.Fan.Veil c f)) (tag : S.Choices)
    {β : ℝ} (pos : 0<β) (y : (Greenbelt.allot i).Slice G) (z : Coat.Air f G) (t : ℝ) :
    let X:=WilsonCoherentMayerHearing.chamber T s K χ 1 v i tag
    (X.wrapY y).input ((t*(Coat.gStep β)⁻¹) • (X.wrapY y).liftA β z)=
      represent (t • angularSample (Greenbelt.allot i) z) := by
  dsimp only
  apply sampled_path fund _ rfl _ pos
  change Assembly.Clear S _ (roster (LocalLTE.Fan.arm (S:=S) v)) _
  rw [LocalLTE.Fan.Field.rosterD]
  exact Assembly.bare_is_Clear _ _ _

end YM.Integration.OriginalMarkedRunAction
