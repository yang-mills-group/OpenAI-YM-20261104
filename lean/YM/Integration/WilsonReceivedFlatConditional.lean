import YM.Integration.WilsonRootedNonflatLog
import YM.Integration.ManuscriptQLocalPrepared

/-! The complete received input, with all its old regular and forced marks, on
the actual independently filed Gaussian. The unmarked divisor is the true
outgoing Wilson density at the specified coarse configuration. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedFlatConditional

open Function Filter MeasureTheory Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree
open Matrix Pressure Pressure.Testing Pressure.Stores Next.SectorChange Next.SectorChange.Rows
open Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent.Affine
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open scoped Topology BigOperators Classical
variable {G:Gauge}{I:Type} [DecidableEq I] {Γ:Census I}(R:Run G)(d:LocalFormal.Datum R.family Γ)
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "Θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => Pressure.Testing.ships R.alloy.B d.cutoff d.level d.period
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "P₀" => R.family.path.rep d.cutoff d.period d.level
local notation "K" => d.kernel (RunFormalChain.fromRun R)
local notation "g" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "i₀" => R.alloy.B.a.clock.J d.level
local notation "i₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "w" => R.kit.walls i₁ i₀
local notation "Coarse" => fieldDir G (R.family.side d.level d.period) 1
variable (allocation : Allocation G (R.family.path.levels.clock.op d.level d.period) (R.alloy.B.a.clock.hatBeta d.level)
  (R.kit.walls (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level))) (q : Chi)
local notation "Outer" => Config G (R.family.side d.level d.period)
variable [Fintype I] {J : Request I} {A : NumericSchedule R.family J} {H : AnalyticInput J A d}
variable {η : ℝ} (packet : FullPreparedInputAt H η) (received : Retained.NativeIntake packet)
variable (rep : packet.carrier.rep = R.family.path.rep d.cutoff d.period (d.level+1)) (x : IndependentTests J.tests)
local notation "arriving" => (packet.input.leaf (testInclusion J.tests x)).density

include received in
theorem moments (v : Outer) (b : Coarse) :
    Actual.Push Δ (P).beta arriving v =
      (fun s : Γ.Mode => WilsonRootedNonflatLog.sum R d allocation q v b (Actual.atMark s arriving) : Poly Γ) := by
  have valid := ManuscriptQLocalPrepared.input R d packet received x
  funext s
  refine (congrFun (Actual.grades (S:=Δ) (D:=arriving) (J:=v) (β:=(P).beta)) s).trans ?_
  exact (WilsonRootedNonflatLog.measured R d allocation q v b _ (valid.1 s)
    (fun κ U => congrArg (fun z : Poly Γ => z.part s) (valid.2 κ U))).symm

include received rep in
theorem connected (v : Outer) (b : Coarse) :
    Local.cumulant P arriving Δ v = Extra.Trajectories.connected
      (((P₀).eval v : ℂ)⁻¹ •
        (fun s : Γ.Mode => WilsonRootedNonflatLog.sum R d allocation q v b (Actual.atMark s arriving) : Poly Γ)) := by
  have valid := ManuscriptQLocalPrepared.input R d packet received x
  have floor : Actual.Floor (P) arriving := ⟨fun U => by
    have h := ManuscriptQLocalPrepared.quiet R d packet received x U
    exact h.trans (congrArg (fun z : Rep G _ => (z.eval U : ℂ)) rep),valid.1,valid.2⟩
  have hpoly := moments R d allocation q packet received x v b
  have quiet := (Local.RealStep.advance R.family d.cutoff d.period d.level d.below arriving R.makes floor).vacancy v
  rw [Local.cumulant,Local.normalized,Local.yield,Order.unitScale,hpoly]
  congr 2
  exact congrArg (fun z : ℂ => z⁻¹) ((congrArg (fun z : Poly Γ => z.part Γ.quiet) hpoly).symm.trans quiet)

end YM.Integration.WilsonReceivedFlatConditional
