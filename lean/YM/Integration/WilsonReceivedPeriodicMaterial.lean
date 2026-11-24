import YM.Integration.WilsonReceivedMarkedCoefficient
import YM.Integration.PhysicalWilsonPeriodizedMaterial
import YM.Integration.PeriodicMarkedWinding

/-! The polynomial in the received Wilson estimate is computed on one
finite periodic Gaussian with the actual marked inputs and stationary drift. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedPeriodicMaterial
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

local notation "X" => testInclusion J.tests x
local notation "arriving" => (packet.input.leaf (X)).density
local notation "analytic" => ManuscriptQLocalActualLog.source R d H (X)
local notation "forced" => WilsonReceivedMarkedCofactor.compulsory R d packet x
local notation "income" => MarkedPackets.uniformModelCost J.inputPacketRankCap (Fintype.card I) (A.admittedCost d.level)
local notation "toll" => fun i => H.inputRadii i/H.kernelCosts i
local notation "budget" => income * (Real.exp ((Fintype.card I:ℝ)*packet.regularPrice)-1)
variable (angle : fieldDir G (R.family.side d.level d.period) 1)
local notation "v" => Integral.sample g angle
local notation "model" => WilsonReceivedIndependentRemainder.model R d (H:=H) x angle
local notation "z" => ((P₀).eval v : ℂ)
local notation "hard" => (z⁻¹ • Actual.Push Δ (P).beta forced v : Poly Γ)
local notation "chosen" => ({d with colors:=H.colors (X),field:=angle} : LocalFormal.Datum R.family Γ)
local notation "finite" => Order.value (g : ℂ) ((chosen).markedLog (RunFormalChain.fromRun R) J.order)
local notation "zones" => fun _ : (Δ).Choices => Integral.zone K (P).p d.forest g angle
local notation "localError" => Local.markingError P analytic K g d.forest d.tag (H.colors (X))
  (zones) angle J.order (Fintype.card I)


local notation "material" => PhysicalWilsonPeriodizedMaterial.reference R d.cutoff d.level d.period
  d.below angle (H.colors (X)) J.order
local notation "invoice" => fun s : Γ.Mode => budget / Poly.toll toll s + ‖(hard).part s‖

/-- Identify the full finite moment table before taking its logarithm. -/
theorem original :
    (chosen).raw (RunFormalChain.fromRun R) J.order = material ∧
    finite = Order.value (g : ℂ) (Order.logMarked material) := by
  have h : (chosen).raw (RunFormalChain.fromRun R) J.order = material :=
    PhysicalWilsonPeriodizedMaterial.original R d.cutoff d.level d.period d.below
      angle (H.colors (X)) J.order d.forest d.tag (H.convention.well (X))
  exact ⟨h,congrArg (fun A => Order.value (g : ℂ) (Order.logMarked A)) h⟩

include received rep allocation q in
/-- The original normalized connected read is compared to the material on
its own finite torus. The error retains its actual compulsory numerator. -/
theorem measured (s : Γ.Mode) :
    ‖(Local.cumulant P arriving Δ v).part s -
      (Order.value (g : ℂ) (Order.logMarked material)).part s‖ ≤
      OriginalMarkedRunAction.partitionTariff model (invoice) s + ‖(localError).part s‖ := by
  rw [←(original R d (H:=H) x angle).2]
  exact WilsonReceivedMarkedCoefficient.measured R d allocation q packet received rep x angle s

end YM.Integration.WilsonReceivedPeriodicMaterial
