import YM.Integration.WilsonReceivedRegularTransport
import YM.Integration.WilsonRetainedOccupiedLog

/-! Price the connected coefficient on the complete measured Wilson input against the
independently specified finite marked log, through the actual marked denominator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedMarkedCoefficient
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
local notation "reg" => WilsonReceivedMarkedCofactor.regular R d packet x
local notation "forced" => WilsonReceivedMarkedCofactor.compulsory R d packet x
local notation "income" => MarkedPackets.uniformModelCost J.inputPacketRankCap (Fintype.card I) (A.admittedCost d.level)
local notation "toll" => fun i => H.inputRadii i/H.kernelCosts i
local notation "budget" => income * (Real.exp ((Fintype.card I:ℝ)*packet.regularPrice)-1)
variable (angle : fieldDir G (R.family.side d.level d.period) 1)
local notation "v" => Integral.sample g angle
local notation "model" => WilsonReceivedIndependentRemainder.model R d (H:=H) x angle
local notation "corr" => WilsonReceivedIndependentRemainder.correction R d allocation q packet x v angle
local notation "z" => ((P₀).eval v : ℂ)
local notation "avg" => actualAverage R.family (N:=d.cutoff) reg v
local notation "hard" => (z⁻¹ • Actual.Push Δ (P).beta forced v : Poly Γ)
local notation "actual" => (z⁻¹ • Actual.Push Δ (P).beta arriving v : Poly Γ)
local notation "chosen" => ({d with colors:=H.colors (X),field:=angle} : LocalFormal.Datum R.family Γ)
local notation "finite" => Order.value (g : ℂ) ((chosen).markedLog (RunFormalChain.fromRun R) J.order)
local notation "zones" => fun _ : (Δ).Choices => Integral.zone K (P).p d.forest g angle
local notation "localError" => Local.markingError P analytic K g d.forest d.tag (H.colors (X))
  (zones) angle J.order (Fintype.card I)

omit [Fintype I] in
private theorem positive : z ≠ 0 :=
  Complex.ofReal_ne_zero.mpr ((Normal.actual R.family.path R.makes.wilson d.cutoff d.period
    d.level d.below.le).positive v).ne'

include received rep allocation q in
theorem table : actual = model + avg + hard := by
  have raw : Actual.Push Δ (P).beta arriving v = (z • model : Poly Γ) + corr := by
    rw [WilsonReceivedFlatConditional.moments R d allocation q packet received x v angle]
    funext s
    exact WilsonReceivedIndependentRemainder.numerator R d allocation q packet received x angle s
  rw [raw,smul_add,smul_smul,inv_mul_cancel₀ (positive R d angle),one_smul,
    WilsonReceivedRegularTransport.split R d allocation q packet received rep x v angle,add_assoc]

include received rep in
private theorem quiet : (actual).part Γ.quiet=1 := by
  have valid := ManuscriptQLocalPrepared.input R d packet received x
  have floor : Actual.Floor (P) arriving := ⟨fun U => by
    have h := ManuscriptQLocalPrepared.quiet R d packet received x U
    exact h.trans (congrArg (fun u : Rep G _ => (u.eval U : ℂ)) rep),valid.1,valid.2⟩
  have vacant : (Actual.Push Δ (P).beta arriving v).part Γ.quiet = z :=
    (Local.RealStep.advance R.family d.cutoff d.period d.level d.below arriving R.makes floor).vacancy v
  rw [Poly.part_smul,vacant,inv_mul_cancel₀ (positive R d angle)]

private theorem baseline :
    (model).part Γ.quiet=1 ∧ Extra.Trajectories.connected model = finite + localError := by
  have h := ManuscriptQLocalActualLog.conditional R d H (X) angle
  have pushed : Actual.Push Δ (P).beta analytic v = (z • model : Poly Γ) := by
    rw [h.2,h.1]
    rfl
  have vacancy : (Actual.Push Δ (P).beta analytic v).part Γ.quiet = z :=
    (Local.RealStep.advance R.family d.cutoff d.period d.level d.below analytic
    R.makes (ManuscriptQLocalActualLog.floor R d H (X))).vacancy v
  constructor
  · apply mul_left_cancel₀ (positive R d angle)
    exact ((congrArg (fun u : Poly Γ => u.part Γ.quiet) pushed).symm.trans vacancy).trans
      (mul_one z).symm
  · have normed : Local.cumulant P analytic Δ v = Extra.Trajectories.connected model := by
      rw [Local.cumulant,Local.normalized,Local.yield,Order.unitScale,vacancy,pushed,
        smul_smul,inv_mul_cancel₀ (positive R d angle),one_smul]
    exact normed.symm.trans h.1


local notation "invoice" => fun s : Γ.Mode => budget / Poly.toll toll s + ‖(hard).part s‖

include received rep allocation q in
/-- The two surviving costs are the local interacting error and the signed
forced numerator at its original physical normalization. -/
theorem measured (s : Γ.Mode) :
    ‖(Local.cumulant P arriving Δ v).part s - (finite).part s‖ ≤
      OriginalMarkedRunAction.partitionTariff model (invoice) s + ‖(localError).part s‖ := by
  have eq := table R d allocation q packet received rep x angle
  have hw (i) : 0<(toll) i := div_pos (H.input_radius_positive i) (H.kernel_positive i)
  have perturb (j : Γ.Mode) : ‖(actual).part j - (model).part j‖ ≤ (invoice) j := by
    have ar : ‖(avg).part j‖ ≤ budget / Poly.toll toll j := by
      apply (le_div_iff₀ (Poly.worth hw j)).2
      rw [mul_comm]
      exact (Poly.member hw j _).trans (WilsonReceivedRegularTransport.one R d packet x v)
    rw [eq,Poly.part_plus,Poly.part_plus]
    rw [show (model).part j + (avg).part j + (hard).part j - (model).part j =
      (avg).part j + (hard).part j by abel]
    exact (norm_add_le ..).trans (add_le_add ar le_rfl)
  have base := baseline R d (H:=H) x angle
  have pc := OriginalMarkedRunAction.partition_change (actual) (model) (invoice)
    (quiet R d packet received rep x angle) base.1 perturb s
  have full : Local.cumulant P arriving Δ v = Extra.Trajectories.connected (actual) := by
    rw [eq,WilsonReceivedRegularTransport.connected R d allocation q packet received rep x angle]
  rw [full]
  calc
    _ = ‖((Extra.Trajectories.connected (actual)).part s - (Extra.Trajectories.connected (model)).part s)
      + (localError).part s‖ := by rw [base.2,Poly.part_plus]; congr 1; abel
    _ ≤ _ := (norm_add_le ..).trans (add_le_add pc le_rfl)

end YM.Integration.WilsonReceivedMarkedCoefficient
