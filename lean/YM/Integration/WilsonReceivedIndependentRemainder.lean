import YM.Integration.WilsonReceivedFlatConditional
import YM.Integration.WilsonReceivedMarkedCofactor

/-! Exact error in the independent finite marked logarithm on the complete
prepared Wilson source. The previous signed remainder is integrated on its
actual forest and shared tag before any vacuum subtraction. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedIndependentRemainder
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
local notation "analytic" => ManuscriptQLocalActualLog.source R d H (testInclusion J.tests x)
local notation "Fine" => Config G (R.family.side (d.level+1) d.period)

/-- The entire signed residual at the actual previous field. -/
def cofactor (U : Fine) : Poly Γ :=
  Poly.pass (H.packets.read (testInclusion J.tests x) g U) *
    ((packet.prepared.remainder.leaf (testInclusion J.tests x)).density U -
      ((P).eval U : ℂ) • (1 : Poly Γ))

include rep in
theorem selected (U : Fine) : cofactor R d packet x U =
    ((P).eval U : ℂ) • WilsonReceivedMarkedCofactor.regular R d packet x U +
      WilsonReceivedMarkedCofactor.compulsory R d packet x U := by
  have quiet := congrArg (fun z : Rep G _ => (z.eval U : ℂ)) rep
  have h := WilsonReceivedMarkedCofactor.split R d packet x U
  rw [quiet,sub_self,zero_smul,add_zero] at h
  exact (ManuscriptQLocalActualLog.inherited R d H (testInclusion J.tests x) packet U).symm.trans h

def correction (v : Outer) (angle : Coarse) : Poly Γ :=
  fun s => WilsonRootedNonflatLog.sum R d allocation q v angle (fun U => (cofactor R d packet x U).part s)

/-- The independently filed finite log, including its genuine local chart error. -/
def model (angle : Coarse) : Poly Γ :=
  let colors := H.colors (testInclusion J.tests x)
  let chosen : LocalFormal.Datum R.family Γ := {d with colors:=colors,field:=angle}
  let zones := fun _ : (Δ).Choices => Integral.zone K (P).p d.forest g angle
  (Order.value (g : ℂ) (chosen.markedLog (RunFormalChain.fromRun R) J.order) +
    Local.markingError P analytic K g d.forest d.tag colors zones angle J.order (Fintype.card I)).pass

include received in
theorem discrepancy (v : Outer) (angle : Coarse) (s : Γ.Mode) :
    WilsonRootedNonflatLog.sum R d allocation q v angle (Actual.atMark s arriving) -
      WilsonRootedNonflatLog.sum R d allocation q v angle (Actual.atMark s analytic) =
      WilsonRootedNonflatLog.sum R d allocation q v angle (fun U => (cofactor R d packet x U).part s) := by
  let a := Actual.atMark s arriving
  let h := Actual.atMark s analytic
  have valid := ManuscriptQLocalPrepared.input R d packet received x
  have ideal := ManuscriptQLocalActualLog.floor R d H (testInclusion J.tests x)
  have ha : Envelope a := valid.1 s
  have hh : Envelope h := ideal.safe s
  have ia : GaugeInvariant a := fun κ U => congrArg (fun z : Poly Γ => z.part s) (valid.2 κ U)
  have ih : GaugeInvariant h := fun κ U => congrArg (fun z : Poly Γ => z.part s) (ideal.gauges κ U)
  have idiff : GaugeInvariant (fun U=>a U-h U) := fun κ U => congrArg₂ (·-·) (ia κ U) (ih κ U)
  have kernel := R.family.path.levels.transition_mass d.level d.period (P).beta
  have delta : (fun U=>a U-h U) = fun U => (cofactor R d packet x U).part s := by
    funext U
    exact congrArg (fun z : Poly Γ => z.part s) (ManuscriptQLocalActualLog.inherited R d H (testInclusion J.tests x) packet U)
  calc
    _ = (Δ).push (P).beta a v - (Δ).push (P).beta h v :=
      congrArg₂ (·-·) (WilsonRootedNonflatLog.measured R d allocation q v angle _ ha ia)
        (WilsonRootedNonflatLog.measured R d allocation q v angle _ hh ih)
    _ = (Δ).push (P).beta (fun U=>a U-h U) v := by
      unfold StepData.push
      simp_rw [smul_sub]
      exact (integral_sub (StepData.push_slice kernel v a (ha.integrableC _))
        (StepData.push_slice kernel v h (hh.integrableC _))).symm
    _ = _ := (WilsonRootedNonflatLog.measured R d allocation q v angle _ (ha.subC hh) idiff).symm.trans
      (congrArg (WilsonRootedNonflatLog.sum R d allocation q v angle) delta)

include received in
theorem numerator (angle : Coarse) (s : Γ.Mode) :
    let v := Integral.sample g angle
    WilsonRootedNonflatLog.sum R d allocation q v angle (Actual.atMark s arriving) =
      ((P₀).eval v : ℂ) * (model R d (H:=H) x angle).part s +
        WilsonRootedNonflatLog.sum R d allocation q v angle (fun U=>(cofactor R d packet x U).part s) := by
  intro v
  have delta := discrepancy R d allocation q packet received x v angle s
  have filed := WilsonRootedNonflatLog.original R d H (testInclusion J.tests x) allocation q angle s
  have base : WilsonRootedNonflatLog.sum R d allocation q v angle (Actual.atMark s analytic) =
      ((P₀).eval v : ℂ) * (model R d (H:=H) x angle).part s := filed
  rw [←base,←delta]
  abel


include received rep in
theorem connected (angle : Coarse) :
    let v := Integral.sample g angle
    Local.cumulant P arriving Δ v =
      Extra.Trajectories.connected
        (model R d (H:=H) x angle + (((P₀).eval v : ℂ)⁻¹ •
          correction R d allocation q packet x v angle : Poly Γ)) := by
  intro v
  rw [WilsonReceivedFlatConditional.connected R d allocation q packet received rep x v angle]
  apply congrArg Extra.Trajectories.connected
  funext s
  have nz : ((P₀).eval v : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr ((Normal.actual R.family.path R.makes.wilson d.cutoff d.period
      d.level d.below.le).positive v).ne'
  change ((P₀).eval v : ℂ)⁻¹ * WilsonRootedNonflatLog.sum R d allocation q v angle
    (Actual.atMark s arriving) = _ + ((P₀).eval v : ℂ)⁻¹ * _
  rw [numerator R d allocation q packet received x angle s,mul_add,←mul_assoc,inv_mul_cancel₀ nz,one_mul]
  rfl

end YM.Integration.WilsonReceivedIndependentRemainder
