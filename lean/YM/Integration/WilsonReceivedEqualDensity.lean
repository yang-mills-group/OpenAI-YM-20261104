import YM.Integration.WilsonReceivedPeriodicMaterial

/-! Re-enter the actual finite Wilson step after a marked hard merger that
preserves its quiet density pointwise. Its entire signed residual is integrated
against the original kernel and kept together through vacuum subtraction. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedEqualDensity
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
local notation "Outer" => Config G (R.family.side d.level d.period)
variable [Fintype I] {J : Request I} {A : NumericSchedule R.family J} {H : AnalyticInput J A d}
variable {η : ℝ} (packet : FullPreparedInputAt H η) (received : Retained.NativeIntake packet)
variable (x : IndependentTests J.tests)

local notation "X" => testInclusion J.tests x
local notation "arriving" => (packet.input.leaf (X)).density
local notation "analytic" => ManuscriptQLocalActualLog.source R d H (X)
local notation "forced" => WilsonReceivedMarkedCofactor.compulsory R d packet x
variable (angle : fieldDir G (R.family.side d.level d.period) 1)
local notation "v" => Integral.sample g angle
local notation "model" => WilsonReceivedIndependentRemainder.model R d (H:=H) x angle
local notation "z" => ((P₀).eval v : ℂ)
local notation "chosen" => ({d with colors:=H.colors (X),field:=angle} : LocalFormal.Datum R.family Γ)
local notation "finite" => Order.value (g : ℂ) ((chosen).markedLog (RunFormalChain.fromRun R) J.order)
local notation "zones" => fun _ : (Δ).Choices => Integral.zone K (P).p d.forest g angle
local notation "localError" => Local.markingError P analytic K g d.forest d.tag (H.colors (X))
  (zones) angle J.order (Fintype.card I)


local notation "material" => PhysicalWilsonPeriodizedMaterial.reference R d.cutoff d.level d.period
  d.below angle (H.colors (X)) J.order

local notation "actual" => (z⁻¹ • Actual.Push Δ (P).beta arriving v : Poly Γ)
local notation "residual" => (arriving - analytic)
local notation "debit" => (z⁻¹ • Actual.Push Δ (P).beta (residual) v : Poly Γ)
local notation "Fine" => Config G (R.family.side (d.level+1) d.period)
variable (same : ∀ U : Config G (R.family.side (d.level+1) d.period),
  packet.carrier.rep.eval U = (R.family.path.rep d.cutoff d.period (d.level+1)).eval U)

include same in
/-- Fieldwise equality leaves the regular and genuinely compulsory parts of the
received polynomial at their original addresses. -/
theorem components (U : Fine) :
    residual U = ((P).eval U : ℂ) • WilsonReceivedMarkedCofactor.regular R d packet x U +
      forced U := by
  have h := WilsonReceivedMarkedCofactor.split R d packet x U
  have quiet := congrArg (fun a : ℝ => (a : ℂ)) (same U)
  rw [quiet,sub_self,zero_smul,add_zero] at h
  exact h

include received in
/-- Integrate the complete signed table before applying the connected log. -/
theorem table : actual = model + debit := by
  have clean := ManuscriptQLocalActualLog.floor R d H (X)
  have arrivingSafe := (ManuscriptQLocalPrepared.input R d packet received x).1
  have diffSafe := Actual.leaf_sub arrivingSafe clean.safe
  have split : Actual.Push Δ (P).beta arriving v =
      Actual.Push Δ (P).beta analytic v + Actual.Push Δ (P).beta (residual) v := by
    funext s
    have joined : Actual.atMark s arriving = Actual.atMark s analytic + Actual.atMark s (residual) := by
      funext U
      change (arriving U).part s = (analytic U).part s + ((arriving U).part s - (analytic U).part s)
      abel
    rw [show (Actual.Push Δ (P).beta arriving v) s =
        (Δ).push (P).beta (Actual.atMark s arriving) v from congrFun (Actual.grades (S:=Δ) (D:=arriving) (J:=v) (β:=(P).beta)) s,
      joined,StepData.push_add (R.family.path.levels.transition_mass d.level d.period (P).beta) _ _
        ((clean.safe s).integrableC _) ((diffSafe s).integrableC _),Pi.add_apply]
    exact congrArg₂ (·+·) (congrFun (Actual.grades (S:=Δ) (D:=analytic) (J:=v) (β:=(P).beta)) s).symm
      (congrFun (Actual.grades (S:=Δ) (D:=residual) (J:=v) (β:=(P).beta)) s).symm
  have h := ManuscriptQLocalActualLog.conditional R d H (X) angle
  have pushed : Actual.Push Δ (P).beta analytic v = (z • model : Poly Γ) :=
    h.2.trans (congrArg (fun a : Poly Γ => z • a.pass) h.1)
  have nz : z ≠ 0 := Complex.ofReal_ne_zero.mpr
    ((Normal.actual R.family.path R.makes.wilson d.cutoff d.period d.level d.below.le).positive v).ne'
  rw [split,pushed,smul_add,smul_smul,inv_mul_cancel₀ nz,one_smul]

private theorem normalizedField (incoming : Fine → Poly Γ) (floor : Actual.Floor (P) incoming) :
    (z⁻¹ • Actual.Push Δ (P).beta incoming v : Poly Γ).part Γ.quiet = 1 ∧
    Local.cumulant P incoming Δ v =
      Extra.Trajectories.connected (z⁻¹ • Actual.Push Δ (P).beta incoming v : Poly Γ) := by
  have vacant : (Actual.Push Δ (P).beta incoming v).part Γ.quiet = z :=
    (Local.RealStep.advance R.family d.cutoff d.period d.level d.below incoming R.makes floor).vacancy v
  constructor
  · rw [Poly.part_smul,vacant,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
      ((Normal.actual R.family.path R.makes.wilson d.cutoff d.period d.level d.below.le).positive v).ne')]
  · rw [Local.cumulant,Local.normalized,Local.yield,Order.unitScale,vacant]

include received same in
theorem normalized : (actual).part Γ.quiet = 1 ∧
    Local.cumulant P arriving Δ v = Extra.Trajectories.connected (actual) := by
  have ok := ManuscriptQLocalPrepared.input R d packet received x
  have floor : Actual.Floor (P) arriving := ⟨fun U =>
    (ManuscriptQLocalPrepared.quiet R d packet received x U).trans
      (congrArg (fun a : ℝ => (a : ℂ)) (same U)),ok.1,ok.2⟩
  exact normalizedField R d angle arriving floor

include received same in
/-- Every occupied coefficient is controlled by the true signed, normalized
output residual and the current local expansion on its finite periodic material. -/
theorem measured (s : Γ.Mode) :
    ‖(Local.cumulant P arriving Δ v).part s -
      (Order.value (g : ℂ) (Order.logMarked material)).part s‖ ≤
      OriginalMarkedRunAction.partitionTariff model (fun j => ‖(debit).part j‖) s +
        ‖(localError).part s‖ := by
  have exactTable := table R d packet received x angle
  have normed := normalized R d packet received x angle same
  have law := ManuscriptQLocalActualLog.conditional R d H (X) angle
  have clean := normalizedField R d angle analytic (ManuscriptQLocalActualLog.floor R d H (X))
  have pushed : Actual.Push Δ (P).beta analytic v = (z • model : Poly Γ) :=
    law.2.trans (congrArg (fun a : Poly Γ => z • a.pass) law.1)
  have nz : z ≠ 0 := Complex.ofReal_ne_zero.mpr
    ((Normal.actual R.family.path R.makes.wilson d.cutoff d.period d.level d.below.le).positive v).ne'
  rw [pushed,smul_smul,inv_mul_cancel₀ nz,one_smul] at clean
  have base := clean.2.symm.trans law.1
  have perturb (j : Γ.Mode) : ‖(actual).part j - (model).part j‖ ≤ ‖(debit).part j‖ := by
    rw [exactTable,Poly.part_plus,add_sub_cancel_left]
  have pc := OriginalMarkedRunAction.partition_change (actual) (model)
    (fun j => ‖(debit).part j‖) normed.1 clean.1 perturb s
  rw [normed.2,←(WilsonReceivedPeriodicMaterial.original R d (H:=H) x angle).2]
  calc
    _ = ‖((Extra.Trajectories.connected (actual)).part s -
        (Extra.Trajectories.connected (model)).part s) + (localError).part s‖ := by
      rw [base,Poly.part_plus]; congr 1; abel
    _ ≤ _ := (norm_add_le ..).trans (add_le_add pc le_rfl)

end YM.Integration.WilsonReceivedEqualDensity
