import YM.Integration.WilsonIndependentCompleteFiniteTerminal
import YM.Integration.WilsonThermometerUnitFilingPinRegister

/-! The complete earned angular word in the earlier finite Haar reading, on the actual original band. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingPinProgram
open WilsonIndependentCapturedTerminal
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Budget RegulatorIR.Spatial RegulatorIR.Uniform
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Epoch RegulatorIR.Calibration RegulatorIR.Profiles RegulatorIR.Taping
open RegulatorIR.Binding RegulatorIR.Geometry RegulatorIR.Halo RegulatorIR.FVAAlt2
open WilsonPositionProgramReporterBand WilsonIndependentCapturedPages Pert.Asymptotics
open scoped ENNReal Classical Topology
open WilsonThermometerUnitFilingCoverRegister (Submission)
open WilsonThermometerUnitFilingCoverCurrency (gross sign)
open WilsonThermometerUnitFilingPinRegister (part full Portions)
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type}
local notation "program" => Oracle.books C.family.path.levels.clock.kernel

theorem original {simple : G.Simple} {axis : Axis} {ε : ℝ}
    (elected : WilsonPositionProgramNestedElection.course simple axis ε C.kit)
    (paid : WilsonPositionProgramStageInvoice.Requested C.kit)
    (slow : WilsonWindowReportingPace.Slow C.kit)
    (branch : ∀ patch : Patch, patch.Branches C.family.path.levels.clock.kernel G)
    (order u P debt : ℕ) :
    ∃ first : ℕ, ∀ stage ≥ first, ∀ B : Band C D stage,
    ∃ v : Stop C D B u (debt+P+1), ∀ report : X → ℕ,
      let m := B.lower ∘ report
      let j := B.span ∘ report
      let w := B.powers ∘ report
      let S := WilsonPositionProgramInfraredCircuit.circuit C D m j w (fun x => B.blocks (report x))
      let b := birth C D v report
      let last := stopped C D v report
      ∀ (color : G.ColorIndex) (F : Tent j), Notebook S (program) G branch color (Rocket.native j) F order →
      ∃ seed : (S.dialect (program) G branch (sheet F)).Primitive
          (WilsonIndependentCapturedCalendar.meter C D m j w) order (quantum 1 0),
      let L := S.dialect (program) G branch (sheet F)
      let T := b.after.part L (S.payroll (program) G branch (sheet F)) seed
      let M := WilsonIndependentFreshReel.margins (S.lane (program) G branch (sheet F)) b.after
      ∀ (h : ℕ) (H : X→Submission G) (booked : ∀ x, (H x).grades ()+1=h)
        (center : X→Room), L.cushion (1/8) center →
      ∀ β g₀ cash : X→ℝ, (∀ x, Real.exp 1 ≤ β x) → (∀ x, Real.exp ((H x).σ⁻¹^2) ≤ β x) →
        (∀ x, 0<g₀ x) → (∀ x, 0 ≤ cash x) → (∀ x, β x*(g₀ x)^2 ≤ 2) →
      ∀ d:ℕ, (∀ x,(H x).cost/((H x).rad ()) ≤ (1+cash x)/(g₀ x)^d) →
      let fee := fun x=>4*(2*gross G h 2 order*(1+cash x)/(g₀ x)^(d+2))
      let Z := full S (program) branch (sheet F) (S.payroll (program) G branch (sheet F)) seed b H booked center
      ∀ e, e ≤ order → ∀ᶠ t : ℕ in atTop, ∀ x, report x=t →
        ∀ N per : ℕ, B.reporter+t ≤ N →
        let g := regulatorRun C.family N per (B.reporter+t)
        fee x ≤ (g^debt)⁻¹ →
        ‖(b.after.expanse L).vista T Z M x e -
          note (Z.point ((WilsonIndependentFreshScalar.remaining b last).choose x) e 0)‖ ≤ g^P := by
  obtain ⟨first,ready⟩:=WilsonIndependentCompleteFiniteTerminal.original (X:=X) C D elected paid slow
    branch order u P debt
  refine ⟨first,?_⟩
  intro stage late B
  obtain ⟨v,plan⟩:=ready stage late B
  refine ⟨v,?_⟩
  intro report m j w S b last color F notebook
  obtain ⟨seed,opens⟩:=plan report color F notebook
  refine ⟨seed,?_⟩
  intro L T M h H booked center interior β g₀ cash above purchased gp cp heat d income fee Z
  let quiet:=S.payroll (program) G branch (sheet F)
  let lots:=part S (program) branch (sheet F) quiet seed b H booked center
  let film (x:X)(s:Portions H):=Halo.convey
    ((WilsonThermometerUnitFilingPinBalance.pin S (program) branch (sheet F) b center) x)
    (WilsonThermometerUnitFilingCoverAudition.bank (H x).rows (s x) (H x).test (H x).read)
  have born (x:X)(s:Portions H):=WilsonThermometerUnitFilingPinRegister.enrolled S (program) branch
    (sheet F) quiet seed b H booked center s x
  have start:=WilsonThermometerUnitFilingPinRegister.entry S (program) branch (sheet F) quiet seed b H booked center
  have positive (x:X):0 ≤ fee x:=by
    have h0:0 ≤ gross G h 2 order:=Finset.sum_nonneg (fun i _=>sign h 2 i)
    have hx:=gp x
    have hc:=cp x
    dsimp [fee]
    positivity
  apply opens (Portions H) h h lots Z film born atTop start center interior fee positive
  intro choose i hi r _
  have earned:=WilsonThermometerUnitFilingPinRegister.quoted S (program) branch (sheet F) quiet seed b
    H booked center (WilsonIndependentCapturedCalendar.meter C D m j w) β g₀ cash above purchased
    gp cp heat d income order i r 2 hi choose
  have amount (x:X): ENNReal.ofReal (fee x)=
      ENNReal.ofReal (2*gross G h 2 order*(1+cash x)/(g₀ x)^(d+2))*(2:ℝ≥0∞)^2:=by
    dsimp [fee];rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (4:ℝ)),mul_comm];norm_num
  simpa only [amount] using earned

end YM.Integration.WilsonThermometerUnitFilingPinProgram
