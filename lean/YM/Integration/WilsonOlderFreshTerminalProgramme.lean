import YM.Integration.WilsonThermometerUnitFilingPinProgram
import YM.Integration.WilsonOlderFreshTerminalClock

/-! Continue the complete enrolled one-name word, including its scalar,
from the physical stop through the independently normalized finite integral. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOlderFreshTerminalProgramme
open WilsonIndependentCapturedTerminal
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Budget RegulatorIR.Spatial RegulatorIR.Uniform
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Epoch RegulatorIR.Calibration RegulatorIR.Profiles RegulatorIR.Taping
open RegulatorIR.Binding RegulatorIR.Geometry RegulatorIR.Halo RegulatorIR.FVAAlt2
open WilsonPositionProgramReporterBand WilsonIndependentCapturedPages Pert.Asymptotics
open WilsonThermometerUnitFilingCoverRegister (Submission)
open WilsonThermometerUnitFilingCoverCurrency (gross)
open WilsonThermometerUnitFilingPinRegister (full)
open scoped BigOperators ENNReal Classical Topology
variable {G : Gauge} (R : Run G) (D : XSpace.Run) {X : Type}
local notation "program" => Oracle.books R.family.path.levels.clock.kernel

def series (order : ℕ) (g : ℝ) (f : ℕ → ℝ) : ℝ := ∑ e ∈ Finset.range (order+1), g^e*f e

theorem polynomial (order : ℕ) {g fare : ℝ} (gp : 0 ≤ g) (small : g ≤ 1)
    (f h : ℕ → ℝ) (paid : ∀ e ≤ order, ‖f e-h e‖ ≤ fare) :
    ‖series order g f-series order g h‖ ≤ (order+1:ℕ)*fare := by
  unfold series
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ e ∈ Finset.range (order+1), ‖g^e*f e-g^e*h e‖ := norm_sum_le _ _
    _ ≤ ∑ e ∈ Finset.range (order+1), fare := by
      apply Finset.sum_le_sum
      intro e he
      rw [←mul_sub,norm_mul,Real.norm_of_nonneg (pow_nonneg gp _)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ gp small)).trans
        (paid e (Nat.le_of_lt_succ (Finset.mem_range.mp he)))
    _ = _ := by simp

theorem original {simple : G.Simple} {axis : Axis} {ε : ℝ}
    (elected : WilsonPositionProgramNestedElection.course simple axis ε R.kit)
    (paid : WilsonPositionProgramStageInvoice.Requested R.kit)
    (slow : WilsonWindowReportingPace.Slow R.kit)
    (branch : ∀ patch : Patch, patch.Branches R.family.path.levels.clock.kernel G)
    (order u P loss debt : ℕ) :
    let reserve := debt+4*(P+loss)
    ∃ first : ℕ, ∀ stage ≥ first, ∀ B : Band R D stage,
    ∃ v : Stop R D B u (reserve+P+1), ∀ report : X → ℕ,
      let m := B.lower ∘ report
      let j := B.span ∘ report
      let w := B.powers ∘ report
      let S := WilsonPositionProgramInfraredCircuit.circuit R D m j w (fun x => B.blocks (report x))
      let b := birth R D v report
      let last := stopped R D v report
      ∀ (color : G.ColorIndex) (F : Tent j), Notebook S (program) G branch color (Rocket.native j) F order →
      ∃ seed : (S.dialect (program) G branch (sheet F)).Primitive
          (WilsonIndependentCapturedCalendar.meter R D m j w) order (quantum 1 0),
      let L := S.dialect (program) G branch (sheet F)
      let T := b.after.part L (S.payroll (program) G branch (sheet F)) seed
      let M := WilsonIndependentFreshReel.margins (S.lane (program) G branch (sheet F)) b.after
      ∀ (h : ℕ) (H : X→Submission G) (booked : ∀ x, (H x).grades ()+1=h)
        (center : X→Room), L.cushion (1/8) center →
      ∀ β g₀ cash : X→ℝ, (∀ x, Real.exp 1 ≤ β x) → (∀ x, Real.exp ((H x).σ⁻¹^2) ≤ β x) →
        (∀ x, 0<g₀ x) → (∀ x, 0 ≤ cash x) → (∀ x, β x*(g₀ x)^2 ≤ 2) →
      ∀ d : ℕ, (∀ x,(H x).cost/((H x).rad ()) ≤ (1+cash x)/(g₀ x)^d) →
      let fee := fun x=>4*(2*gross G h 2 order*(1+cash x)/(g₀ x)^(d+2))
      let Z := full S (program) branch (sheet F) (S.payroll (program) G branch (sheet F)) seed b H booked center
      ∀ᶠ t : ℕ in atTop, ∀ x, report x=t → ∀ N per : ℕ, B.reporter+t ≤ N →
        let g := regulatorRun R.family N per (B.reporter+t)
        let weak := fun e => note (Z.point ((WilsonIndependentFreshScalar.remaining b last).choose x) e 0)
        let terminal := (b.after.expanse L).vista T Z M x
        fee x ≤ (g^debt)⁻¹ →
        (∀ e ≤ order, ‖terminal e-weak e‖ ≤ g^P) ∧
          ‖series order g terminal-series order g weak‖ ≤ (order+1:ℕ)*g^P := by
  intro reserve
  obtain ⟨first,open₀⟩ := WilsonThermometerUnitFilingPinProgram.original (X:=X) R D
    elected paid slow branch order u P reserve
  refine ⟨first,?_⟩
  intro stage paidStage B
  obtain ⟨v,choice⟩ := open₀ stage paidStage B
  refine ⟨v,?_⟩
  intro report m j w S b last color F book
  obtain ⟨seed,scheduled⟩ := choice report color F book
  refine ⟨seed,?_⟩
  intro L T M h H booked center inside β g₀ cash late strip positive nonneg thermal d funded fee Z
  have issued := scheduled h H booked center inside β g₀ cash late strip positive nonneg thermal d funded
  have all := (Finset.range (order+1)).eventually_all.mpr
    (fun e he => issued e (Nat.le_of_lt_succ (Finset.mem_range.mp he)))
  filter_upwards [all,v.heard] with t byGrade stop
  intro x test N per live g weak terminal purchase
  obtain ⟨gp,small,_,_⟩ := stop.2 N per live
  have ratio : g^reserve ≤ g^debt := pow_le_pow_of_le_one gp.le small (Nat.le_add_right ..)
  have cap : fee x ≤ (g^reserve)⁻¹ :=
    purchase.trans ((inv_le_inv₀ (pow_pos gp _) (pow_pos gp _)).mpr ratio)
  have coeff (e : ℕ) (he : e ≤ order) : ‖terminal e-weak e‖ ≤ g^P :=
    byGrade e (Finset.mem_range.mpr (Nat.lt_succ_of_le he)) x test N per live cap
  exact ⟨coeff,polynomial order gp.le small terminal weak coeff⟩

end YM.Integration.WilsonOlderFreshTerminalProgramme
