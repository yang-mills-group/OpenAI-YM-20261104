import YM.Integration.WilsonIndependentCapturedCalendar
import YM.Integration.WilsonIndependentFreshAppointment
import YM.Integration.WilsonPositionProgramInfraredAtlas

/-! The scalar continuation uses the actual selected variable-block schedule.
Its global meter charges the logarithm of the scale ratio and is independent
of the number of copies of the physical torus. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonIndependentFreshCalendar
open WilsonIndependentCapturedCalendar
open Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Budget RegulatorIR.Spatial RegulatorIR.Uniform
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Epoch RegulatorIR.Calibration RegulatorIR.Profiles RegulatorIR.Taping
open RegulatorIR.Binding RegulatorIR.Geometry RegulatorIR.Halo RegulatorIR.FVAAlt2
open WilsonPositionProgramCommonWindow WilsonPositionProgramVariableCircuit
open scoped ENNReal Classical
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type}
variable (m j : X → ℕ) (w : X → ℕ → ℕ)
    (blocks : ∀ x k, (C.family.S.block (m x+k)).val = D.ratio^(w x k))
local notation "circuit" => WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
local notation "atlas" => WilsonPositionProgramInfraredAtlas.budget C D m j w blocks
local notation "program" => Oracle.books C.family.path.levels.clock.kernel
local notation "birth" => Rocket.native j

/-- Stage enrollment precedes every cutoff and every choice of a physical
test. The only source-specific numerical hypothesis here is the tariff for
positive angular ranks at capture. -/
theorem original {simple : G.Simple} {axis : Axis} {ε : ℝ}
    (first : WilsonPositionProgramNestedElection.course simple axis ε C.kit)
    (paid : WilsonPositionProgramStageInvoice.Requested C.kit) (slow : WilsonWindowReportingPace.Slow C.kit)
    (branch : ∀ patch : Patch, patch.Branches C.family.path.levels.clock.kernel G) (p : ℕ) :
    ∃ start : ℕ, ∀ (m j : X → ℕ) (w : X → ℕ → ℕ)
      (blocks : ∀ x k, (C.family.S.block (m x+k)).val = D.ratio^(w x k)), (∀ x, start ≤ m x) →
      let S := WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
      ∀ (color : G.ColorIndex) (F : Tent j), Notebook S (program) G branch color (Rocket.native j) F p →
      ∃ seed : (S.dialect (program) G branch (sheet F)).Primitive (meter C D m j w) p (quantum 1 0),
      ∀ (arity offset : ℕ) (capture stop : Choice j)
        (Z : (capture.after.part (S.dialect (program) G branch (sheet F))
          (S.payroll (program) G branch (sheet F)) seed).Report arity)
        (portrait : X → Portrait G), (∀ x, BasisT arity offset (portrait x) (Z.main (Page.opening capture.after.spans x))) →
      ∀ (root : X → Room) (gross : X → ℝ), (∀ x, 0 ≤ gross x) →
        (∀ i, i ≤ p → ∀ r, 0 < r → Claim (meter C D m j w)
          (fun x => (S.dialect (program) G branch (sheet F)).coverQ root 2 (capture.choose x))
          (fun x => ENNReal.ofReal (gross x)) (fun x => Z.main (Page.opening capture.after.spans x) i r)) →
        capture.age ≤ stop.age → ∀ e, e ≤ p → ∃ K : ℝ, ∃ h : ℕ, 0 ≤ K ∧ ∀ x,
        ‖note (Z.main (Page.finallyW capture.after.spans x) e 0) - note (Z.main ((WilsonIndependentFreshScalar.remaining capture stop).choose x) e 0)‖ ≤
          K * (fare C D m j w x)^h * (gross x * (S.l (capture.choose x) / S.l (stop.choose x))^(1/2:ℝ)) := by
  obtain ⟨start, stages⟩ := WilsonPositionProgramInfraredAtlas.purchased (X:=X) C D first paid slow branch p
  refine ⟨start,?_⟩
  intro m j w blocks late S color F notebook
  have opening (x : X) : S.l ((Rocket.native j).choose x) = 1 := by
    exact div_self (by exact_mod_cast (WilsonPositionProgramInfraredCircuit.count D j w (Page.opening j x)).property.ne')
  have peak (x : X) : (WilsonPositionProgramInfraredAtlas.budget C D m j w blocks).peak ((Rocket.native j).choose x) = 0 := by
    change Real.log (S.l ((Rocket.native j).choose x)) = 0
    rw [opening,Real.log_one]
  obtain ⟨seed,heard⟩ := WilsonIndependentFreshAppointment.original S (program) branch simple
    (show quantum 1 0 ≤ Lodge.through p by simp [quantum,Lodge.through])
    (stages m j w blocks late) notebook peak opening (age C D m j w blocks)
  refine ⟨seed,?_⟩
  intro arity offset capture stop Z portrait actual root gross hg bounds order e he
  have answer := heard arity offset capture stop Z portrait actual root gross hg bounds order e he
  simpa only [meter,ENNReal.toReal_ofReal (le_trans zero_le_one (fare_one C D m j w _))] using answer

end YM.Integration.WilsonIndependentFreshCalendar
