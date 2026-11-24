import YM.Integration.WilsonIndependentCapturedAppointment
import YM.Integration.WilsonPositionProgramInfraredAtlas

/-! The scalar continuation uses the actual selected variable-block schedule.
Its global meter charges the logarithm of the scale ratio and is independent
of the number of copies of the physical torus. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonIndependentCapturedCalendar
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

def fare (x : X) : ℝ := 1 + RG16.Lambda C.family.path.levels (m x+j x) +
    Real.log (D.den (elapsed (w x) (j x)) : ℝ)

theorem fare_one (x : X) : 1 ≤ fare C D m j w x := by
  have hden : (1:ℝ) ≤ (D.den (elapsed (w x) (j x)) : ℝ) := by
    exact_mod_cast D.den_pos _
  unfold fare
  linarith [(RG16.Literal.lambda_pos C.family (m x+j x)).le, Real.log_nonneg hden]

def meter : Meter X := ⟨fun x => ENNReal.ofReal (fare C D m j w x),
  fun x => by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (fare_one C D m j w x),
  fun _ => ENNReal.ofReal_ne_top⟩

theorem age : OfAge (atlas) (meter C D m j w) := by
  apply (Poly.roof (coverL j (meter C D m j w))).mono
  intro t
  apply ENNReal.ofReal_le_ofReal
  let a := D.den (elapsed (w t.bindW) (j t.bindW))
  let b := D.den (elapsed (w t.bindW) (remaining j t))
  have ba : b ≤ a := by
    apply Nat.pow_le_pow_right (Nat.zero_lt_of_lt D.large)
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.sub_le ..))
  have hb : (1:ℝ) ≤ b := by exact_mod_cast D.den_pos (elapsed (w t.bindW) (remaining j t))
  have ha : (0:ℝ) < a := by exact_mod_cast D.den_pos _
  have ratio : (circuit).l t = (a:ℝ)/b := by
    change ((D.finalSide.side.val * D.den (elapsed (w t.bindW) (j t.bindW-0)) : ℕ):ℝ) /
      ((D.finalSide.side.val * b : ℕ):ℝ) = _
    simp only [Nat.sub_zero,Nat.cast_mul]
    exact mul_div_mul_left _ _ (by exact_mod_cast D.finalSide.side.property.ne')
  have large : (1:ℝ) ≤ (a:ℝ)/b := (one_le_div (by linarith)).2 (by exact_mod_cast ba)
  have hlog := Real.log_le_log (div_pos ha (by linarith)) (div_le_self ha.le hb)
  change 1+RG16.Lambda C.family.path.levels (m t.bindW+j t.bindW)+|Real.log ((circuit).l t)| ≤
    1+RG16.Lambda C.family.path.levels (m t.bindW+j t.bindW)+Real.log (a:ℝ)
  rw [ratio,abs_of_nonneg (Real.log_nonneg large)]
  linarith

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
      ∀ (arity offset : ℕ) (Z : (S.payroll (program) G branch (sheet F)).Report arity)
        (portrait : X → Portrait G), (∀ x, BasisT arity offset (portrait x) (Z.main (Page.opening j x))) →
      ∀ (capture stop : Choice j) (root : X → Room) (gross : X → ℝ), (∀ x, 0 ≤ gross x) →
        (∀ i, i ≤ p → ∀ r, 0 < r → Claim (meter C D m j w)
          (fun x => (S.dialect (program) G branch (sheet F)).coverQ root 2 (capture.choose x))
          (fun x => ENNReal.ofReal (gross x)) (fun x => Z.main (capture.choose x) i r)) →
        capture.age ≤ stop.age → ∀ e, e ≤ p → ∃ K : ℝ, ∃ h : ℕ, 0 ≤ K ∧ ∀ x,
        ‖note (Z.main (Page.finallyW j x) e 0) - note (Z.main (stop.choose x) e 0)‖ ≤
          K * (fare C D m j w x)^h * (gross x * (S.l (capture.choose x) / S.l (stop.choose x))^(1/2:ℝ)) := by
  obtain ⟨start, stages⟩ := WilsonPositionProgramInfraredAtlas.purchased (X:=X) C D first paid slow branch p
  refine ⟨start,?_⟩
  intro m j w blocks late S color F notebook arity offset Z portrait actual capture stop root gross hg bounds order e he
  have opening (x : X) : S.l ((Rocket.native j).choose x) = 1 := by
    exact div_self (by exact_mod_cast (WilsonPositionProgramInfraredCircuit.count D j w (Page.opening j x)).property.ne')
  have peak (x : X) : (WilsonPositionProgramInfraredAtlas.budget C D m j w blocks).peak ((Rocket.native j).choose x) = 0 := by
    change Real.log (S.l ((Rocket.native j).choose x)) = 0
    rw [opening,Real.log_one]
  have answer := WilsonIndependentCapturedAppointment.original S (program) branch simple
    (show quantum 1 0 ≤ Lodge.through p by simp [quantum,Lodge.through])
    (stages m j w blocks late) notebook peak opening (age C D m j w blocks) Z portrait actual root gross hg bounds order he
  simpa only [meter,ENNReal.toReal_ofReal (le_trans zero_le_one (fare_one C D m j w _))] using answer

end YM.Integration.WilsonIndependentCapturedCalendar

