import YM.Integration.WilsonIndependentCapturedCalendar
import YM.Integration.WilsonIndependentFreshAppointment
import YM.Integration.WilsonIndependentFreshEndInvoice
import YM.Integration.WilsonPositionProgramInfraredAtlas

/-! The scalar continuation uses the actual selected variable-block schedule.
Its global meter charges the logarithm of the scale ratio and is independent
of the number of copies of the physical torus. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonIndependentFreshHaarCalendar
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
      ∀ (root : X → Room), (S.dialect (program) G branch (sheet F)).cushion (1/8) root → ∀ (gross : X → ℝ), (∀ x, 0 ≤ gross x) →
        (∀ i, i ≤ p → ∀ r, 0 < r → Claim (meter C D m j w)
          (fun x => (S.dialect (program) G branch (sheet F)).coverQ root 2 (capture.choose x))
          (fun x => ENNReal.ofReal (gross x)) (fun x => Z.main (Page.opening capture.after.spans x) i r)) →
        capture.age ≤ stop.age → ∀ e, e ≤ p → ∃ K : ℝ, ∃ h : ℕ, 0 ≤ K ∧ ∀ x,
        ‖(capture.after.expanse (S.dialect (program) G branch (sheet F))).vista
            (capture.after.part (S.dialect (program) G branch (sheet F)) (S.payroll (program) G branch (sheet F)) seed) Z
            (WilsonIndependentFreshReel.margins (S.lane (program) G branch (sheet F)) capture.after) x e - note (Z.main ((WilsonIndependentFreshScalar.remaining capture stop).choose x) e 0)‖ ≤
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
  obtain ⟨_,finish⟩ := WilsonIndependentFreshEndInvoice.original S (program) branch simple
    (show quantum 1 0 ≤ Lodge.through p by simp [quantum,Lodge.through])
    (stages m j w blocks late) notebook peak opening (age C D m j w blocks) D.finalSide.side.val
    (fun x => (congrArg Subtype.val (WilsonPositionProgramInfraredCircuit.finalSide D j w x)).le)
  refine ⟨seed,?_⟩
  intro arity offset capture stop Z portrait actual root inside gross hg bounds order e he
  let A := meter C D m j w
  let price x := gross x * (S.l (capture.choose x) / S.l (stop.choose x))^(1/2:ℝ)
  have hprice (x : X) : 0 ≤ price x := by
    apply mul_nonneg (hg x)
    exact Real.rpow_nonneg (div_nonneg ((S.dialect (program) G branch (sheet F)).hl _).le ((S.dialect (program) G branch (sheet F)).hl _).le) _
  let endVal x := (capture.after.expanse (S.dialect (program) G branch (sheet F))).vista
    (capture.after.part (S.dialect (program) G branch (sheet F)) (S.payroll (program) G branch (sheet F)) seed) Z
    (WilsonIndependentFreshReel.margins (S.lane (program) G branch (sheet F)) capture.after) x e
  let cov x := note (Z.main (Page.finallyW capture.after.spans x) e 0)
  let weak x := note (Z.main ((WilsonIndependentFreshScalar.remaining capture stop).choose x) e 0)
  have fin := finish arity offset capture stop Z portrait actual root inside (fun x => ENNReal.ofReal (gross x))
    (fun _ => ENNReal.ofReal_ne_top) bounds (fun _ => Nat.zero_le _) order e he
  have hfin : Carry A (fun x => ENNReal.ofReal (price x)) (fun x => ‖endVal x - cov x‖ₑ) := by
    simpa only [price,ENNReal.ofReal_mul (hg _)] using fin
  obtain ⟨a,i,ha,left⟩ := RegulatorIR.Centered.Carry_rt hprice hfin
  obtain ⟨b,k,hb,right⟩ := heard arity offset capture stop Z portrait actual root gross hg bounds order e he
  refine ⟨a+b,max i k,add_nonneg ha hb,?_⟩
  intro x
  let f := fare C D m j w x
  have one : 1 ≤ f := fare_one C D m j w x
  have eval : (A.val x).toReal = f := ENNReal.toReal_ofReal (le_trans zero_le_one one)
  have hi : f^i ≤ f^(max i k) := pow_le_pow_right₀ one (le_max_left ..)
  have hk : f^k ≤ f^(max i k) := pow_le_pow_right₀ one (le_max_right ..)
  have hL : ‖endVal x-cov x‖ ≤ a*f^i*price x := by simpa only [eval] using left x
  have hR : ‖cov x-weak x‖ ≤ b*f^k*price x := by simpa only [show ((meter C D m j w).val x).toReal = f from eval] using right x
  calc
    _ ≤ ‖endVal x-cov x‖ + ‖cov x-weak x‖ := by
      simpa only [dist_eq_norm] using dist_triangle (endVal x) (cov x) (weak x)
    _ ≤ a*f^i*price x + b*f^k*price x := add_le_add hL hR
    _ ≤ a*f^(max i k)*price x + b*f^(max i k)*price x := by
      have px := hprice x
      gcongr
    _ = _ := by change _ = (a+b)*f^_*price x; ring

end YM.Integration.WilsonIndependentFreshHaarCalendar
