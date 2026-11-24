import YM.Integration.WilsonPositionProgramInfraredMeter
import YM.Integration.WilsonIndependentGroupedOrbitBills
import YM.Integration.WilsonOriginalPublicNodalSafeCenter

/-! Full physical-prefix orbit on the helper's genuine side, funded on the original variable-block course. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalPhysicalNote
open Set Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.FVAAlt2
open RegulatorIR.FVAAlt2.Kick RegulatorIR.Atlas RegulatorIR.Calibration RegulatorIR.Taping
open RegulatorIR.Budget RegulatorIR.Budget.Layer RegulatorIR.Epoch RegulatorIR.Prim RegulatorIR.Geometry
open RegulatorIR.Prim RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Momentum RegulatorIR.Ledger.Sky
open Next.Foundations
open scoped Classical ENNReal NNReal
variable {G:Gauge}(R:Run G)(V:XSpace.Run){X:Type}
    (m j:X → ℕ)(w:X → ℕ → ℕ)(blocks:∀x k,(R.family.S.block (m x+k)).val=V.ratio^(w x k))
local notation "C" => WilsonPositionProgramInfraredCircuit.circuit R V m j w blocks
local notation "Y" => Oracle.books R.family.path.levels.clock.kernel
local notation "B" => WilsonPositionProgramInfraredAtlas.budget R V m j w blocks
variable (Z:∀P:Patch,P.Branches R.family.path.levels.clock.kernel G)(col:G.ColorIndex)(p:ℕ)

def Funded (i:X → ℕ)(H:ℝ)(F:Tent j):Prop:=
  let L:=WilsonPositionProgramInfraredMeter.wallet R V m j w i H
  let T:=(C).lane Y G Z (sheet F)
  let cash:=(C).leadA Y G (Lodge.through p)
  Cylinder T ((C).payroll Y G Z (sheet F)) ((C).pushP Y G) ((C).takeP Y G) L cash p 1 0 ∧
    Lantern ((C).dialect Y G Z (sheet F)) (Rocket.native j) L cash (1/2) ∧ T.Endings L

theorem appointed (simple:G.Simple)(i:X → ℕ)(H:ℝ)(F:Tent j)
    (pre:SatisfiesQ G Y C Z B p (Lodge.through p) (1/2))
    (book:Notebook C Y G Z col (Rocket.native j) F p):
    Funded R V m j w blocks Z p i H F:=by
  obtain ⟨unit,small⟩:=WilsonPositionProgramInfraredCircuit.units R V m j w blocks
  let L:=WilsonPositionProgramInfraredMeter.wallet R V m j w i H
  have age:=WilsonPositionProgramInfraredMeter.age R V m j w blocks i H
  have zero (x:X):(B).peak ((Rocket.native j).choose x)=0:=by
    change Real.log ((C).l (Page.opening j x))=0
    rw [unit,Real.log_one]
  have cash:=reservations C G Y Z zero age pre col book simple unit
  refine ⟨cash.1.emits (by norm_num) (show quantum 1 0 ≤ Lodge.through p from by
    dsimp [quantum,Lodge.through];omega),cash.2,?_⟩
  obtain ⟨endSide,bounded⟩:=small
  exact closures C G Y Z age pre endSide bounded F

variable {simple:G.Simple}{axis:Axis}{ε:ℝ}
theorem original (first:WilsonPositionProgramNestedElection.course simple axis ε R.kit)
    (sale:WilsonPositionProgramStageInvoice.Requested R.kit)(slow:WilsonWindowReportingPace.Slow R.kit):
    ∃base:ℕ,∀(m j:X → ℕ)(w:X → ℕ → ℕ)
      (blocks:∀x k,(R.family.S.block (m x+k)).val=V.ratio^(w x k)),(∀x,base ≤ m x) →
      let C₀:=WilsonPositionProgramInfraredCircuit.circuit R V m j w blocks
      ∃F:Tent j,Notebook C₀ Y G Z col (Rocket.native j) F p ∧
        (∀x,sheet F (Page.opening j x)=Clocks.flat) ∧
        ∀(i:X → ℕ)(H:ℝ),Funded R V m j w blocks Z p i H F:=by
  obtain ⟨base,paid⟩:=WilsonPositionProgramInfraredAtlas.purchased (X:=X) R V first sale slow Z p
  refine ⟨base,?_⟩
  intro m j w blocks old C₀
  obtain ⟨F,book⟩:=Calibration.tomorrows C₀ Y G Z col (Rocket.native j) p
  refine ⟨F,book,fun x=>?_,fun i H=>appointed R V m j w blocks Z col p simple i H F (paid m j w blocks old) book⟩
  change (F (Page.opening _ x)).scale=_
  rw [show F (Page.opening _ x)=Calibration.dawn from book.reference x]
  exact Rocket.still

end YM.Integration.WilsonOriginalPublicNodalPhysicalNote
end
