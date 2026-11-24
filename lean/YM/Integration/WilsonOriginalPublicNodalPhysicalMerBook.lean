import YM.Integration.WilsonOriginalPublicNodalPhysicalNote
import YM.Integration.WilsonIndependentNotebookMarkedEdge

/-! Elect a priced physical-prefix helper whose complete marked history is the originally supplied train. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalPhysicalMerBook
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

local notation "originals" => (fun _:X=>R.family.path.levels)
open WilsonOriginalPublicNodalPhysicalNote (Funded)
open WilsonIndependentSpoutPayrollRoute (reported)

theorem aligned (x:X):
    WilsonIndependentPublicFreeTrain.Matches R.family.path.levels (C) R.family.path.levels.clock.kernel (m x) x:=by
  refine ⟨rfl,?_,?_⟩
  · intro v hv
    subst x;rfl
  · intro f hf
    subst x
    exact (WilsonPositionProgramInfraredCircuit.history R V m j w blocks).pact f 0

structure Issued (p:ℕ)(F:Tent j):Prop where
  book (col:G.ColorIndex):Notebook (C) (Y) G Z col (Rocket.native j) F p
  flat (x:X):sheet F (Page.opening j x)=Clocks.flat
  old (v:Page j):RegulatorIR.Clocks.Matches p (((C).payroll (Y) G Z (sheet F)).bulk v)
    (reported originals m v)
  conditional (f:Flap j)(n:Side):WilsonIndependentSpoutMeasuredHearing.Hearing (C) Z F f
    R.family.path.levels (m f.volW) p n
  marked (f:Flap j):WilsonIndependentNotebookMarkedEdge.Reads (C) (Y) Z F originals m p f
  funded (i:X → ℕ)(H:ℝ):Funded R V m j w blocks Z p i H F

include col in
theorem original (simple:G.Simple)(p:ℕ){axis:Axis}{ε:ℝ}
    (first:WilsonPositionProgramNestedElection.course simple axis ε R.kit)
    (sale:WilsonPositionProgramStageInvoice.Requested R.kit)(slow:WilsonWindowReportingPace.Slow R.kit):
    ∃base:ℕ,∀(m j:X → ℕ)(w:X → ℕ → ℕ)
      (blocks:∀x k,(R.family.S.block (m x+k)).val=V.ratio^(w x k)),(∀x,base ≤ m x) →
        ∃F:Tent j,Issued R V m j w blocks Z p F:=by
  obtain ⟨base,paid⟩:=WilsonPositionProgramInfraredAtlas.purchased (X:=X) R V first sale slow Z p
  refine ⟨base,?_⟩
  intro m j w blocks old
  let circuit:=WilsonPositionProgramInfraredCircuit.circuit R V m j w blocks
  obtain ⟨F,books,previous,_,hearing,reads⟩:=WilsonIndependentNotebookMarkedEdge.selected circuit (Y) Z
    (fun _:X=>R.family.path.levels) m simple (aligned R V m j w blocks) p
  refine ⟨F,books,?_,previous,hearing,reads,?_⟩
  · intro x
    change (F (Page.opening j x)).scale=_
    rw [show F (Page.opening j x)=Calibration.dawn from (books col).reference x]
    exact Rocket.still
  · intro i H
    exact WilsonOriginalPublicNodalPhysicalNote.appointed R V m j w blocks Z col p simple i H F
      (paid m j w blocks old) (books col)

end YM.Integration.WilsonOriginalPublicNodalPhysicalMerBook
end
