import YM.Integration.WilsonPositionProgramVariableCircuit
import YM.FVAAlt2.Sound.Figure
import YM.FVAAlt2.Pipeline.Readers
import YM.FVAAlt2.Pipeline.Urban
import YM.FVAAlt2.Sound.Tender

/-! Original signed planted rosters on the variable chronological block circuit. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramVariableHistory
open Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.FVAAlt2
open RegulatorIR.FVAAlt2.Period.Field RegulatorIR.FVAAlt2.Pipeline
open WilsonPositionProgramVariableCircuit
open RegulatorIR.Calibration
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type} (m j : X → ℕ) (w : X → ℕ → ℕ)
    (blocks : ∀ x k, (C.family.S.block (m x+k)).val=D.ratio^(w x k))
    (branch : ∀ P : RG.Patch, P.Branches C.family.path.levels.clock.kernel G)
    {I : Type} [Fintype I] [LinearOrder I] (d : I → ℕ)
    (v : ∀ a, (C.family.labels.level (d a)).Index) (z : X → I → Cover)
    {A : Type} [Fintype A] [DecidableEq A] (mask : Marker.Census A) (u : A)
local notation "H" => history C D m j w blocks
local notation "E" => circuit C D m j w blocks
local notation "K" => RunFormalChain.fromRun C
local notation "Y" => RegulatorIR.Oracle.books C.family.path.levels.clock.kernel
local notation "src" => Sound.Figure.prop C z d v

/-- The independent kinetic file on the common variable circuit precedes the physical period.
Every literal bare roster is propagated on the actual signed finite Wilson chain. -/
theorem roster (color : G.ColorIndex) (r : ℕ) :
    ∃ F : Tent j, Notebook E Y G branch color (Rocket.native j) F r ∧
      ∃ T : See.Times (sheet F) r, ∀ per, ∃ U : See.Agenda H mask per,
        See.Setup K H mask u src (sheet F) per r T U ∧
        ∀ (b : Page j) e, e ≤ r → See.prime H mask u (sheet F) per r T U (x:=b) 0 e =
          ((See.observe branch K H src (sheet F) per b e 0 Fin.elim0 : ℝ) : ℂ) := by
  obtain ⟨F,hF⟩ := Calibration.tomorrows E Y G branch color (Rocket.native j) r
  have start := Sound.flatTop Y branch hF
  obtain ⟨T,_⟩ := See.prices (sheet F) r start
  refine ⟨F,hF,T,?_⟩
  intro per
  obtain ⟨U,hU⟩ := See.hire Y branch K H mask u src (sheet F) per r T start
  exact ⟨U,hU,fun b _ he => See.scalar_here Y branch K H mask u src (sheet F) per r T start hU b he⟩

end YM.Integration.WilsonPositionProgramVariableHistory
end
