import YM.Integration.WilsonIndependentMatchedOpeningCover
import YM.Integration.WilsonIndependentMatchedOpeningRoster
/-! The issued normalized finite R/W group stencils form the precise opening of the actual marked Notebook. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOpeningComplete
open Function Filter Finset PowerSeries Lattice RG Wilson Tree Source Labels XSpace XSpace.Rose Gauge
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Bank
open PertExtension RegulatorIR RegulatorIR.Geometry RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Prim RegulatorIR.Diagram RegulatorIR.Halo RegulatorIR.Oracle RegulatorIR.Cluster
open RegulatorIR.Diagram RegulatorIR.Ward RegulatorIR.Oracle RegulatorIR.Prim RegulatorIR.Ledger RegulatorIR.Clocks RegulatorIR.Calibration
open WilsonIndependentRawRosterWord (bank degree)
open WilsonIndependentMatchedOpeningRoster (field)
open scoped Classical
variable {G:Gauge}{I:Type}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
    (σ:I→Bool)(d:I→ℕ)(key:∀i,(R.family.labels.level (d i)).Index)
    {E:I→ℕ}(cut:∀i,d i<E i)

theorem original (J:Composite I)(o:I→ Cover){H:Type}{L:H→ℕ}(A:H→Levels G)(s:H→ℕ)(w:H):
    Auth (J.accounts (degree R d key)) (field R W σ d key cut o J) ∧
    bank R W σ d key J o=WilsonIndependentNotebookPayrollMark.source
      A s (Page.opening L w) (field R W σ d key cut o J):=by
  have auth:=WilsonIndependentMatchedOpeningRoster.enrolled R W σ d key cut o J
  have raw:=WilsonIndependentRawRosterWord.enrolled R W σ d key J o
  exact ⟨auth,WilsonIndependentMatchedOpeningCover.source _ _
    (WilsonIndependentMatchedOpeningCover.recover _ _ auth raw.1.canopy raw.1.symmetry raw.2
      (WilsonIndependentMatchedOpeningRoster.ray R W σ d key cut J o)) A s w⟩

theorem measured (J:Composite I)(o:I→ Cover){H:Type}{L:H→ℕ}(A:H→Levels G)(s:H→ℕ)(w:H)(p:ℕ):
    RegulatorIR.Clocks.Matches p (bank R W σ d key J o) (WilsonIndependentNotebookPayrollMark.source
      A s (Page.opening L w) (field R W σ d key cut o J)):=by
  intro j _
  exact congrFun (original R W σ d key cut J o (L:=L) A s w).2 j
end YM.Integration.WilsonIndependentMatchedOpeningComplete
