import YM.Integration.WilsonIndependentConditionalDiagramResponse
import YM.Integration.WilsonIndependentPublicCoverCruise
import YM.WilsonCoeffUV.VacuumLaw

/-! The marked free diagram on an actual finite Spout page, including its own kinetic reset. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalVerse
open Lattice RG WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil
open WilsonCoeffUV.Shard FreeResolvent RegulatorIR RegulatorIR.Ledger RegulatorIR.Oracle
open Laurent Bloch Exterior Stationary Work.F08 Matrix Metric Precision Next.Free Tree
open Embroider Embroider.Canvas
variable {G:Gauge}{Ω:Type}{M:Ω→ℕ}{n:Page M→Side}

theorem original (A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    {m N k:ℕ}(finer:m<N)(c:Side)(Z:Era G ℝ)(source:Auth (k+1) Z):
    let P:=loose A m; let S:=mStep A c m;let F:=repeatF S
    let H:=freeForms A N (m+1);let Q:=roam A N m c
    let V:=(story A Ñ N (m+1)).1 (c*P.L)
    let D:=WilsonIndependentConditionalDiagramResponse.response S F H Q Ñ V (Z.1 (c*P.L)) (k+1)
    Blue.redo (ratioHigh A Ñ N m) (Blue.projectZero D)=Blue.flash ((verseI A Ñ m N (k+1) Z).1 c) :=by
  intro P S F H Q V D
  have hv:= (old A Ñ simple ratio N (m+1) finer).basis (c*P.L)
  have marked:=WilsonIndependentConditionalDiagramResponse.original S F H Q hv.lamp ratio (source.span _)
    (A.blocks m 0).branches (Bank.age_sym A N (m+1) (c*P.L)) hv.shape (source.pale _)
    (Convention.tree_pos A m N rfl)
  rw [show Blue.projectZero D=Blue.flash (reed S F H Q Ñ V (k+1) (Z.1 (c*P.L))) from marked,
      Blue.redo_stern _ (reed_band S F H Q _ hv.lamp ratio (source.span _))]
  rfl

end YM.Integration.WilsonIndependentConditionalVerse
