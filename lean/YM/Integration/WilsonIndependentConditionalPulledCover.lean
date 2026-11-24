import YM.Integration.WilsonIndependentConditionalPulledBoard
import YM.Integration.WilsonIndependentConditionalOrdinaryCover

/-! The genuine finite and covered receiving tensors, obtained from the unshifted heat followed by the released mean on every board. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalPulledCover
open Lattice RG WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil
open WilsonCoeffUV.Shard FreeResolvent RegulatorIR RegulatorIR.Ledger RegulatorIR.Oracle
open Laurent Bloch Exterior Stationary Work.F08 Matrix Metric Precision Next.Free Tree
open WilsonCoeffUV.Blue Embroider Embroider.Canvas PowerSeries
variable {G:Gauge}

open WilsonIndependentConditionalHeldGaussian PowerSeries RegulatorIR RegulatorIR.Diagram
theorem received (A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    {m N k:ℕ}(finer:m<N)(c:Side)(Z:Era G ℝ)(source:Auth (k+1) Z):
    let P:=loose A m; let S:=mStep A c m;let F:=repeatF S
    let H:=freeForms A N (m+1);let Q:=roam A N m c
    let V:=(story A Ñ N (m+1)).1 (c*P.L)
    let D:=rated (fun e=>e+(k+1)) (WilsonIndependentConditionalPulledBoard.output S F H Q Ñ V (Z.1 (c*P.L)) (k+1))
    Blue.redo (ratioHigh A Ñ N m) D=Blue.flash ((verseI A Ñ m N (k+1) Z).1 c):=by
  intro P S F H Q V D
  have hv:= (old A Ñ simple ratio N (m+1) finer).basis (c*P.L)
  have marked:=WilsonIndependentConditionalPulledBoard.original S F H Q hv.lamp ratio (source.span _)
    (A.blocks m 0).branches (Bank.age_sym A N (m+1) (c*P.L)) hv.shape (source.pale _)
    (Convention.tree_pos A m N rfl)
  rw [show D=Blue.flash (reed S F H Q Ñ V (k+1) (Z.1 (c*P.L))) from marked,
      Blue.redo_stern _ (reed_band S F H Q _ hv.lamp ratio (source.span _))]
  rfl

def report (A:Levels G)(Ñ:ChartRatio G)(m N k:ℕ)(Z:Era G ℝ)(c:Side):Ink (Woods G c):=
  let P:=loose A m;let S:=mStep A c m;let F:=repeatF S
  let H:=freeForms A N (m+1);let Q:=roam A N m c
  let V:=(story A Ñ N (m+1)).1 (c*P.L)
  redo (ratioHigh A Ñ N m) (rated (fun e=>e+k) (WilsonIndependentConditionalPulledBoard.output S F H Q Ñ V (Z.1 (c*P.L)) k))

theorem finite (A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    {m N k:ℕ}(finer:m<N)(Z:Era G ℝ)(source:Auth (k+1) Z)(c:Side)(i r:ℕ):
    WilsonIndependentConditionalMarkedCover.tensor (report A Ñ m N (k+1) Z c) i r=(verseI A Ñ m N (k+1) Z).1 c i r:=by
  have chart:=Auth.verse A finer simple ratio source
  rw [show report A Ñ m N (k+1) Z c=Blue.flash ((verseI A Ñ m N (k+1) Z).1 c)
       from received A simple ratio finer c Z source]
  exact WilsonIndependentConditionalMarkedCover.reads (chart.span c) (chart.pale c) i r

theorem original (A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    {m N k:ℕ}(finer:m<N)(Z:Era G ℝ)(source:Auth (k+1) Z)(i r:ℕ):
    Bends 0 (fun c=>WilsonIndependentConditionalMarkedCover.tensor (report A Ñ m N (k+1) Z c) i r) ((verseI A Ñ m N (k+1) Z).2 i r):=by
  simpa only [finite A simple ratio finer Z source] using (Auth.verse A finer simple ratio source).wing i r

end YM.Integration.WilsonIndependentConditionalPulledCover
