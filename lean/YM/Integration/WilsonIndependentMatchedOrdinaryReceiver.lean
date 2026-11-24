import YM.Integration.WilsonIndependentConditionalPulledCover
import YM.Integration.WilsonIndependentConditionalInsertion
import YM.Integration.WilsonIndependentMatchedOrdinaryProfile

/-! Evaluation of a complete finite ordinary source before and after the
measured kinetic reversion, with the identical unmarked denominator. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentMatchedOrdinaryReceiver
open Lattice RG WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil
open WilsonCoeffUV.Shard FreeResolvent RegulatorIR RegulatorIR.Ledger RegulatorIR.Oracle
open Laurent Bloch Exterior Stationary Work.F08 Matrix Metric Precision Next.Free Tree
open WilsonCoeffUV.Blue Embroider Embroider.Canvas PowerSeries MeasureTheory
open WilsonCoeffUV.Convention WilsonIndependentConditionalInsertion RegulatorIR.Diagram
open PertExtension PertExtension.GaussianScore
open scoped Classical BigOperators MatrixOrder
variable {G:Gauge}

def denominator (A:Levels G)(Ñ:ChartRatio G)(m N:ℕ)(c:Side)
    (ν:Measure (Lawn (Active G (repeatF (mStep A c m)))))(y:Woods G c→ℝ):PowerSeries ℝ:=
  let S:=mStep A c m;let F:=repeatF S; let Q:=roam A N m c
  let V:=(story A Ñ N (m+1)).1 (c*(loose A m).L)
  read (Convention.tree_pos A m N rfl) ν y (raiseE (shot S F Q Ñ V))

def numerator (A:Levels G)(Ñ:ChartRatio G)(m N:ℕ)(c:Side)
    (ν:Measure (Lawn (Active G (repeatF (mStep A c m)))))(y:Woods G c→ℝ)
    (P:Ink (Woods G (c*(loose A m).L))):PowerSeries ℝ:=
  let S:=mStep A c m;let F:=repeatF S;let Q:=roam A N m c
  let V:=(story A Ñ N (m+1)).1 (c*(loose A m).L)
  let inlet:=loom (camSlice G S F (extractV G S F Q)) P
  read (Convention.tree_pos A m N rfl) ν y (raiseE (shot S F Q Ñ V)*inlet)

def before (A:Levels G)(Ñ:ChartRatio G)(m N k:ℕ)(c:Side)(Z:Era G ℝ):Ink (Woods G c):=
  let S:=mStep A c m;let F:=repeatF S;let H:=freeForms A N (m+1);let Q:=roam A N m c
  let V:=(story A Ñ N (m+1)).1 (c*(loose A m).L)
  flash (reed S F H Q Ñ V k (Z.1 (c*(loose A m).L)))

theorem dated (A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    {m N k:ℕ}(finer:m<N)(c:Side)(Z:Era G ℝ)(paid:Auth k Z)
    (P:Ink (Woods G (c*(loose A m).L)))(given:flash (Z.1 (c*(loose A m).L))=P):
    (∀ (ν:Measure (Lawn (Active G (repeatF (mStep A c m))))) [ν.HasTemperateGrowth]
        [ν.IsAddRightInvariant] [NeZero ν] (y:Woods G c→ℝ),
        constantCoeff (denominator A Ñ m N c ν y)=1 ∧
        numerator A Ñ m N c ν y P=denominator A Ñ m N c ν y*
          PowerSeries.map (emphasis y).toRingHom (before A Ñ m N k c Z)) ∧
        Blue.redo (ratioHigh A Ñ N m) (before A Ñ m N k c Z)=
          Blue.flash ((verseI A Ñ m N k Z).1 c):=by
  let S:=mStep A c m;let F:=repeatF S;let H:=freeForms A N (m+1);let Q:=roam A N m c
  have hv:=(old A Ñ simple ratio N (m+1) finer).basis (c*(loose A m).L)
  refine ⟨?_,?_⟩
  · intro ν _ _ _ y
    have h:=WilsonIndependentConditionalInsertion.original S F H Q (Convention.tree_pos A m N rfl)
      ν hv.lamp ratio (paid.span _) (A.blocks m 0).branches (Bank.age_sym A N (m+1) _) hv.shape (paid.pale _) y
    dsimp only at h
    rw [WilsonIndependentConditionalInsertion.zero,WilsonIndependentConditionalInsertion.one,given] at h
    exact ⟨h.1,(h.2 _).2 rfl⟩
  · unfold before
    rw [Blue.redo_stern _ (reed_band S F H Q _ hv.lamp ratio (paid.span _))]
    rfl

end YM.Integration.WilsonIndependentMatchedOrdinaryReceiver
