import YM.Integration.WilsonIndependentMatchedElectedColumn
import YM.Integration.WilsonIndependentMatchedOrdinaryHistory
import YM.WilsonCoeffUV.Marked.Step.Exponential

/-! Genuine proper faces of an ordinary pair. Each input is either absent,
the full submitted group field, its fitted master field, or its signed stable
part. The computed input keeps all existing scalar and lower terms. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentMatchedElectedFaces
open Filter Function Matrix Lattice RG Laurent Bloch Metric FreeResolvent Work.F08
open Wilson Tree Precision AnalyticNext.QuarticMatch.Sheets Exterior Next.Free
open Gauge Source Labels XSpace PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.StableStrip
open WilsonCoeffUV.Wheel.Mark
open PertExtension RegulatorIR RegulatorIR.Diagram MeasureTheory
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentMatchedCensusReceipt (Filed)
open WilsonIndependentMatchedFittedSeat (receiving)
open WilsonIndependentMatchedCoveredSeats (seat)
open scoped Classical BigOperators ContDiff
variable {G:Gauge}

structure Sheet (G:Gauge) where
  grade:ℕ
  field:Era G ℝ
  print:(c:Side)→Ink (Woods G c)
  funded:Auth grade field
  actual c:flash (field.1 c)=print c

def empty : Sheet G:=
  ⟨0,pieceO G,fun _=>1,piece_auth,fun n=>by change flash (uband (U:=Woods G n) 1)=1;rw [uband_flash,map_one]⟩

def ordinary (left right:Sheet G):Sheet G:=
  ⟨left.grade+right.grade,agateV left.field right.field,fun n=>left.print n*right.print n,
   left.funded.manor right.funded,fun n=>by
    change flash (woad (left.field.1 n) (right.field.1 n))=_
    rw [woadap _ _ (finite_shell (left.funded.span n)) (finite_shell (right.funded.span n)),left.actual,right.actual]⟩

inductive Slot where | vacant | full | fitted | stable

variable {H:Hol G}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
variable {h D k e u d:ℕ}{E A K U:Credit}{v:Rails h k u e}
variable {s:Bool}{p:h<D}{w:d<D}(M:Master H)
variable (X:CutsP H (M.T h) p v E A K U)(L:Torch H (M.T h) p v E A K)(run:XSpace.Run)
  (base idx f:ℕ)(amp δ η fee:ℝ)(c:Verse (R.family.labels.level d))

private theorem supported (booked:Filed X L run base idx f amp δ η fee (Shrine (plate (sectionAt R W s d) w) c))
    (a:ℝ)(φ:Rarity D)(y:ℝ)(o:CellR) :
    Auth d (word ((a/amp) • X.pt) φ (paceT X.ax.S X.m (X.m+X.i)) y o h) ∧
    Auth h (receiving X (a/amp) φ y o X.i):=by
  constructor
  · obtain ⟨_,_,hi⟩:=WilsonIndependentMatchedFiledIncome.named R W s d w le_rfl 0 0
    rw [booked.actual a,←shrine_μ]
    exact locale_val _ (Mer.placed h φ ((hi (a • c)).1) _ y) o
  · obtain ⟨_,_,hi⟩:=WilsonIndependentMatchedFiledIncome.original (M.T h) p H (M.spec h) (M.pop h) le_rfl 0 0
    have top:X.N=X.ceilC:=by
      change X.N=X.m+X.i
      rw [booked.top,booked.report,booked.gap,WilsonIndependentEvenPassport.count,Nat.add_assoc]
    have src:X.Ntop=plate (M.T h) p:=WilsonIndependentMatchedTopStencils.initial X top
    rw [WilsonIndependentMatchedFittedSeat.inlet,src,←shrine_μ]
    exact locale_val _ (Mer.placed h φ ((hi ((a/amp) • X.tileP)).1) _ y) o

def mounted (booked:Filed X L run base idx f amp δ η fee (Shrine (plate (sectionAt R W s d) w) c))
    (a:ℝ)(φ:Rarity D)(y:ℝ)(o:CellR)(which:Slot):Sheet G:=by
  let x:=paceT X.ax.S X.m (X.m+X.i)
  let P (n:Side):=WilsonIndependentMatchedOrdinaryProfile.stems R W n s w (a • c) φ x y o h
  let V (n:Side):=WilsonIndependentMatchedElectedSection.profile (M.T h) p n ((a/amp) • X.tileP) φ x y o h
  have eqs:=WilsonIndependentMatchedElectedColumn.actual R W M X L run base idx f amp δ η fee c booked a φ y o
  have supports:=supported R W M X L run base idx f amp δ η fee c booked a φ y o
  cases which with
  | vacant=>exact empty
  | full=>exact ⟨d,word ((a/amp) • X.pt) φ x y o h,P,supports.1,fun n=>(eqs n).1⟩
  | fitted=>exact ⟨h,receiving X (a/amp) φ y o X.i,V,supports.2,fun n=>(eqs n).2.1⟩
  | stable=>
    exact ⟨k,seat X (a/amp) φ y o X.i,fun n=>P n-V n,(WilsonIndependentMatchedCoveredSeats.traced X _ φ y o).1 _ le_rfl,
      fun n=>(eqs n).2.2⟩

/-- The complete finite torus response and its cover come from the same print.
Select the common enrolled degree before the heat call. -/
theorem original (left right:Sheet G)(A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    {m N q top:ℕ}(degree:left.grade+right.grade≤q+1)(lower:m≤top)(finer:top≤N):
    (∀n,WilsonIndependentMatchedOrdinaryHistory.scalar A Ñ N q top m (fun l=>left.print l*right.print l) n=
      flash ((cruises A Ñ N (q+1) top m (agateV left.field right.field)).1 n)) ∧
    ∀j r,Bends 0 (fun c=> WilsonIndependentConditionalMarkedCover.tensor
      (WilsonIndependentMatchedOrdinaryHistory.scalar A Ñ N q top m (fun l=>left.print l*right.print l) c) j r)
      ((cruises A Ñ N (q+1) top m (agateV left.field right.field)).2 j r):=by
  let S:=ordinary left right
  have valid:Auth (q+1) S.field:=S.funded.tall degree
  exact ⟨WilsonIndependentMatchedOrdinaryHistory.cleared A simple ratio lower finer S.field valid S.print S.actual,
    WilsonIndependentMatchedOrdinaryHistory.covered A simple ratio lower finer S.field valid S.print S.actual⟩

end YM.Integration.WilsonIndependentMatchedElectedFaces
