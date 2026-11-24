import YM.Integration.WilsonMeasuredPublicEntranceSmoothPublic
import YM.Integration.WilsonMeasuredPublicEntranceProperPhase
import YM.Integration.WilsonMeasuredPublicEntrancePublicFour
import YM.Integration.WilsonMeasuredPublicEntranceSmoothWeights

/-! Take the selected physical limit of the same reflected Wilson measurements and of their cutoff-dependent projected fields. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1400000
namespace YM.Integration.WilsonMeasuredPublicEntrancePhysicalPair
open Function Filter Finset Lattice Wilson RG Source Labels Cells OPE Extraction Spec
open Table Table.Pairing Extraction.Banks RG17 PhysicalNext.Repeat.Legato Climb GapsContact Next.Rank
open XSpace XSpace.Normalize XSpace.Rose MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalBlissMixedGram (columns grades)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonAddressedPublicSelfPurchase (source)
open WilsonMeasuredPublicEntranceOrderedPins (physical publicValue)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {D T:ℕ}{r:Fin 2→ℝ}(B:∀i,Book F (l:=l) H z D T (r i))
    (d:Fin 2→Fin (D+1))(v:∀i,Bool→S.Field (d i).val)
local notation "C" => R.family
local notation "caps" => grades (d 0).val (d 1).val


open WilsonMeasuredPublicEntrancePublicFour (sign)
open WilsonMeasuredPublicEntranceCoverCells (mass)
open WilsonMeasuredPublicEntranceSmoothWeights
open WilsonAddressedPublicNamedQuadrature (value)

open MergeProof Ribbons Accent ManyCopies RG16 RG16.Literal Extra.Histories
open WilsonMeasuredPublicEntranceCellWords
open WilsonReflectedPublicOrientedFaces (displayed)

def fields (b:Fin 2→Bool)(w:ℕ×ℕ):(C).book.Vector caps:=
  Fin.cons (α:=fun i=>(C).label (caps i)) ((((B 0).rows (d 0)).arm (b 0) (v 0 (b 0))).source w)
    (fun _=>(((B 1).rows (d 1)).arm (b 1) (v 1 (b 1))).source w)
def reflected (ax:Axis):Fin 2→Motion:=![(Signed.mirror ax,true),(1,false)]

theorem labels (b:Fin 2→Bool)(ax:Axis)(w:ℕ×ℕ):
    (fun i=>displayed R (caps i) (fields R F B d v b w i) (reflected ax i))=
      source R F B d (fun i=>v i (b i)) b ax w:=by
  funext i
  fin_cases i
  · rfl
  · simp [displayed,reflected,fields,source,columns,grades,show (1:Signed).ortho=1 from map_one Signed.inclusionO]
    exact ((C).labels.level (d 1).val).act_one _

theorem group {site N per:ℕ}(live:site≤N)(o:Fin 2→ Cover)(s:(Stock.census (Fin 2)).Mode)
    (all:s.val=Finset.univ)(b:Fin 2→Bool)(ax:Axis):
    WilsonMeasuredPublicEntranceCellWords.physical R caps (N:=N) (fields R F B d v b (N,per))
      (reflected ax) (fun i=>wrap ((C).side site per) (o i)) s=
    word R caps site N per live o (source R F B d (fun i=>v i (b i)) b ax (N,per)):=by
  funext U
  unfold WilsonMeasuredPublicEntranceCellWords.physical word
  simp_rw [WilsonAddressedPublicGridRooms.top R live]
  rw [all]
  apply Finset.prod_congr rfl
  intro i _
  rw [show displayed R (caps i) (fields R F B d v b (N,per) i) (reflected ax i)=_ from congrFun (labels R F B d v b ax (N,per)) i]
  rfl

theorem original {site N per:ℕ}(live:site≤N)(o:Fin 2→ Cover)(s:(Stock.census (Fin 2)).Mode)
    (all:s.val=Finset.univ)(ax:Axis):
    (∑b,sign b*(C).omega N per (WilsonMeasuredPublicEntranceCellWords.physical R caps (N:=N)
      (fields R F B d v b (N,per)) (reflected ax) (fun i=>wrap ((C).side site per) (o i)) s))=
      WilsonMeasuredPublicEntranceSmoothPublic.observed R F B d v ax site (N,per) o:=by
  unfold WilsonMeasuredPublicEntranceSmoothPublic.observed
  apply Finset.sum_congr rfl
  intro b _
  rw [group R F B d v live o s all b ax,WilsonAddressedPublicOrderedQuadrature.at_grid R d live]

end YM.Integration.WilsonMeasuredPublicEntrancePhysicalPair
end
