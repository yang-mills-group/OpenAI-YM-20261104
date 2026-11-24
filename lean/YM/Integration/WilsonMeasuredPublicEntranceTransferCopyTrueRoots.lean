import YM.Integration.WilsonOriginalPublicTrialPhaseCopiedCourse
import YM.Integration.WilsonOriginalPublicTrialPhaseCampusRoom
import YM.Integration.WilsonSeparatedPrefixScreenedParents
import YM.Integration.WilsonSeparatedPrefixCellParents
import YM.Integration.WilsonForcedReplicaDistance
/-! The actual entered f-sites and all their reflected Wilson copies at capture. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferCopyTrueRoots
open Function Finset Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Ribbons MergeProof.Ribbons.ManyCopies RG16 RG16.Literal
open OPE Extra.Histories Motion Extraction Push.GridApprox
open WilsonOriginalNullOriginGridRoster (ancestry)
open WilsonOriginalPublicTrialPhaseCopiedCourse (root)
open WilsonAddressedPhysicalCells
open private singleton from YM.Integration.WilsonForcedReplicaDistance
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type}{j c f K N p:ℕ}
local notation "C" => R.family
local notation "S" => (C).S

theorem drop (jf:j≤f)(fk:f≤K)(z:Site ((C).side f p)):
    ancestry R p K (((S).toDepth fk p).embed z) j=ancestry R p f z j:=by
  rw [ancestry,dif_pos (jf.trans fk),ancestry,dif_pos jf]
  rw [Next.Rank.Station.parent_nested ((S).toDepth jf p) ((S).toDepth fk p) ((S).toDepth (jf.trans fk) p)
    ((S).toDepth_odd jf p) ((S).toDepth_odd fk p),Ratio.embed_parent]

theorem older (jf:j≤f)(fk:f≤K)(z:Site ((C).side K p))(zero:ancestry R p K z f=0):
    ancestry R p K z j=0:=by
  rw [ancestry,dif_pos fk] at zero
  rw [ancestry,dif_pos (jf.trans fk),Next.Rank.Station.parent_nested ((S).toDepth jf p) ((S).toDepth fk p)
    ((S).toDepth (jf.trans fk) p) ((S).toDepth_odd jf p) ((S).toDepth_odd fk p),zero]
  let Q:=(S).toDepth jf p
  change Q.parent 0=0
  rw [←Q.root.map_zero]
  exact Q.embed_parent _

def funded (fk:f≤K)(o:I→Site ((C).side f p))(c:ℕ)(j:ℕ)(N:ℕ):Prop:=
  let pins:=fun i=>((S).toDepth fk p).embed (o i)
  let atAge:=fun m i=>ancestry R p K (pins i) m
  (∀m,m≤c+1→∀i,atAge m i=0) ∧
    ∀t:Site ((C).side j p),∀a b:I,
      coverNumber ((C).path.rep N p (c+1)).p.B ({root R (j:=j) (atAge (c+1)) (t,a),root R (j:=j) (atAge (c+1)) (t,b)}:Support _)≤1

theorem at_date (jf:c+1≤f)(fk:f≤K)(o:I→Site ((C).side f p))
    (housed:∀i,ancestry R p f (o i) (c+1)=0):
    funded R fk o c j N:=by
  let pins (i:I):=((S).toDepth fk p).embed (o i)
  let current (m:ℕ)(i:I):=ancestry R p K (pins i) m
  have gate i:current (c+1) i=0:=(drop R jf fk (o i)).trans (housed i)
  refine ⟨fun m mc i=>older R mc (jf.trans fk) (pins i) (gate i),?_⟩
  intro t a b
  have eq:root R (j:=j) (current (c+1)) (t,a)=root R (j:=j) (current (c+1)) (t,b):=by
    simp only [root,gate]
  rw [eq,Finset.insert_eq_of_mem (Finset.mem_singleton_self _)]
  exact singleton _ _

theorem screened (base:c+2≤f)(fk:f≤K)(o:I → Cover)(L:ℝ)
    (reach:∀i,‖(S).gridPoint f (o i)‖≤L)(clear:8*L≤(S).a (c+1)):
    funded R fk (snap (C) f p o) c j N:=
  at_date R (by omega) fk _ (WilsonSeparatedPrefixScreenedParents.original R base o L reach clear)

theorem active {n:ℕ}(φ:Test n)(base:c+2≤f)(fk:f≤K)(r L:ℝ)
    (bound:∀x:Points n,φ x≠0→∀i,‖r • x i‖≤L)
    (clear:8*(L+4*(n:ℝ)*(S).a f)≤(S).a (c+1))(o:Sites ((C).side f p) n)
    (cell:mass φ ((S).a f) r ((C).side f p) o≠0):
    funded R fk o c j N:=
  at_date R (by omega) fk o (WilsonSeparatedPrefixCellParents.original R φ base r L bound clear o cell)
end YM.Integration.WilsonMeasuredPublicEntranceTransferCopyTrueRoots
end
