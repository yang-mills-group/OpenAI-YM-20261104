import YM.Integration.ManuscriptQLocalOrdinaryLeaf
import YM.Integration.WilsonCoherentMayerOccurrences

/-! Enter a previously filed regular observable on its original support and price.
The entire formerly occupied team remains on the same sample. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonCoherentMayerOldSlots

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus Progress.DirectedRecipe
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G:Gauge} {f:Side} (A:Rep G f) (a:RegularAddress f)

/-- The tag is chosen before the filed field, its coefficient, and the sample. -/
theorem room (old:Team (QLocalInheritedRegularSlots.carrier A)) :
    ∃tag:ℕ,∀m∈old.own,m.turn≠Wing.logKey (blankRow f (a,tag)):=by
  let k:=fun tag:ℕ=>Wing.logKey (blankRow f (a,tag))
  have inj:Injective k:=by
    intro t t' h
    exact congrArg Prod.snd ((blankRow f).injective (Wing.logKey.inj h))
  have finite:(k ⁻¹' Set.range (fun j:old.own=>(j.1).turn)).Finite:=
    (Set.finite_range _).preimage inj.injOn
  obtain ⟨tag,_,ht⟩:=(Set.infinite_univ:Set.Infinite (Set.univ:Set ℕ)).exists_notMem_finset finite.toFinset
  exact ⟨tag,fun m hm eq=>ht (finite.mem_toFinset.mpr ⟨⟨m,hm⟩,eq⟩)⟩

def increase {R:Rep G f} (old:Team R) (m:Leaf R) (fresh:∀b∈old.own,b.turn≠m.turn):Team R where
  own:=insert m old.own
  alone:=by
    intro v hv w hw same
    rcases Finset.mem_insert.mp hv with ev|iv
    · rcases Finset.mem_insert.mp hw with ew|iw
      · exact ev.trans ew.symm
      · exact (fresh w iw (same.symm.trans (congrArg Leaf.turn ev))).elim
    · rcases Finset.mem_insert.mp hw with ew|iw
      · exact (fresh v iv (same.trans (congrArg Leaf.turn ew))).elim
      · exact old.alone iv iw same

variable (old:Team (QLocalInheritedRegularSlots.carrier A))
def booked (tag:ℕ) (free:∀m∈old.own,m.turn≠Wing.logKey (blankRow f (a,tag)))
    (ψ:Config G f→ℝ) {u:ℝ} (regular:A.p.Regular a.support ψ) (paid:A.p.supBounds a.site a.support ψ u) : Team (QLocalInheritedRegularSlots.carrier A) :=
  increase old (ManuscriptQLocalOrdinaryLeaf.leaf A a ψ regular paid tag) free

theorem entered (tag:ℕ) (free:∀m∈old.own,m.turn≠Wing.logKey (blankRow f (a,tag)))
    (ψ:Config G f→ℝ) {u:ℝ} (regular:A.p.Regular a.support ψ) (paid:A.p.supBounds a.site a.support ψ u) :
    let m:=ManuscriptQLocalOrdinaryLeaf.leaf A a ψ regular paid tag
    let W:=booked A a old tag free ψ regular paid
    m∈W.own ∧ old.own⊆W.own ∧ W.weight=old.weight*u ∧
       m.crest=a.support ∧ ∀U,m.ingredient U=masked A.p.threshold a.support ψ U:=by
  let m:=ManuscriptQLocalOrdinaryLeaf.leaf A a ψ regular paid tag
  have unused:m∉old.own:=fun h=>free m h rfl
  have idx:(QLocalInheritedRegularSlots.carrier A).activities.reg (blankRow f (a,tag))=a:=
    (QLocalInheritedRegularSlots.reserved A a tag).1
  refine ⟨Finset.mem_insert_self .., Finset.subset_insert ..,?_,?_,fun _=>rfl⟩
  · change (∏b∈insert m old.own,b.weight)=_ 
    rw [Finset.prod_insert unused,mul_comm]
    rfl
  · change ((QLocalInheritedRegularSlots.carrier A).activities.reg (blankRow f (a,tag))).support=a.support
    rw [idx]

variable {c L:Side} {S:StepData c f} {T:Tube G S} {P:Teller G} {Q:ConnectedActivityE6.Target G P}
  {w s μ C:ℝ} {o:Target.Order G w} (H:Cash w s μ L Q o C T (QLocalInheritedRegularSlots.carrier A))

theorem observed (tag:ℕ) (free:∀m∈old.own,m.turn≠Wing.logKey (blankRow f (a,tag)))
    (ψ:Config G f→ℝ) {u:ℝ} (regular:A.p.Regular a.support ψ) (paid:A.p.supBounds a.site a.support ψ u)
    {F:Forest S.ratio} (X:Coat T F) (z:momentSpace X) :
    let m:=ManuscriptQLocalOrdinaryLeaf.leaf A a ψ regular paid tag
    let W:=booked A a old tag free ψ regular paid
    (Laminate.partner W H (m.turn.badge S)).joint X z=
      masked A.p.threshold a.support ψ (WilsonCoherentMayerOccurrences.field (QLocalInheritedRegularSlots.carrier A) X z)*
        WilsonCoherentMayerOccurrences.anchor (QLocalInheritedRegularSlots.carrier A) o.a m.turn X z:=by
  exact WilsonCoherentMayerOccurrences.leaf (H:=H) _ _ (Finset.mem_insert_self ..) X z

end YM.Integration.WilsonCoherentMayerOldSlots
