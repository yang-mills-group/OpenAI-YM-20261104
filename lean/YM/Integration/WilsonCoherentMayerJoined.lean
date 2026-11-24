import YM.Integration.WilsonCoherentMayerSubmission

/-! A previously registered single regular field and a later finite portfolio form
one signed submission on their existing addresses, with the same old roster. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonCoherentMayerJoined

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

open WilsonCoherentMayerSubmission
open Function Finset Lattice Wilson RG PhysicalNext.Repeat Legato Lotus
variable {G:Gauge} {run:Run G} {f:Side} {A:Rep G f} {I:Type} [Fintype I]
    (one:Submitted run A Unit) (many:Submitted run A I) (room:∀i,one.key ()≠many.key i)

def join : Submitted run A (Option I) where
  grade | none=>one.grade () | some i=>many.grade i
  site | none=>one.site () | some i=>many.site i
  label | none=>one.label () | some i=>many.label i
  phase | none=>one.phase () | some i=>many.phase i
  key | none=>one.key () | some i=>many.key i
  separated :=by
    intro i j same
    cases i with
    | none =>
      cases j with
      | none=>rfl
      | some j=>exact (room j same).elim
    | some i =>
      cases j with
      | none=>exact (room i same.symm).elim
      | some j=>exact congrArg some (many.separated same)
  covers | none=>one.covers () | some i=>many.covers i
  vacant | none=>one.vacant () | some i=>many.vacant i

omit [Fintype I] in
theorem at_old : row (join one many room) none=row one ():=rfl
omit [Fintype I] in
theorem at_fresh (i:I) : row (join one many room) (some i)=row many i:=rfl

theorem labels : occupied (join one many room)=occupied one∪occupied many:=by
  ext m
  simp only [occupied,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,e⟩
    cases i with
    | none=>exact Or.inl ⟨(),e⟩
    | some i=>exact Or.inr ⟨i,e⟩
  · rintro (⟨⟨⟩,e⟩|⟨i,e⟩)
    · exact ⟨none,e⟩
    · exact ⟨some i,e⟩

variable (prior:Team A) (a:∀m∈prior.own,∀i,m.turn≠(row one i).turn)
    (b:∀m∈(together one prior a).own,∀i,m.turn≠(row many i).turn)

include a b in
omit [Fintype I] in
theorem licensed (i:I):one.key ()≠many.key i:=by
  intro eq
  have live:row one ()∈(together one prior a).own:=Finset.mem_union_right _
    (Finset.mem_image_of_mem _ (Finset.mem_univ ()))
  exact b _ live i (congrArg Wing.logKey eq)

omit [Fintype I] in
theorem available (m:Leaf A) (present:m∈prior.own) (i:Option I):
    m.turn≠(row (join one many (licensed one many prior a b)) i).turn:=by
  cases i with
  | none=>exact a m present ()
  | some i=>exact b m (Finset.mem_union_left _ present) i

private theorem team_eq {u v:Team A} (e:u.own=v.own):u=v:=by
  cases u
  cases v
  congr

theorem source :
    together (join one many (licensed one many prior a b)) prior (available one many prior a b)=
    together many (together one prior a) b:=by
  apply team_eq
  change prior.own∪occupied (join one many _)=(prior.own∪occupied one)∪occupied many
  rw [labels,Finset.union_assoc]

end YM.Integration.WilsonCoherentMayerJoined
