import YM.Integration.WilsonCoherentMayerOldGlyph

/-! A funded old glyph can join every existing marked roster on its own fresh address.
Every further mark is tested on the same sample as that admitted old member. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonCoherentMayerOldReentry


open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

open Source Labels Extraction Table Spec RG17 PhysicalNext.Repeat.Legato MS MS.Menus MS.Local.Physical
open WilsonReportingPrescribedOldGrade

open WilsonCoherentMayerSubmission
variable {G:Gauge} (run:Run G) {order:Extraction.Order} {S₀:Table run.family.book}
    (F₀:Spec.Final run.family order S₀) (L₀:Layout F₀) {B:Deck G}{h:ℕ} (v:Glyph B h)
    (r:ℝ) (z:ℂ) {per:ℕ} (A:Rep G (run.family.side (L₀.level r) per))
    (prior:Team A) (shelf:WilsonCoherentMayerSlots.Shelf A)
    (root:Site (run.family.side (L₀.level r) per)) (χ:ℂ→L[ℝ]ℝ)

def receipt : Submitted run A Unit :=
  WilsonCoherentMayerSlots.issued run (fun _:Unit=>v.size) (fun _=>root) prior shelf
    (fun _=>WilsonCoherentMayerOldGlyph.entered run F₀ L₀ v r z A.p.threshold) (fun _=>χ)

def crew : Team A := together (receipt run F₀ L₀ v r z A prior shelf root χ) prior
    (WilsonCoherentMayerSlots.fresh run _ _ prior shelf _ _)

def member : Leaf A := row (receipt run F₀ L₀ v r z A prior shelf root χ) ()

theorem funds (positive:0<A.p.threshold):
    let b:=member run F₀ L₀ v r z A prior shelf root χ
    let W:=crew run F₀ L₀ v r z A prior shelf root χ
    prior.own⊆W.own ∧ b∈W.own ∧
      b.weight=‖χ‖*∑i,‖WilsonCoherentMayerOldGlyph.column run F₀ L₀ v r z i‖*
        WilsonCoherentMayerEntry.unitPrice run v.size i ∧
      b.crest=(run.family.localSection v.size).footprint root:=by
  refine ⟨Finset.subset_union_left,Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ ())),?_,?_⟩
  · exact WilsonCoherentMayerOldGlyph.costs run F₀ L₀ v r z χ positive
  · change (A.activities.reg (WilsonCoherentMayerSlots.key run (fun _:Unit=>v.size) (fun _=>root) prior ())).support=_
    unfold WilsonCoherentMayerSlots.key
    rw [(shelf _ _).1]
    rfl

variable {N:ℕ} (age:run.family.ref v.size≤L₀.level r) (future:L₀.level r≤N)
    {c l:Side} {S:StepData c (run.family.side (L₀.level r) per)} {T:Tube G S} {P:Teller G}
    {Q:ConnectedActivityE6.Target G P} {w s μ C:ℝ} {o:Target.Order G w} (H:Cash w s μ l Q o C T A)

include age future in
theorem original (positive:0<A.p.threshold) {I:Type} [Fintype I]
    (fresh:Submitted run A I) (separate:∀b∈(crew run F₀ L₀ v r z A prior shelf root χ).own,∀i,
      b.turn≠(row fresh i).turn) {forest:Forest S.ratio} (X:Coat T forest) (u:momentSpace X) :
    let m:=member run F₀ L₀ v r z A prior shelf root χ
    let W:=together fresh (crew run F₀ L₀ v r z A prior shelf root χ) separate
    let U:=WilsonCoherentMayerOccurrences.field A X u
    (Laminate.partner W H (m.turn.badge S)).joint X u=
      masked A.p.threshold ((run.family.localSection v.size).footprint root)
       (fun V=>χ (((run.family.path.levels.clock.hatCoupling (L₀.level r)^v.grade:ℝ):ℂ)*
         WilsonReportingPrescribedOldGlyph.observed run F₀ L₀ v r z N per root V)) U*
         WilsonCoherentMayerOccurrences.anchor A o.a m.turn X u:=by
  let q:=receipt run F₀ L₀ v r z A prior shelf root χ
  let m:=member run F₀ L₀ v r z A prior shelf root χ
  let later:=together fresh (crew run F₀ L₀ v r z A prior shelf root χ) separate
  have funding:=funds run F₀ L₀ v r z A prior shelf root χ positive
  have inside:m∈later.own:=Finset.mem_union_left _ funding.2.1
  have recorded:=WilsonCoherentMayerOldGlyph.observed run F₀ L₀ v r z age future root χ A H
    (q.key ()) (q.covers ()) (q.vacant ()) later inside positive X u
  have sites:(A.activities.reg (q.key ())).support=(run.family.localSection v.size).footprint root:=
    funding.2.2.2
  rw [sites] at recorded
  exact recorded

end YM.Integration.WilsonCoherentMayerOldReentry
