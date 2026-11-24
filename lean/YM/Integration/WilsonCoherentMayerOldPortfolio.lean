import YM.Integration.WilsonCoherentMayerOldReentry
import YM.Integration.WilsonCoherentMayerJoined

/-! On the original one-field hearing, take the issued nonbare mark and all later marked inputs
as one submitted roster. Their joint coefficient has the original addresses and the old tariff. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonCoherentMayerOldPortfolio



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


open WilsonCoherentMayerOldReentry (receipt member crew)
variable {I:Type} [Fintype I] (newer:Submitted run A I)
    (free:∀b∈(crew run F₀ L₀ v r z A prior shelf root χ).own,∀i,b.turn≠(row newer i).turn)

def coalition:Submitted run A (Option I):=
  let head:=receipt run F₀ L₀ v r z A prior shelf root χ
  let res:=WilsonCoherentMayerSlots.fresh run (fun _:Unit=>v.size) (fun _=>root) prior shelf
    (fun _=>WilsonCoherentMayerOldGlyph.entered run F₀ L₀ v r z A.p.threshold) (fun _=>χ)
  WilsonCoherentMayerJoined.join head newer (WilsonCoherentMayerJoined.licensed head newer prior res free)

omit [Fintype I] in
theorem admitted (b:Leaf A) (live:b∈prior.own) (i:Option I):b.turn≠
    (row (coalition run F₀ L₀ v r z A prior shelf root χ newer free) i).turn:=
  WilsonCoherentMayerJoined.available _ _ prior
    (WilsonCoherentMayerSlots.fresh run (fun _:Unit=>v.size) (fun _=>root) prior shelf
       (fun _=>WilsonCoherentMayerOldGlyph.entered run F₀ L₀ v r z A.p.threshold) (fun _=>χ))
    free b live i

theorem roster:together (coalition run F₀ L₀ v r z A prior shelf root χ newer free) prior
     (admitted run F₀ L₀ v r z A prior shelf root χ newer free)=
   together newer (crew run F₀ L₀ v r z A prior shelf root χ) free:=
  WilsonCoherentMayerJoined.source _ _ prior
    (WilsonCoherentMayerSlots.fresh run (fun _:Unit=>v.size) (fun _=>root) prior shelf
       (fun _=>WilsonCoherentMayerOldGlyph.entered run F₀ L₀ v r z A.p.threshold) (fun _=>χ)) free

variable {N:ℕ} (age:run.family.ref v.size≤L₀.level r) (future:L₀.level r≤N)

include age future in
theorem signed (positive:0<A.p.threshold) (U:Config G (run.family.side (L₀.level r) per)):
    let J:=coalition run F₀ L₀ v r z A prior shelf root χ newer free
    (∏m∈occupied J,read J m U)=
      χ ((((run.family.path.levels.clock.hatCoupling (L₀.level r))^v.grade:ℝ):ℂ)*
        WilsonReportingPrescribedOldGlyph.observed run F₀ L₀ v r z N per root U)*
      (∏m∈occupied newer,read newer m U):=by
  dsimp only
  rw [full, Fintype.prod_option, full]
  exact congrArg (fun a:ℝ=>a*∏i,newer.phase i (Push.Local.presented (run.family.localSection (newer.grade i))
    (newer.site i) A.p.threshold (newer.label i) U)) (WilsonCoherentMayerOldGlyph.deposited
    run F₀ L₀ v r z age future root χ positive U)

theorem salary (positive:0<A.p.threshold):
    let J:=coalition run F₀ L₀ v r z A prior shelf root χ newer free
    (∏m∈occupied J,m.weight)=(‖χ‖*∑i,‖WilsonCoherentMayerOldGlyph.column run F₀ L₀ v r z i‖*
        WilsonCoherentMayerEntry.unitPrice run v.size i)*(∏m∈occupied newer,m.weight):=by
  dsimp only
  rw [WilsonCoherentMayerSubmission.prices,Fintype.prod_option,WilsonCoherentMayerSubmission.prices]
  exact congrArg (fun a:ℝ=>a*∏i,WilsonCoherentMayerEntry.wallet run (newer.label i) A.p.threshold (newer.phase i))
    (WilsonCoherentMayerOldGlyph.costs run F₀ L₀ v r z χ positive)

theorem mass (positive:0<A.p.threshold):
    let J:=coalition run F₀ L₀ v r z A prior shelf root χ newer free
    WilsonCoherentReportingPivot.mass run J.grade A.p.threshold J.label=
      (∑i,‖WilsonCoherentMayerOldGlyph.column run F₀ L₀ v r z i‖)*
      WilsonCoherentReportingPivot.mass run newer.grade A.p.threshold newer.label:=by
  dsimp only
  rw [WilsonCoherentReportingPivot.counted,Fintype.prod_option,WilsonCoherentReportingPivot.counted]
  change (∑i,‖(run.family.labels.level v.size).scaled A.p.threshold⁻¹
       (WilsonCoherentMayerOldGlyph.entered run F₀ L₀ v r z A.p.threshold) i‖)*_=_
  rw [WilsonCoherentMayerOldGlyph.unscaled run F₀ L₀ v r z positive]
  rfl

end YM.Integration.WilsonCoherentMayerOldPortfolio
