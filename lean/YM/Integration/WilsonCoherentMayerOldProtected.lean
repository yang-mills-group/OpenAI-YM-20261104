import YM.Integration.WilsonCoherentMayerOldPortfolio
import YM.Integration.WilsonCoherentMayerActivity

/-! The actual old glyph and every new field appear once in the same protected Mayer row. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonCoherentMayerOldProtected




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


open WilsonCoherentMayerOldPortfolio (coalition admitted)
def formed:Team A:=together (coalition run F₀ L₀ v r z A prior shelf root χ newer free) prior
     (admitted run F₀ L₀ v r z A prior shelf root χ newer free)
def gates:Team A:=WilsonCoherentMayerGate.team (formed run F₀ L₀ v r z A prior shelf root χ newer free)
    (occupied (coalition run F₀ L₀ v r z A prior shelf root χ newer free))

variable {upper:ℕ} (age:run.family.ref v.size≤L₀.level r) (future:L₀.level r≤upper)
    {c l:Side} {S:StepData c (run.family.side (L₀.level r) per)} {T:Tube G S} {P:Teller G}
    {Q:ConnectedActivityE6.Target G P} {w s μ C:ℝ} {o:Target.Order G w} (H:Cash w s μ l Q o C T A)
    {p:Molecule S}{M:ℕ}
    (before:(formed run F₀ L₀ v r z A prior shelf root χ newer free).signs S⊆p)
    (u:Mayer.Decors (p\(formed run F₀ L₀ v r z A prior shelf root χ newer free).signs S) M)

include age future before in
theorem joint (positive:0<A.p.threshold) {forest:Forest S.ratio} (X:Coat T forest) (a:momentSpace X):
    let U:=WilsonCoherentMayerOccurrences.field A X a
    Mayer.planned H p u (Laminate.partner (formed run F₀ L₀ v r z A prior shelf root χ newer free) H) X a=
      (χ ((((run.family.path.levels.clock.hatCoupling (L₀.level r))^v.grade:ℝ):ℂ)*
        WilsonReportingPrescribedOldGlyph.observed run F₀ L₀ v r z upper per root U)*
        (∏m∈occupied newer,read newer m U))*
      Mayer.planned H p u (Laminate.partner (gates run F₀ L₀ v r z A prior shelf root χ newer free) H) X a:=by
  let J:=coalition run F₀ L₀ v r z A prior shelf root χ newer free
  let reserve:=admitted run F₀ L₀ v r z A prior shelf root χ newer free
  let rest:=gates run F₀ L₀ v r z A prior shelf root χ newer free
  let U:=WilsonCoherentMayerOccurrences.field A X a
  have cut:=WilsonCoherentMayerOccurrences.original (H:=H) (together J prior reserve) (occupied J)
    (registered J prior reserve).1 (regular J) (read J) (qualifies J) before u X a
  have drawn:=(WilsonCoherentMayerOldPortfolio.signed run F₀ L₀ v r z A prior shelf root χ
    newer free age future positive U)
  exact cut.trans (congrArg (fun b:ℝ=>b*Mayer.planned H p u (Laminate.partner rest H) X a) drawn)

end YM.Integration.WilsonCoherentMayerOldProtected
