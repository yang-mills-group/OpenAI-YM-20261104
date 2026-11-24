import YM.Integration.WilsonCoherentMayerOldProtected
import YM.Integration.WilsonRootedMayerColumn

/-! One nonbare glyph, the whole fresh roster and the retained old signed course on the
single native restricted covariance of the original participating supports. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonCoherentMayerOldMarginal





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

open PhysicalNext.Repeat.Daisy RGLocalTaylor.Mayer
open WilsonCoherentMayerOldProtected (formed gates)

variable {N:ℕ} (age:run.family.ref v.size≤L₀.level r) (future:L₀.level r≤N)

def observed (U:Config G (run.family.side (L₀.level r) per)):ℝ:=
  χ ((((run.family.path.levels.clock.hatCoupling (L₀.level r))^v.grade:ℝ):ℂ)*
      WilsonReportingPrescribedOldGlyph.observed run F₀ L₀ v r z N per root U)*
   (∏m∈occupied newer,read newer m U)

variable {c l:Side} {S:StepData c (run.family.side (L₀.level r) per)} {T:Tube G S} {P:Teller G}
    {Q:ConnectedActivityE6.Target G P} {w s μ C:ℝ} {o:Target.Order G w} (H:Cash w s μ l Q o C T A)
    {j n k k':ℕ} {a d' ℓ Y b σ r' B q K θ bill e uJ vJ:ℝ} {phase:Chi}

include age future in
theorem original (positive:0<A.p.threshold) (loc:H.ThinP)
    (captain:Captain H j a d' ℓ Y b σ r' B q n phase)
    (law:Awning H captain.conduit b σ bill e uJ vJ k k') (room:Q.goal l s≤K)
    (M:ℕ) (grade:Orders M) (approved:Approved K θ j M) (allowed:authorized H loc.val)
    (live:grade.val≤M) (cohort:Start loc.val)
    (before:(formed run F₀ L₀ v r z A prior shelf root χ newer free).signs S⊆loc.val)
    (V:Config G c) (inside:Healthy (Pressure.temp s) (H.smallAt loc) V):
    let W:=formed run F₀ L₀ v r z A prior shelf root χ newer free
    let rest:=loc.val\W.signs S
    Laminate.column W loc.val H (χ:=phase) M grade V=
      ∑u∈univ.filter (fun u:Decors rest M=>decorOrder u=grade.val),
        likely fun f:Greenbelt.Reserve S=>likely fun tag:S.Choices=>
          let X:=((planted (prism T s phase o.K V (Greenbelt.allot f)) loc.val).taggedL tag)
          let E:=WilsonRootedMayerHull.coordinates H loc.val X
          ∫y:(Greenbelt.allot f).Slice G, ∫a:Body (↥E),
            let ζ:momentSpace X:=(y,Pond.spill E a)
            observed run F₀ L₀ v r z A root χ newer (N:=N) (WilsonCoherentMayerOccurrences.field A X ζ)*
            Mayer.planned H loc.val u (Laminate.partner
               (gates run F₀ L₀ v r z A prior shelf root χ newer free) H) X ζ
            ∂Pond.arch E X.relating ∂(Greenbelt.allot f).order G:=by
  let W:=formed run F₀ L₀ v r z A prior shelf root χ newer free
  have actual:=WilsonRootedMayerColumn.original H W loc captain law room M grade approved
    allowed live cohort before V inside
  refine actual.trans (Finset.sum_congr rfl fun u _=>congr_arg (@likely (Greenbelt.Reserve S) _) (funext fun f=>
    congr_arg (@likely S.Choices _) (funext fun tag=>?_)))
  let X:=((planted (prism T s phase o.K V (Greenbelt.allot f)) loc.val).taggedL tag)
  let E:=WilsonRootedMayerHull.coordinates H loc.val X
  apply integral_congr_ae
  filter_upwards with y
  apply integral_congr_ae
  filter_upwards with a
  exact WilsonCoherentMayerOldProtected.joint run F₀ L₀ v r z A prior shelf root χ newer free
    age future H before u positive X (y,Pond.spill E a)

end YM.Integration.WilsonCoherentMayerOldMarginal
