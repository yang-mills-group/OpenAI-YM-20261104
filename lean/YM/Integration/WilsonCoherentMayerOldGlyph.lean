import YM.Integration.WilsonReportingPrescribedOldGlyph
import YM.Integration.WilsonCoherentMayerSlots
import YM.Integration.WilsonCoherentMayerOccurrences

/-! A re-entered registered glyph beside its intact previous marked team.
The written finite column retains all of the strictly lower contractions. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerOldGlyph

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
variable {G:Gauge} (run:Run G) {order:Extraction.Order} {S₀:Table run.family.book}
    (F₀:Spec.Final run.family order S₀) (L₀:Layout F₀) {B:Deck G}{h:ℕ} (v:Glyph B h)
    (r:ℝ) (z:ℂ)

def column : run.family.label v.size :=
  (WilsonReportingPrescribedOldGlyph.scale run F₀ L₀ h r*z) • (raw run v+lower run v (run.family.path.levels.clock.hatCoupling (L₀.level r)))

def entered (θ:ℝ) : run.family.label v.size :=
  (run.family.labels.level v.size).scaled θ (column run F₀ L₀ v r z)

theorem unscaled {θ:ℝ} (positive:0<θ):
    (run.family.labels.level v.size).scaled θ⁻¹ (entered run F₀ L₀ v r z θ)=column run F₀ L₀ v r z:=by
  simpa only [entered,inv_inv] using
    (run.family.labels.level v.size).scaled_inv (inv_ne_zero positive.ne') (column run F₀ L₀ v r z)

variable {N per:ℕ} (age:run.family.ref v.size≤L₀.level r)(future:L₀.level r≤N)
variable (o₀:Site (run.family.side (L₀.level r) per)) (χ:ℂ→L[ℝ]ℝ)

include age future in
theorem deposited {θ:ℝ} (positive:0<θ) (U:Config G (run.family.side (L₀.level r) per)) :
    WilsonCoherentMayerEntry.raw run (entered run F₀ L₀ v r z θ) o₀ θ χ U=
      χ ((((run.family.path.levels.clock.hatCoupling (L₀.level r))^v.grade:ℝ):ℂ)*WilsonReportingPrescribedOldGlyph.observed run F₀ L₀ v r z N per o₀ U):=by
  change χ ((run.family.localSection v.size).places
    ((run.family.labels.level v.size).scaled θ⁻¹ (entered run F₀ L₀ v r z θ)) o₀ U)=_
  rw [unscaled run F₀ L₀ v r z positive, WilsonReportingPrescribedOldGlyph.original run F₀ L₀ v r z N per age future o₀ U]
  congr 1
  let T:=run.family.localSection v.size
  let c:=WilsonReportingPrescribedOldGlyph.scale run F₀ L₀ h r*z
  let y:=lower run v (run.family.path.levels.clock.hatCoupling (L₀.level r))
  have added : T.places (raw run v+y) o₀ U=T.places (raw run v) o₀ U+T.places y o₀ U:=
    congrFun (T.eval_linear.map_add (raw run v) y) (expandAt o₀ U)
  have scaled : T.places (c • (raw run v+y)) o₀ U=c*T.places (raw run v+y) o₀ U:=
    congrFun (T.eval_linear.map_smul c (raw run v+y)) (expandAt o₀ U)
  exact scaled.trans (congrArg (c*·) added)

theorem costs {θ:ℝ} (positive:0<θ) :
    WilsonCoherentMayerEntry.wallet run (entered run F₀ L₀ v r z θ) θ χ=
      ‖χ‖*∑a,‖column run F₀ L₀ v r z a‖ *WilsonCoherentMayerEntry.unitPrice run v.size a:=by
  unfold WilsonCoherentMayerEntry.wallet
  rw [unscaled run F₀ L₀ v r z positive]

variable {c l:Side} {S:StepData c (run.family.side (L₀.level r) per)} {T:Tube G S} (A:Rep G (run.family.side (L₀.level r) per))
    {P:Teller G} {Q:ConnectedActivityE6.Target G P} {w s μ C:ℝ} {o:Target.Order G w}
    (H:Cash w s μ l Q o C T A) (key:ℕ)
    (covers:(run.family.localSection v.size).footprint o₀ ⊆ (A.activities.reg key).support)
    (blank:A.activities.E key=0)

include age future in
theorem observed (prior:Team A) (live:(WilsonCoherentMayerEntry.entered run A key o₀ (entered run F₀ L₀ v r z A.p.threshold) χ covers blank)∈prior.own) (positive:0<A.p.threshold)
    {forest:Forest S.ratio} (X:Coat T forest) (u:momentSpace X) :
    let U:=WilsonCoherentMayerOccurrences.field A X u
    (Laminate.partner prior H (((WilsonCoherentMayerEntry.entered run A key o₀ (entered run F₀ L₀ v r z A.p.threshold) χ covers blank)).turn.badge S)).joint X u =
      masked A.p.threshold (A.activities.reg key).support
        (fun V=>χ ((((run.family.path.levels.clock.hatCoupling (L₀.level r))^v.grade:ℝ):ℂ)*WilsonReportingPrescribedOldGlyph.observed run F₀ L₀ v r z N per o₀ V)) U *
        WilsonCoherentMayerOccurrences.anchor A o.a ((WilsonCoherentMayerEntry.entered run A key o₀ (entered run F₀ L₀ v r z A.p.threshold) χ covers blank)).turn X u:=by
  rw [WilsonCoherentMayerOccurrences.leaf (H:=H) prior (WilsonCoherentMayerEntry.entered run A key o₀ (entered run F₀ L₀ v r z A.p.threshold) χ covers blank) live X u]
  have eq:=funext (deposited run F₀ L₀ v r z age future o₀ χ positive)
  change masked _ _ (WilsonCoherentMayerEntry.raw run _ o₀ _ χ) _ * _ = _
  rw [eq]

end YM.Integration.WilsonCoherentMayerOldGlyph
