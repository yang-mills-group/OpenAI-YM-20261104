import YM.Integration.WilsonRegisteredSectorPrice
import YM.Integration.WilsonRegisteredSectorSeats

/-! On the originally paid nonbare family, all individually allocated source
fees precede the cutoff and the perturbative monetary and spatial tests.
The same cash controls the previous portfolio and the normalized named hats. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredSectorIntake
open Filter Function Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Extra.Multi
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirQuote QLocalRequestedSectorSale QLocalRequestedSectorCalendar
open PhysicalNext.Repeat.Opera PhysicalNext.Repeat.Daisy
open MergeProof LocalLTE
open scoped Topology BigOperators Classical


open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical


open WilsonInheritedRegisteredField RGLocalTaylor.Mayer PhysicalNext.Repeat.Daisy
open Push.AbsoluteSums ManuscriptQLocalMarkedHeightRun
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {Γ:Marker.Census V} (R:Run G)

variable {J:Request V} (A:NumericSchedule R.family J)
    (extra:Stage→ℕ→ℝ) (γ:ℝ)
    (paid:QLocalRequestedSectorCalendar.Paid J (acquisition G J) extra γ R.kit)

theorem original (simple:G.Simple):
    ∀ᶠ m in (atTop:Filter ℕ), ∀(d:LocalFormal.Datum R.family Γ),d.level=m →
      ∀(F:AnalyticInput J A d) {η:ℝ}(I:FullPreparedInputAt F η), Retained.NativeIntake I →
      let lev:=R.alloy.B.a
      let i:=lev.clock.J d.level
      let j:=lev.clock.J (d.level+1)
      let book:=paid.choose j i
      let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
      let Q:=ManuscriptQLocalVacuumFamily.source (QLocalInheritedPhysicalInlet.rep I) F.layers g 1
      let Y:=QLocalInheritedRegularSlots.carrier Q
      ∃H:Cash book.W (lev.clock.hatBeta d.level) book.μ (lev.clock.op d.level d.period).patch.L
        (target J (R.kit.target j i)) book.order book.c (ships R.alloy.B d.cutoff d.level d.period) Y,
        Cash.Renewed J.outputFieldOrder (toll J) 1 1 H ∧
        Crossed J γ R A d book H (I.inherited+ManuscriptQLocalVacuumRadius.bill F.vacuum.packets g 1) ∧
        WilsonRegisteredSectorPrice.Priced (expense J (R.kit.target j i)) H J Γ ((2*g)^(J.order+1)) ∧
        WilsonRegisteredHeightIntake.Bought R d Q ∧ WilsonRegisteredSectorSeats.Filed R d.below Q Γ:=by
  filter_upwards [WilsonRegisteredHeightIntake.original (Γ:=Γ) R A extra γ paid simple,
    eventually_ge_atTop (R.family.ref (max J.inputFieldOrder J.inputDistanceOrder))]
    with m ledger order d date F η I prior
  intro lev i j book g Q Y
  obtain ⟨H,renew,cross,high,both⟩:=ledger d date F I prior
  refine ⟨H,renew,cross,WilsonRegisteredSectorPrice.paid _ _ J Γ _ high,both,?_⟩
  have onset:R.family.ref (max J.inputFieldOrder J.inputDistanceOrder)≤d.level+1:=by omega
  exact WilsonRegisteredSectorSeats.original R d.below onset Q (A.input_norm d.level)

end YM.Integration.WilsonRegisteredSectorIntake
