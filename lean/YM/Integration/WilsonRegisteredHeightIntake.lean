import YM.Integration.WilsonRegisteredIntakePair
import YM.Integration.ManuscriptQLocalMarkedHeightRun

/-! The two previously measured Wilson marks are contracted on the exact
nonbare family and cash issued for an original prepared physical intake. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredHeightIntake
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

def Bought (d:LocalFormal.Datum R.family Γ) (Q:Rep G (R.family.side (d.level+1) d.period)):Prop:=
  ∀(d₁ d₂:ℕ),R.family.ref d₁≤d.level+1 → R.family.ref d₂≤d.level+1 →
  ∀(v₁:R.family.label d₁)(v₂:R.family.label d₂)(o₁ o₂:Site (R.family.side (d.level+1) d.period)),
    let P:=R.family.path.rep d.cutoff d.period (d.level+1)
    let Z₁:=packet R.makes d.below v₁ o₁
    let Z₂:=packet R.makes d.below v₂ o₂
    let L₁:=R.family.labels.level d₁
    let L₂:=R.family.labels.level d₂
    let c:=(R.family.path.levels.params (d.level+1)).columns
    ∃e₁ e₂:ℕ→ℝ, SumBudget (fun i=>P.p.mass (Z₁.support i) (e₁ i)) (c*L₁.coeffSize (L₁.core Z₁.x)) ∧
      SumBudget (fun j=>P.p.mass (Z₂.support j) (e₂ j)) (c*L₂.coeffSize (L₂.core Z₂.x)) ∧
      (Q.p.supportExponent≤P.p.supportExponent →
        SumBudget (fun i=>Q.p.mass (Z₁.support i) (e₁ i)) (c*L₁.coeffSize (L₁.core Z₁.x)) ∧
        SumBudget (fun j=>Q.p.mass (Z₂.support j) (e₂ j)) (c*L₂.coeffSize (L₂.core Z₂.x))) ∧
      ∀(i j:ℕ)(χ ψ:ℂ→L[ℝ]ℝ), (∀z,|χ z|≤‖z‖) → (∀z,|ψ z|≤‖z‖) →
      ∀old:Team (QLocalInheritedRegularSlots.carrier Q),
        ∃W:Team (QLocalInheritedRegularSlots.carrier Q),
          W.weight=(old.weight*e₁ i)*e₂ j ∧ old.own⊆W.own ∧
          ∀U,(∏b∈W.own,b.ingredient U)=
            χ (Z₁.maskedTerm P i U)*ψ (Z₂.maskedTerm P j U)*(∏b∈old.own,b.ingredient U)

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
        High (expense J (R.kit.target j i)) H J Γ ((2*g)^(J.order+1)) ∧ Bought R d Q:=by
  filter_upwards [ManuscriptQLocalMarkedHeightRun.issued (Γ:=Γ) R A extra γ paid simple,
    eventually_ge_atTop (R.family.ref (max J.inputFieldOrder J.inputDistanceOrder))]
    with m ledger order d date F η I prior
  intro lev i j book g Q Y
  obtain ⟨H,renew,win,high,_,_⟩:=ledger d date F I prior
  refine ⟨H,renew,win,high,?_⟩
  intro d₁ d₂ ref₁ ref₂ v₁ v₂ o₁ o₂
  have onset:R.family.ref (max J.inputFieldOrder J.inputDistanceOrder)≤d.level+1:=by omega
  have record:LocalComparison.NormAt R.family (d.level+1) Q.p
    J.inputFieldOrder J.inputDistanceOrder J.inputSupport:=A.input_norm d.level
  simpa only [record.reserve] using
    (WilsonRegisteredIntakePair.paired R d.below ref₁ ref₂ onset Q record v₁ v₂ o₁ o₂)

end YM.Integration.WilsonRegisteredHeightIntake
