import YM.Integration.WilsonPositionSeparatedProfileMayerLeadingGaussian

/-! The original minimal signed incidence at the zero exponential decoration
is numerically compared with the independently filed finite Wick, through
any prescribed thermal order, before every site, forest and regulator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileMayerLeadingMarket
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Legato
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio} {R:Rep G f}
    {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ C:ℝ} {o:Target.Order G W}
    {H:Cash W s μ L Q o C T R} {j n l k M:ℕ} {χ:Chi}

open WilsonPositionSeparatedProfileMayerMasks WilsonPositionSeparatedProfileMayerGateReturn
open WilsonCoherentMayerSubmission WilsonCoherentMayerOccurrences WilsonCoherentMayerHearing
open WilsonPositionSeparatedProfileMayerGateSafety LocalTaylorR2.Exponent
open Precision Coat Source Matrix Dict06 AnalyticBridge.LocalGaussianLaws ProbabilityTheory
open WilsonPositionSeparatedProfileMayerLeadingGaussian
open private averaged from YM.Integration.WilsonPositionSeparatedProfileMayerLeadingWindow

variable {I:Type} [Fintype I]
theorem original (run:Run G) (d:I→ℕ) (P:Teller G) (L:Side) (D:Patch) (branch:D.Branches P.bind G) {W:ℝ} (o:Target.Order G W) (t:ℕ) (power:ℝ):
    ∃Ctab:ℝ,0≤Ctab ∧ ∃E:ℝ→ℝ,Rate G L power E ∧ ∀ᶠ s:ℝ in atTop,∀ {c f:Side} {S:StepData c f} (T:Tube G S) {R:Rep G f} {Q:ConnectedActivityE6.Target G P} {μ C:ℝ}
    (H:Cash W s μ L Q o C T R),S.patch=D→S.patch.L=L→0<R.beta→|Coat.gStep R.beta|≤1→0≤Pressure.temp s→Stamp T→
    ∀entry:Submitted run R I,d=entry.grade→(∀i z,|entry.phase i z|≤‖z‖)→∀old:Team R,old.own=∅→∀fresh:∀m∈old.own,∀i,m.turn≠(row entry i).turn,
    ∀loc:H.ThinP,loc.val=(together entry old fresh).signs S→∀ {j n k l M:ℕ} {χ:Chi} {r q a Y D' A b B C' ρ e uJ vJ θ K:ℝ},
    (N:Captain H j C' D' Y B A b r a q n χ)→Awning H N.conduit A b ρ e uJ vJ k l→Q.goal L s≤K→Mayer.Approved K θ j M→authorized H loc.val→Mayer.Start loc.val→
    let cash:=WilsonCoherentReportingPivot.mass run entry.grade R.p.threshold entry.label
    let column:=Laminate.column (together entry old fresh) loc.val H (χ:=χ) M (0:Orders M) (1:Config G c)
    |column-forecast entry T s o χ t|≤(sites entry T s).card*E s*bank entry old+
      cash*(Ctab*(Coat.gStep R.beta)^(t+1))+cash*WilsonPositionSeparatedProfileMayerStencilPrice.budget run d t*|WilsonOriginalSignedSamplerMoment.fee T L P o t s|:=by
  obtain ⟨Ctab,hc,paid⟩:=WilsonPositionSeparatedProfileMayerLeadingTaylor.original run d P L D branch t
  obtain ⟨E,rate,rates⟩:=WilsonPositionSeparatedProfileMayerGateSafety.tariff P L o power
  refine ⟨Ctab,hc,E,rate,?_⟩;filter_upwards [paid,rates] with s purchase alarm
  intro c f S T R Q μ C H same patch hot scale temp stamped entry given cap old vacant fresh loc minimal j n k l M χ r q a Y D' A b B C' ρ e uJ vJ θ K N law room allow inside cohort
  subst d
  let g:=Coat.gStep R.beta
  let cash:=WilsonCoherentReportingPivot.mass run entry.grade R.p.threshold entry.label
  let upper:=cash*(Ctab*g^(t+1))
  let lower:=cash*WilsonPositionSeparatedProfileMayerStencilPrice.budget run entry.grade t*|WilsonOriginalSignedSamplerMoment.fee T L P o t s|
  let column:=Laminate.column (together entry old fresh) loc.val H (χ:=χ) M (0:Orders M) (1:Config G c)
  let read:=WilsonPositionSeparatedProfileMayerLeadingWindow.read entry old T s o χ
  have gate:|column-read|≤_:= (WilsonPositionSeparatedProfileMayerLeadingWindow.measured entry old fresh loc minimal N law room allow inside cohort temp stamped (E s) alarm.1 (alarm.2 H)).1
  let X (i:Greenbelt.Reserve S) (tag:S.Choices):Coat T (Greenbelt.allot i):=chamber T s o.K χ 1 ∅ i tag
  have compare:|read-forecast entry T s o χ t|≤upper+lower:=by
    apply (averaged (A:=Greenbelt.Reserve S) _ _);intro i
    apply (averaged (A:=S.Choices) _ _);intro tag
    have hm:(X i tag).manifest:=by
      change (roster (LocalLTE.Fan.arm (S:=S) ∅)).flags=RG.flags (Pressure.temp s) (1:Config G c)
      rw [LocalLTE.Fan.Field.rosterD];exact (Greenbelt.prism T s χ o.K (1:Config G c) (Greenbelt.allot i)).bowed temp
    have clear:Assembly.Clear S (X i tag).x (X i tag).seeds (Greenbelt.allot i):=by
      change Assembly.Clear S s (roster (LocalLTE.Fan.arm (S:=S) ∅)) _
      rw [LocalLTE.Fan.Field.rosterD];exact Assembly.bare_is_Clear S s _
    have earlier:=purchase T H (X i tag) rfl same patch hm H.laws.data.funds.funds (WilsonOriginalSignedShutterSquare.blank χ s o.K ∅ i tag) rfl clear hot entry rfl cap old
    simp only [vacant,prod_empty,one_mul] at earlier
    have later:=WilsonPositionSeparatedProfileMayerLeadingGaussian.measured entry H temp cap scale old vacant χ t i tag
    exact (abs_sub_le _ _ _).trans (add_le_add earlier later)
  change |column-forecast entry T s o χ t|≤_+upper+lower
  rw [add_assoc];exact (abs_sub_le column read _).trans (add_le_add gate compare)

end YM.Integration.WilsonPositionSeparatedProfileMayerLeadingMarket
