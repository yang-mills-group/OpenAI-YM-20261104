import YM.Integration.WilsonGaussianOrientedPanel
import YM.Integration.WilsonMatrixOriginalFundedEarlierPanel
import YM.Integration.WilsonMatrixOriginalLowerWard

/-! The Ward ratio of the actual earlier Wilson covariance on the run financing the original Gaussian and independent MS prescription. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonGaussianEarlierPanel
open Filter Function Set MeasureTheory Lattice Wilson RG RG17 Source Marker Extraction Extraction.Order
open Table Spec Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm
open Next.UVStress Next.Rank.Price PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register
open WilsonLimitConstruction Trace.Sundial Next.Rank OPE.Orbits RG12 SharpGram
open WilsonMatrixOriginalFundedPanel WilsonMatrixOriginalEarlierPanel
open scoped Classical Topology BigOperators
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionSpectatorPrices WilsonInvariantActionPairCovariance
open WilsonInvariantActionCalibratedColumn WilsonInvariantActionPosition WilsonInvariantActionCapturedProfile

/-- A signed earlier covariance and its Ward ratio use the same records and moving labels. -/
def Observed {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) (Z : WilsonPrescription G)
    {H : (Bel R.family.book).Hierarchy} (L : Layout F) {U : Filter (ℕ × ℕ)} (δ g : ℝ → ℝ) : Prop :=
  ∃ (D:Profiles R 4) (j:D.probes.index) (v₀:(standard R.family.labels).Ref 4)
    (hs:D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 v₀)
    (e:ℕ) (deposit:ℝ→RG17.Free R.family 4→R.family.label 4) (χ:ℂ→L[ℝ]ℝ) (σ:ℝ),
    Row (H:=H) (U:=U) F J Z L δ g D j v₀ hs e deposit χ σ ∧
    let φ:=WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
    let v:=(Bel R.family.book).project 4 v₀
    let a:=fun r=>deposit r (stepField R.family)
    let b:=fun r=>deposit r (freeInput F J Z 4 r v)
    ∀q:ℕ,∀ε>0,∀ᶠr in trail, let k:=berth R (2*1+q+1+25) (L.level r)
      ∀hr:0<r,∀ᶠz:ℕ×ℕ in U,∃live:k<z.1,
      let marks:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z (a r)) (fun _=>atRef L 4 r z (b r))
      let low:=χ (earlier R (per:=z.2) live.le marks (dilate hr φ))
      let stress:=χ (tested (TraceExtension.center F) (homogeneous F J Z r 4 v) r φ)
      low ≠ 0 ∧ |(r^4/(4*δ r))*stress/low - 1| ≤ ε*(g r)^q

theorem receive {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) (Z : WilsonPrescription G)
    {H : (Bel R.family.book).Hierarchy} (L : Layout F) {U : Filter (ℕ × ℕ)}
    {δ g : ℝ → ℝ} (fee : Coupling G g) (seen : Captured (H:=H) (U:=U) F J Z L δ g) :
    Observed (H:=H) (U:=U) F J Z L δ g := by
  obtain ⟨D,j,w,sites,e,deposit,χ,σ,record⟩ := seen
  exact ⟨D,j,w,sites,e,deposit,χ,σ,record,
    WilsonMatrixOriginalLowerWard.at_earlier F J Z L fee D j w sites e deposit χ σ record⟩

def Measured {G : Gauge} (R : Run G) (simple : G.Simple) (Z : WilsonPrescription G) : Prop :=
  ∀ (B : ℕ), 0<B → ∀ v : Extraction.Order,
    ∃ (w : Extraction.Order) (S : Table R.family.book) (F : Final R.family (v.refine w) S)
      (H : (Bel R.family.book).Hierarchy) (arch : Trace.Terrace.Arch R.family)
      (l : Ultrafilter (ℕ × ℕ)) (J : ℝ → tower S) (A : ℝ → Spin.change S 4) (δ : ℝ → ℝ)
      (u₀ : Ultrafilter UVIndex) (bank : Mantle F (u₀ : Filter UVIndex)) (L : Layout F),
      Bliss F l arch H ∧ Leading F J ∧ (∀ d : ℕ, ∀ᶠ r in trail, Frame.obedient F H (J r) d) ∧
      (∀ᶠ r in trail, J r 4 = A r) ∧ (∀ᶠ r in trail, AlignV F.room.kernel F.sector H (A r)) ∧
      TendC F A δ ∧ Coupling G (glo A) ∧ Pegs bank L ∧
      L.level = WilsonMeasuredWindow.stop R.family.path.levels simple B ∧ L.lens ≤ (v.refine w).fuse ∧
      Observed (H:=H) (U:=L.lens) F J Z L δ (glo A)

theorem measured {G : Gauge} {R : Run G} {T : Campaign R} (W : Campaign.Pillars R T)
    (simple : G.Simple) {ρ : ℝ} (funded : FundedOriginalProperties.{u} simple ρ W)
    (subsidy : WilsonReportColumnSubsidy.Eligible R.kit) (pace : WilsonWindowReportingPace.Slow R.kit)
    (Z : WilsonPrescription G) : Measured R simple Z := by
  intro B hB v
  obtain ⟨w,S,F,H,arch,l,J,A,δ,u₀,bank,L,bliss,lead,obey,same,align,cal,fee,pegs,level,lens,seen⟩ :=
    WilsonMatrixOriginalFundedEarlierPanel.on_run simple W funded subsidy pace Z hB v
  exact ⟨w,S,F,H,arch,l,J,A,δ,u₀,bank,L,bliss,lead,obey,same,align,cal,fee,pegs,level,lens,
    receive F J Z L fee seen⟩

end YM.Integration.WilsonGaussianEarlierPanel

namespace YM.Integration.WilsonGaussianEarlierPanel
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

open RGLocalTaylor RGLocalTaylor.Laminate

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Marker.Census V}

open FVA2 FVA2.CityHistory FVA2.Register FVAAlt2 FormalOPE.RG10.BlockGauge
open MS MS.Rake MS.Land MS.Tide MS.Orbit MS.Dial MS.Fleet MS.Local.Physical
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open ManuscriptQLocalCofinalAffineFields (schedule)
open RG RG.Supply Precision Org Push.PriceCompiler
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonLimitConstruction.FundedCompanySelection


theorem purchased {G : Gauge} {V : Type} [Fintype V] [DecidableEq V]
    (simple : G.Simple) {ε : ℝ} (hε : 0 < ε) (J : Request V) (χ : Chi)
    (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ) (calendar : XSpace.Run) (dial : Bool) :
    ∃ (N : WilsonPrescription G) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
      (S : Prescription (Press.portDeck G)), N.run=calendar ∧ Main.Match N simple M S dial ∧
      ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
        (affine : ManuscriptQLocalCofinalAffineFields.Paid R) (Q : Prescription (Press.portDeck G))
        (orders : ManuscriptQLocalScalarDirections.PaidOrders schedule schedule R.kit)
        (table : WilsonScalarSourceTableForecast.Paid schedule schedule R.kit)
        (booking : QLocalRequestedSectorCalendar.Paid J
          (WilsonGaussianDeterminantTender.joined G J χ (WilsonCoherentMayerCovarianceCalendar.decal G))
          extra γ R.kit),
        Measured R simple N ∧ WilsonWindowReportingPace.Slow R.kit ∧ WilsonReportColumnSubsidy.Eligible R.kit ∧
        PhysicalNext.Repeat.Legato.Citizen R.family R.w
          (PhysicalNext.Repeat.Legato.Bandage.mutt R.family.path.levels R.Q) R.doors ∧
        WilsonRootedPhysicalSpringReportedMS.Settled.{u} simple ε J extra γ M S R T W affine Q ∧
        WilsonRootedPhysicalSpringStoredMS.Ready simple M R affine Q orders ∧
        WilsonRootedPhysicalSpringUnitMS.Ready simple M R affine Q table ∧
        WilsonGaussianDeterminantQuarticMS.Common simple R J χ extra γ M Q affine orders booking ∧
        WilsonRootedPhysicalSpringAccurateMS.Ready simple M R affine Q table ∧
        WilsonGaussianSourceMS.Common simple R J χ extra γ M Q affine table booking := by
  obtain ⟨N,M,S,clock,matched,R,T,W,affine,Q,orders,table,booking,_,slow,subsidy,citizen,settled,remaining⟩ :=
    WilsonGaussianOrientedPanel.purchased.{u} simple hε J χ extra γ hγ calendar dial
  exact ⟨N,M,S,clock,matched,R,T,W,affine,Q,orders,table,booking,
    measured W simple settled.1.original subsidy slow N,slow,subsidy,citizen,settled,remaining⟩

end YM.Integration.WilsonGaussianEarlierPanel
end
