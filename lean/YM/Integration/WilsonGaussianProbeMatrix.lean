import YM.Integration.WilsonGaussianRecoveredPanel
import YM.Integration.SignedWilsonProbeInverse
import YM.Integration.WilsonMatrixTicketPhysicalLensRows
import YM.Integration.WilsonReportingPrescribedOldSignedPanel

/-! Finite Wilson Gram matrices, moving quotient prices and independently reported columns
on the original funded running field. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonGaussianProbeMatrix

open Filter RG RG17 Marker Extraction Extraction.Order Spec Table Climb PhysMS OPE Trace.Pilot
open Next.UVStress Next.Rank PhysicalNext.Repeat.Legato SharpGram FiniteHorizonGram
open Push.FiniteDetection.Free SignedWilsonProbeInverse WilsonReportingPrescribedOldSignedPanel
open Source FVA2 FVA2.Register WilsonPositionHomogeneousFrame Pert.Position
open MS MS.Menus MS.Local.Physical RGComparison.Core16 OPE.Therm
open scoped Classical Topology
open Trace.Sundial Spin WilsonLimitConstruction Precision


structure Filed {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) (L : Layout F)
    {B : Deck G} (Q : MS.Land.Prescription B) : Prop where
  service : Services R.family f S
  gram : ∀ D : ℕ, ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ r in trail, ∀ᶠ a : ℕ × ℕ in f.fuse,
    Function.Bijective (regulated J D r a) ∧
    ∀ (z : E R.family.labels D) (u : ProbeIndex R.family D → ℂ),
      decode J D r a (regulated J D r a z) = z ∧
      regulated J D r a (decode J D r a u) = u ∧
      ‖decode J D r a u - z‖ ≤ K * ‖u - regulated J D r a z‖
  chart : ∀ (U : Ultrafilter (ℕ × ℕ)), (U : Filter (ℕ × ℕ)) ≤ f.fuse →
    ∃ B : Lenses.Mantle F (U : Filter (ℕ × ℕ)), ∀ d : ℕ, ∀ᶠ m in atTop,
      (∀ x : S.Field d, ∃ (y : R.family.label d) (w : ℕ × ℕ → R.family.label d),
        S.project d y = x ∧ Tendsto w (U : Filter (ℕ × ℕ)) (𝓝 y) ∧
        ∀ᶠ i in (U : Filter (ℕ × ℕ)), Next.UVStress.quota R.family d m i.1 i.2 (w i) ≤
          2 * R.family.path.levels.clock.hatBeta m ^ Lenses.price d * R.family.S.a m ^ d *
            ‖(Load.tent B m d).symm x‖) ∧
      ∀ (j : ℕ), j ≤ d → ∀ (u : S.Field d →ₗ[ℂ] ℂ)
        (l : Filter (ℕ × ℕ)), l.NeBot → l ≤ (U : Filter (ℕ × ℕ)) →
        ∀ (w : ℕ × ℕ → R.family.label d) (z : R.family.label d) (q : ℝ),
          Tendsto w l (𝓝 z) →
          (∀ᶠ i in l, Next.UVStress.quota R.family d m i.1 i.2 (w i) ≤ q) →
          ‖u (S.project d z)‖ * R.family.S.a m ^ (d-j) ≤
            min ((‖LinearMap.toContinuousLinearMap (𝕜 := ℂ) (u.comp (S.project d))‖ *
                  Price.outward R.family d m * R.family.S.a m ^ (d-j)) * q)
                ((2 * Lenses.bonus R.family d *
                  ‖LinearMap.toContinuousLinearMap (𝕜 := ℂ) (u.comp (Load.tent B m d).toLinearMap)‖ /
                  R.family.S.a m ^ j) * q)
  annihilator : ∀ (U : Ultrafilter (ℕ × ℕ)) (_ : (U : Filter (ℕ × ℕ)) ≤ f.fuse)
    (B : Lenses.Mantle F (U : Filter (ℕ × ℕ)))
    (_ : OPE.Outward R.family f S F.sector.derivatives)
    {d j : ℕ} (_ : j ≤ d) (u : S.Field d →ₗ[ℂ] ℂ)
    (_ : ∀ c : ℕ, c < j → ∀ hc : c ≤ d, ∀ z : S.Field c,
      u (F.sector.derivatives.rise hc z) = 0),
    ∃ L : ℕ, ∀ᶠ m in atTop,
      ‖LinearMap.toContinuousLinearMap (𝕜 := ℂ) (u.comp (Load.tent B m d).toLinearMap)‖ /
        R.family.S.a m ^ j ≤ 2 * R.family.path.levels.clock.hatBeta m ^ (L + Lenses.price d)
  columns : ∀ (a b:ℝ→R.family.label 4) (χ:ℂ→L[ℝ]ℝ) (φ:Test 2) {r:ℝ} (hr:0<r)
    (u v:MS.Rake.Label B) (hu:4≤u.h) (hv:4≤v.h) (μ:ℝ) (k l:ℕ) (N per:ℕ),
    let x := atRef L 4 r (N,per) (a r)
    let y := atRef L 4 r (N,per) (b r)
    let ψ := dilate hr φ
    WilsonMatrixOriginalFiledPanel.Value F L a b χ φ hr (N,per)-
        separated R (N:=N) (per:=per) χ ψ (issued R (N:=N) (per:=per) Q u μ k) (issued R (N:=N) (per:=per) Q v μ l)=
      separated R (N:=N) (per:=per) χ ψ (residual R (N:=N) (per:=per) Q u hu μ k x) (R.family.O N per y)+
        separated R (N:=N) (per:=per) χ ψ (issued R (N:=N) (per:=per) Q u μ k) (residual R (N:=N) (per:=per) Q v hv μ l y)

theorem filed {G : Gauge} {R : Run G} (simple : G.Simple) {T : Campaign R}
    (W : Campaign.Pillars R T) {ρ : ℝ} (original : WilsonLimitConstruction.FundedOriginalProperties.{u} simple ρ W)
    {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
    (J : ℝ → tower S) (leading : Leading F J) (service : Services R.family f S)
    (L : Layout F) {B : Deck G} (Q : MS.Land.Prescription B) : Filed F J L Q := by
  refine ⟨service, ?_, ?_, ?_, ?_⟩
  · exact fun d => SignedWilsonProbeInverse.inverse F J leading service d
  · exact fun U hu => WilsonMatrixTicketPhysicalLensRows.purchased R simple W original F service U hu
  · intro U hu bank ticket d j hj u kill
    exact WilsonMatrixTicketPhysicalLensRows.necessary F service U hu bank ticket hj u kill
  · intro a b χ φ r hr u v hu hv μ k l N per
    exact WilsonReportingPrescribedOldSignedPanel.original R Q F L a b χ φ hr u v hu hv μ k l N per

def Measured {G : Gauge} (R : Run G) (simple : G.Simple) (N : WilsonPrescription G) (Q : MS.Land.Prescription (Press.portDeck G)) : Prop :=
  ∀ (B : ℕ), 17≤B → ∀ v : Extraction.Order,
    ∃(w:Extraction.Order)(S:Table R.family.book)(F:Final R.family (v.refine w) S)
      (H:(Bel R.family.book).Hierarchy)(J:ℝ→tower S)(A:ℝ→Spin.change S 4)(δ:ℝ→ℝ)(L:Layout F),
      Leading F J ∧ (∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d) ∧
      (∀ᶠr in trail,J r 4=A r) ∧ TendC F A δ ∧ Coupling G (glo A) ∧
      L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B ∧ L.lens≤(v.refine w).fuse ∧
      Filed F J L Q ∧ WilsonGaussianRecoveredPanel.Observed (H:=H) (U:=L.lens) F J N L B δ (glo A)

open WilsonMatrixOriginalFundedPanel

theorem measured {G : Gauge} {R : Run G} {T : Campaign R} (W : Campaign.Pillars R T)
    (simple : G.Simple) {ρ : ℝ} (funded : WilsonLimitConstruction.FundedOriginalProperties.{u} simple ρ W)
    (subsidy : WilsonReportColumnSubsidy.Eligible R.kit) (pace : WilsonWindowReportingPace.Slow R.kit)
    (N : WilsonPrescription G) (Q : MS.Land.Prescription (Press.portDeck G)) : Measured R simple N Q := by
  intro B large v
  have record := funded
  obtain ⟨_,_,_,_,_,_,_,_,_,selected,_⟩:=record
  obtain ⟨w,S,F,_,_,_,_,_,fac,_,H,arch,l,bliss,_,A,J,_,_,δ,_,same,_,comp,lead,obey⟩:=selected v
  obtain ⟨u₀,bank,L,pegs,level,lens,_⟩:=WilsonMatrixOriginalFundedPanel.measured_layout simple W funded pace (B:=B) (by omega) F fac
  letI : L.lens.NeBot := L.notbot
  have prior := WilsonMatrixOriginalEarlierPanel.original (F:=F) (J:=J) (Z:=N) (L:=L) (lead:=lead)
    (paid:=obey) (simple:=simple) (funded:=funded) (subsidy:=subsidy) (pace:=pace) (hB:=show 0 < B by omega) (level:=level)
    (U:=L.lens) (chosen:=le_rfl) (bank:=bank) (E:=fac.toServices) (pegs:=pegs)
    same comp.alignment.spun comp.leading comp.coupling
  have date := WilsonMatrixOriginalReportingMargin.captured F J N L lead obey simple W funded subsidy
    pace large level le_rfl comp.coupling prior
  exact ⟨w,S,F,H,J,A,δ,L,lead,obey,same,comp.leading,comp.coupling,level,lens,
    filed simple W funded F J lead fac.toServices L Q,
    WilsonGaussianRecoveredPanel.receive F J N L comp.coupling date⟩

end YM.Integration.WilsonGaussianProbeMatrix

namespace YM.Integration.WilsonGaussianProbeMatrix
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
        Measured R simple N Q ∧ WilsonGaussianRecoveredPanel.Measured R simple N ∧ WilsonGaussianEarlierPanel.Measured R simple N ∧ WilsonWindowReportingPace.Slow R.kit ∧ WilsonReportColumnSubsidy.Eligible R.kit ∧
        PhysicalNext.Repeat.Legato.Citizen R.family R.w
          (PhysicalNext.Repeat.Legato.Bandage.mutt R.family.path.levels R.Q) R.doors ∧
        WilsonRootedPhysicalSpringReportedMS.Settled.{u} simple ε J extra γ M S R T W affine Q ∧
        WilsonRootedPhysicalSpringStoredMS.Ready simple M R affine Q orders ∧
        WilsonRootedPhysicalSpringUnitMS.Ready simple M R affine Q table ∧
        WilsonGaussianDeterminantQuarticMS.Common simple R J χ extra γ M Q affine orders booking ∧
        WilsonRootedPhysicalSpringAccurateMS.Ready simple M R affine Q table ∧
        WilsonGaussianSourceMS.Common simple R J χ extra γ M Q affine table booking := by
  obtain ⟨N,M,S,clock,matched,R,T,W,affine,Q,orders,table,booking,recovered,earlier,slow,subsidy,citizen,settled,remaining⟩ :=
    WilsonGaussianRecoveredPanel.purchased.{u} simple hε J χ extra γ hγ calendar dial
  exact ⟨N,M,S,clock,matched,R,T,W,affine,Q,orders,table,booking,
    measured W simple settled.1.original subsidy slow N Q,recovered,earlier,slow,subsidy,citizen,settled,remaining⟩

end YM.Integration.WilsonGaussianProbeMatrix
end
