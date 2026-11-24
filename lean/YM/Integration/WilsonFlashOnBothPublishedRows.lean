import YM.Integration.WilsonFlashRoundedOnTheElectedWindow
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedRoundedReader
import YM.Integration.WilsonGraphAppointedOrdinaryTestedExpansion
import YM.Integration.WilsonGraphAppointedEmptyPublicShape

set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.GradedFar.AppointedFlashNumerator
open Filter Set XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Scale Dframe OPE Orbits Continuation Continuation.Window Physical
open YM.Answer.ContinuumLimit YM.Integration
open scoped Topology BigOperators Classical
universe u

variable (g : YangMills.GaugeGroup) (hg : g.IsSimple) (dates : ℕ → ℕ) (strictDates : StrictMono dates)
private abbrev issuedDatum := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev selectedVision := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)
private abbrev electedPerspective := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev filedFrame := Elected.Hframe (issuedDatum g hg) (selectedVision.{u} g hg dates strictDates).pupil.last (selectedVision.{u} g hg dates strictDates).pupil.J

theorem numerator {n : ℕ} (d : Fin n → ℕ) (h : ℕ) {K : Set (Points n)}
    (hK : IsCompact K) (hx : K ⊆ conf n) (p : ℕ) (B : ℝ) (hB : 0 < B) :
    RoundedAt (issuedDatum g hg) (Physical.Y0 (selectedVision.{u} g hg dates strictDates).pupil.last (filedFrame.{u} g hg dates strictDates) d (fun _ : Fin 1 => h))
      (upper g.core 1 B) K {RootG} ((selectedVision.{u} g hg dates strictDates).T (issuedDatum g hg)) p := by
  let cap := max (Finset.univ.sup d) h
  have hd (i : Fin n) : d i ≤ cap := (Finset.le_sup (f := d) (Finset.mem_univ i)).trans (le_max_left ..)
  exact onWindow.{u} g hg dates strictDates hd (fun _ => le_max_right ..) hK hx
    isCompact_singleton (singleton_subset_iff.mpr ok_wall) p B hB

theorem measured {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ) (h q : ℕ) {K : Set (Points n)}
    (hK : IsCompact K) (hx : K ⊆ conf n) (L : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ i : View (selectedVision.{u} g hg dates strictDates).pupil.last, ∀ x ∈ K,
      ∀ u : Inputs g.core d, Within L u →
      Ball (D*((selectedVision.{u} g hg dates strictDates).T (issuedDatum g hg) r)^(q+1))
        (Physical.packet (selectedVision.{u} g hg dates strictDates).pupil.last (filedFrame.{u} g hg dates strictDates) (selectedVision.{u} g hg dates strictDates).pupil.P d h r i x u - Wave.cropped (issuedDatum g hg) (electedPerspective.{u} g hg).MS x u h q ((selectedVision.{u} g hg dates strictDates).T (issuedDatum g hg) r)) := by
  obtain ⟨frame, history⟩ := AppointedTwoFiledPayments.electedCosts.{u} g hg dates strictDates
  exact Physical.AppointedTwoRoundedRows.measuredFromTwoRows (electedPerspective.{u} g hg).matching
    (AppointedPhysicalWindowAndPhase.electedClock.{u} g hg dates strictDates) history frame hK hx L hn d h q
    (numerator.{u} g hg dates strictDates d h hK hx)
    (fun p B hB => AppointedCenteredRounded.roundedAt.{u} g hg dates strictDates h p {RootG}
      isCompact_singleton (singleton_subset_iff.mpr ok_wall) one_pos hB)

theorem receives {n : ℕ} (hn : 0 < n) (h : ℕ) :
    _root_.YM.Integration.GradedFar.AppointedPublicOrdinaryJets.Receives.{u} g hg dates strictDates n h := by
  intro hin
  apply AppointedRoundedReader.regained.{u} g hg dates strictDates hn hin h
  intro e he K hK hx p hp B hB
  exact numerator.{u} g hg dates strictDates e h hK hx p B hB

theorem allJets (n h : ℕ) :
    _root_.YM.Integration.GradedFar.AppointedOrdinaryPurchases.AtOutput.{u} g hg dates strictDates n h := by
  intro q j d K hK hx
  cases n with
  | zero => exact AppointedEmptyPublicShape.empty.{u} g hg dates strictDates h q j d K
  | succ n =>
    exact _root_.YM.Integration.GradedFar.AppointedPublicOrdinaryJets.onReader.{u}
      g hg dates strictDates q j d K hK hx (receives.{u} g hg dates strictDates (Nat.succ_pos n) h)

end YM.FVA2.GradedFar.AppointedFlashNumerator
end
