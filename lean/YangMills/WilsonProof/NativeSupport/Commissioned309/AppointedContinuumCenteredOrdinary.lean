import YangMills.WilsonProof.NativeSupport.Commissioned309.AppointedTwoFiledPayments
import YM.Integration.WilsonGraphCenteredRoundedSource

namespace YM.FVA2.GradedFar.AppointedTwoFiledPayments
noncomputable section
set_option maxHeartbeats 4000000
open Filter Function Real Set MeasureTheory PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window OPE Orbits Physical
open YM.Answer.ContinuumLimit YM.Integration
open scoped Topology BigOperators Classical ContDiff

section Paper
universe u
variable (g : YangMills.GaugeGroup) (hg : g.IsSimple) (dates : ℕ → ℕ) (strictDates : StrictMono dates)

theorem onNumerator {n : ℕ} (hn : 0<n) (d : Fin n → ℕ) (h q : ℕ) {K : Set (Points n)}
    (hK : IsCompact K) (hx : K ⊆ conf n) (L : ℝ)
    (numerator : ∀ p : ℕ, ∀ B : ℝ, 0 < B →
      Filing (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) d (fun _ : Fin 1 => h) K {RootG} (upper g.core 1 B) (WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) p) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ i : View (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last, ∀ x∈K, ∀ u : Inputs g.core d, Within L u →
      Ball (D*((WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) r)^(q+1)) (Physical.packet (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.P d h r i x u -
        Wave.cropped (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg).MS x u h q ((WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) r)) := by
  obtain ⟨frame,history⟩ := electedCosts.{u} g hg dates strictDates
  exact Physical.AppointedTwoRoundedRows.measuredFromTwoRows (WilsonGraphPaperPublication.perspective.{u} g hg).matching
    (AppointedPhysicalWindowAndPhase.electedClock.{u} g hg dates strictDates) history frame hK hx L hn d h q
    (fun p B hB => rounded (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg).matching (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) _ _ _ _ _ (WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) p (numerator p B hB))
    (fun p B hB => AppointedCenteredRounded.roundedAt.{u} g hg dates strictDates h p {RootG}
      isCompact_singleton (singleton_subset_iff.mpr ok_wall) one_pos hB)

end Paper
end
end YM.FVA2.GradedFar.AppointedTwoFiledPayments

