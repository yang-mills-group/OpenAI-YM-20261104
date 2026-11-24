import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedTwoFiledPublicRows
import YangMills.WilsonProof.NativeSupport.Commissioned309.AppointedContinuumCenteredOrdinary

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedTwoFiledPublicRows
set_option maxHeartbeats 4000000
open Filter Function Real Set MeasureTheory PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window OPE Orbits Physical
open YM.Answer.ContinuumLimit YM.Integration
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {n m : ℕ} {A : Family G} {o : Extraction.Order} {P : Table A.book}

universe u
variable (g : YangMills.GaugeGroup) (hg : g.IsSimple) (dates : ℕ → ℕ) (strictDates : StrictMono dates)

theorem onNumerator {n : ℕ} (hn : 0<n) (d : Fin n → ℕ) (h q : ℕ) {K : Set (Points n)}
    (hK : IsCompact K) (hx : K ⊆ conf n) (L : ℝ)
    (numerator : ∀ p : ℕ, ∀ B : ℝ, 0 < B →
      AppointedTwoFiledPayments.Filing (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) d (fun _ : Fin 1 => h) K {RootG} (upper g.core 1 B) (WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) p)
    :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ i : View (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last, ∀ x∈K, ∀ u : Inputs g.core d, Within L u →
      Ball (D*((WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) r)^(q+1)) ((show Sec g.core h from (_root_.YM.Answer.ContinuumLimit.AppointedOrdinaryPacket.measurement hg (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)).wilsonOPE r h (fun j => ⟨d j, u j⟩) i.2 x) -
        Wave.cropped (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg).MS x u h q ((WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) r)) := by
  obtain ⟨D,hD,paid⟩ := AppointedTwoFiledPayments.onNumerator.{u} g hg dates strictDates hn d h q hK hx L numerator
  refine ⟨D,hD,?_⟩
  filter_upwards [paid] with r hr
  intro i x hx₀ u hu
  rw [readerValue.{u} g hg dates strictDates d u h r i x]
  exact hr i x hx₀ u hu

theorem onPublishedPick {n : ℕ} (hn : 0<n) (d : Fin n → ℕ) (h q : ℕ) {K : Set (Points n)}
    (hK : IsCompact K) (hx : K ⊆ conf n) (L : ℝ)
    (numerator : ∀ p : ℕ, ∀ B : ℝ, 0 < B →
      AppointedTwoFiledPayments.Filing (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) d (fun _ : Fin 1 => h) K {RootG} (upper g.core 1 B) (WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) p)
    :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ o : E4, ∀ x∈K, ∀ u : Inputs g.core d, Within L u →
      Ball (D*((WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) r)^(q+1)) ((show Sec g.core h from (_root_.YM.Answer.ContinuumLimit.AppointedOrdinaryPacket.measurement hg (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)).wilsonOPE r h (fun j => ⟨d j, u j⟩) o x) -
        Wave.cropped (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg).MS x u h q ((WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) r)) := by
  obtain ⟨D,hD,paid⟩ := onNumerator.{u} g hg dates strictDates hn d h q hK hx L numerator
  refine ⟨D,hD,?_⟩
  filter_upwards [paid] with r hr
  intro o x hx₀ u hu
  exact hr (none, o) x hx₀ u hu

end YM.FVA2.GradedFar.AppointedTwoFiledPublicRows
end


